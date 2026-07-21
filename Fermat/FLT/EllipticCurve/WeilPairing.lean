/-
WeilPairing.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyCurve.torsion_det` (the determinant of the mod-`p`
representation is the mod-`p` cyclotomic character):

* `WeilPairing.exists_weilPairing` (sorry node): **the Weil pairing** — on
  the `p`-torsion of an elliptic curve over `ℚ` there is an alternating,
  nondegenerate, `ZMod p`-bilinear, Galois-equivariant pairing, the Galois
  group acting on the target through (the mod-`p` reduction of) the
  cyclotomic character. This is the arithmetic content: `E[p] ∧ E[p] ≅ μ_p`.

* `WeilPairing.pairing_map_eq_det_smul` / `WeilPairing.det_eq_of_conj`
  (PROVEN): the linear algebra — on a 2-dimensional space an alternating
  bilinear form transforms under any endomorphism by the determinant, so an
  endomorphism scaling the pairing by `c` has determinant `c`.

Given these, `FreyCurve.torsion_det` follows (`FreyConditions.lean`): the
Galois action scales the Weil pairing by the cyclotomic character, so its
determinant IS the cyclotomic character.
-/
module

public import Fermat.FLT.EllipticCurve.Torsion
public import Fermat.FLT.GaloisRepresentation.Chebotarev
public import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

@[expose] public section

namespace WeilPairing

universe u

section DetOfPairing

variable {F : Type*} [Field F] {V : Type u} [AddCommGroup V] [Module F V]

set_option backward.isDefEq.respectTransparency false in
/-- On a 2-dimensional space, an alternating bilinear form transforms
under any endomorphism by the determinant:
`e (f x) (f y) = det f * e x y`. -/
lemma pairing_map_eq_det_smul (hrank : Module.rank F V = 2)
    (e : V →ₗ[F] V →ₗ[F] F) (halt : ∀ v, e v v = 0)
    (f : V →ₗ[F] V) (x y : V) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite F V :=
    Module.finite_of_rank_eq_nat (by exact_mod_cast hrank)
  have hfr : Module.finrank F V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hfr
  -- skew-symmetry from the alternating property
  have hskew : ∀ v w : V, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add,
      add_zero] at h
    linear_combination h
  -- the matrix of `f` in the basis `b`
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  -- both sides are bilinear; compare on basis pairs
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ f f = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : V →ₗ[F] V →ₗ[F] F => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- On a 2-dimensional space, an endomorphism that scales a nonzero
alternating bilinear form by `c` has determinant `c`. -/
lemma det_eq_of_conj (hrank : Module.rank F V = 2)
    (e : V →ₗ[F] V →ₗ[F] F) (halt : ∀ v, e v v = 0)
    (hnd : ∃ x y, e x y ≠ 0)
    {f : V →ₗ[F] V} {c : F} (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h1 := pairing_map_eq_det_smul hrank e halt f x y
  exact mul_right_cancel₀ hxy (h1.symm.trans (hc x y))

end DetOfPairing

open WeierstrassCurve

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ` (mirrors the local
instance of `HardlyRamified/Frey.lean`). -/
noncomputable local instance instAlgebraPadicIntZModWeilPairing
    (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- The `q`-power Frobenius of an algebraic closure of `𝔽_q`, as an
algebra homomorphism over `ZMod q` (it fixes the prime field by
Fermat's little theorem). -/
noncomputable def frobAlgHom (q : ℕ) [Fact q.Prime] :
    AlgebraicClosure (ZMod q) →ₐ[ZMod q] AlgebraicClosure (ZMod q) :=
  { frobenius (AlgebraicClosure (ZMod q)) q with
    commutes' := fun c => by
      show frobenius (AlgebraicClosure (ZMod q)) q
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) c) = _
      rw [frobenius_def, ← map_pow, ZMod.pow_card] }

/-- A classical decidable-equality instance on the algebraic closure of
`𝔽_q` (needed for the group law on points). -/
noncomputable instance instDecEqAlgClosureZMod (q : ℕ) [Fact q.Prime] :
    DecidableEq (AlgebraicClosure (ZMod q)) := Classical.typeDecidableEq _

/-- The endomorphism of the `p`-torsion of (the base change to `𝔽̄_q`
of) an elliptic curve over `𝔽_q` induced by the `q`-power Frobenius,
as a `ZMod p`-linear map. -/
noncomputable def frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) (p : ℕ) :
    Module.End (ZMod p)
      ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) :=
  AddMonoidHom.toZModLinearMap p
    (TorsionCounting.endRestrict
      (WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
        (frobAlgHom q)) p)

set_option maxHeartbeats 8000000 in
set_option warn.sorry false in
set_option linter.unusedSimpArgs false in
/-- **Reduction transfer at good primes** (sorry node — the
Néron–Ogg–Shafarevich reduction isomorphism): away from a finite set of
places (containing the places of bad reduction and the residue
characteristic `p`), the mod-`p` representation at the global Frobenius
of `q` is conjugate to the `q`-power Frobenius acting on the
`p`-torsion of an elliptic curve over `𝔽_q` (the reduction of a minimal
model of `E` at `q`). Ingredients available in
`KnownIn1980s/EllipticCurves/GoodReduction.lean`: torsion points have
integral coordinates at good places (`torsion_abscissa_mem`), distinct
torsion points have distinct reductions (`torsion_abscissa_residue_ne`,
injectivity of reduction on torsion), and inertia acts trivially
(`torsion_unramified_of_good_reduction`); surjectivity of reduction on
`p`-torsion follows from counting (`p ≠ q`, both torsion groups have
`p²` elements once the reduced curve's torsion is also counted), and
the Frobenius compatibility is the definition of the global Frobenius
on the residue extension. -/
theorem exists_frobenius_reduction_model (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p) (hodd : Odd p) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        haveI : Fact q.Prime := ⟨hq⟩
        ∃ (_ : q ≠ p) (Wbar : WeierstrassCurve (ZMod q))
          (_ : Wbar.IsElliptic)
          (ψ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)
            ≃ₗ[ZMod p]
            ((Wbar.map (algebraMap (ZMod q)
              (AlgebraicClosure (ZMod q)))).nTorsion p)),
          ∀ x, ψ (E.galoisRep p hppos
              (GaloisRepresentation.globalFrob
                hq.toHeightOneSpectrumRingOfIntegersRat) x) =
            frobeniusTorsionEnd q Wbar p (ψ x) := by
  classical
  -- Step 0: a global integral model — a variable change carrying `E` to
  -- the base change of a curve over `ℤ` with nonzero discriminant
  have hkey : ∀ (a : ℚ) (m : ℕ), a.den ∣ m →
      ∃ b : ℤ, a * (m : ℚ) = (b : ℚ) := by
    rintro a m ⟨t, ht⟩
    refine ⟨a.num * t, ?_⟩
    have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
    have hmul : a * (a.den : ℚ) = (a.num : ℚ) := by
      have h1 : ((a.num : ℚ) / (a.den : ℚ)) * (a.den : ℚ) = (a.num : ℚ) :=
        div_mul_cancel₀ _ hden
      rwa [Rat.num_div_den] at h1
    rw [ht]
    push_cast
    rw [← mul_assoc, hmul]
  have hmodel : ∃ (C : WeierstrassCurve.VariableChange ℚ)
      (W : WeierstrassCurve ℤ),
      C • E = W.map (algebraMap ℤ ℚ) ∧ W.Δ ≠ 0 := by
    set N : ℕ := E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den
      with hNdef
    have hN0 : N ≠ 0 := by
      simp [hNdef]
    have hNQ0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
    set C : WeierstrassCurve.VariableChange ℚ :=
      ⟨Units.mk0 ((N : ℚ))⁻¹ (inv_ne_zero hNQ0), 0, 0, 0⟩ with hCdef
    -- each denominator divides `N`
    have hd1 : E.a₁.den ∣ N := ⟨E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den,
      by rw [hNdef]; ring⟩
    have hd2 : E.a₂.den ∣ N := ⟨E.a₁.den * E.a₃.den * E.a₄.den * E.a₆.den,
      by rw [hNdef]; ring⟩
    have hd3 : E.a₃.den ∣ N := ⟨E.a₁.den * E.a₂.den * E.a₄.den * E.a₆.den,
      by rw [hNdef]; ring⟩
    have hd4 : E.a₄.den ∣ N := ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₆.den,
      by rw [hNdef]; ring⟩
    have hd6 : E.a₆.den ∣ N := ⟨E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den,
      by rw [hNdef]; ring⟩
    obtain ⟨b₁, hb₁⟩ := hkey E.a₁ (N ^ 1) (hd1.trans (dvd_pow_self N one_ne_zero))
    obtain ⟨b₂, hb₂⟩ := hkey E.a₂ (N ^ 2) (hd2.trans (dvd_pow_self N two_ne_zero))
    obtain ⟨b₃, hb₃⟩ := hkey E.a₃ (N ^ 3) (hd3.trans (dvd_pow_self N three_ne_zero))
    obtain ⟨b₄, hb₄⟩ := hkey E.a₄ (N ^ 4) (hd4.trans (dvd_pow_self N four_ne_zero))
    obtain ⟨b₆, hb₆⟩ := hkey E.a₆ (N ^ 6) (hd6.trans (dvd_pow_self N (by norm_num)))
    have hmap : C • E =
        (⟨b₁, b₂, b₃, b₄, b₆⟩ : WeierstrassCurve ℤ).map
          (algebraMap ℤ ℚ) := by
      ext <;>
        simp only [WeierstrassCurve.variableChange_def, hCdef,
          WeierstrassCurve.map, Units.val_inv_eq_inv_val, Units.val_mk0,
          inv_inv, mul_zero, add_zero, zero_mul, zero_add, sub_zero,
          zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          eq_intCast, mul_one]
      · rw [← hb₁]
        push_cast
        ring
      · rw [← hb₂]
        push_cast
        ring
      · rw [← hb₃]
        push_cast
        ring
      · rw [← hb₄]
        push_cast
        ring
      · rw [← hb₆]
        push_cast
        ring
    refine ⟨C, ⟨b₁, b₂, b₃, b₄, b₆⟩, hmap, ?_⟩
    -- the integer discriminant is nonzero, since the `ℚ`-curve is
    -- elliptic and the variable change preserves that
    intro hz
    haveI : (C • E).IsElliptic := inferInstance
    have h1 : (C • E).Δ ≠ 0 := (C • E).isUnit_Δ.ne_zero
    apply h1
    rw [hmap, WeierstrassCurve.map_Δ, hz, map_zero]
  obtain ⟨C, W, hmap, hΔ0⟩ := hmodel
  -- Step 1: the excluded places — the primes dividing the integral
  -- discriminant, together with `p`
  set badPrimes : Finset ℕ := W.Δ.natAbs.primeFactors ∪ {p}
    with hbaddef
  refine ⟨badPrimes.image (fun r =>
    if h : r.Prime then h.toHeightOneSpectrumRingOfIntegersRat
    else Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat), ?_⟩
  intro q hq hqS
  haveI : Fact q.Prime := ⟨hq⟩
  have hqbad : q ∉ badPrimes := by
    intro hmem
    apply hqS
    refine Finset.mem_image.mpr ⟨q, hmem, ?_⟩
    rw [dif_pos hq]
  have hqp : q ≠ p := by
    intro hh
    exact hqbad (Finset.mem_union_right _ (Finset.mem_singleton.mpr hh))
  have hqΔ : ¬ ((q : ℤ) ∣ W.Δ) := by
    intro hdvd
    apply hqbad
    refine Finset.mem_union_left _ (Nat.mem_primeFactors.mpr
      ⟨hq, ?_, ?_⟩)
    · exact Int.natAbs_dvd_natAbs.mpr (by simpa using hdvd)
    · exact Int.natAbs_ne_zero.mpr hΔ0
  -- Step 2: the reduced curve over `𝔽_q` is elliptic
  set Wbar : WeierstrassCurve (ZMod q) := W.map (Int.castRingHom (ZMod q))
    with hWbardef
  have hWbarΔ : Wbar.Δ ≠ 0 := by
    rw [hWbardef, WeierstrassCurve.map_Δ]
    intro hzz
    exact hqΔ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzz)
  haveI hWbarell : Wbar.IsElliptic :=
    (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr hWbarΔ)
  refine ⟨hqp, Wbar, hWbarell, ?_⟩
  -- the model identification over `ℚ̄`: the base-changed variable
  -- change carries the base change of `E` to the base change of `W`
  have hmapbar : (C.map (algebraMap ℚ (AlgebraicClosure ℚ))) •
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) =
      W.map (algebraMap ℤ (AlgebraicClosure ℚ)) := by
    rw [WeierstrassCurve.map_variableChange, hmap,
      WeierstrassCurve.map_map]
    rfl
  -- Step 3a: the `E`-side point identification — collapse the trivial
  -- base change, apply the variable-change equivalence, and rewrite
  -- along the model equality
  have hid : ∀ V : WeierstrassCurve (AlgebraicClosure ℚ),
      ((V⁄(AlgebraicClosure ℚ)) : WeierstrassCurve (AlgebraicClosure ℚ))
        = V := by
    intro V
    show V.map (algebraMap (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) = V
    rw [show algebraMap (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) =
      RingHom.id (AlgebraicClosure ℚ) from rfl]
    exact V.map_id
  let hmodelPt :
      ((E.map (algebraMap ℚ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point ≃+
      ((W.map (algebraMap ℤ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point :=
    ((WeierstrassCurve.Affine.Point.equivOfEq
        (hid (E.map (algebraMap ℚ (AlgebraicClosure ℚ))))).trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))).symm.trans
        ((WeierstrassCurve.Affine.Point.equivOfEq hmapbar).trans
          (WeierstrassCurve.Affine.Point.equivOfEq
            (hid (W.map (algebraMap ℤ (AlgebraicClosure ℚ)))).symm))))
  -- Step 3b: restrict the point identification to `p`-torsion, as a
  -- `ZMod p`-linear equivalence
  have hmem : ∀ {A B : Type} [AddCommGroup A] [AddCommGroup B]
      (f : A ≃+ B) (x : A), (p : ℤ) • x = 0 → (p : ℤ) • f x = 0 := by
    intro A B _ _ f x hx
    rw [← map_zsmul f, hx, map_zero]
  let ψ₀add : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) ≃+
      ((W.map (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p) :=
    { toFun := fun x => ⟨hmodelPt x.1, (Submodule.mem_torsionBy_iff _ _).mpr
        (hmem hmodelPt x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2))⟩
      invFun := fun y => ⟨hmodelPt.symm y.1,
        (Submodule.mem_torsionBy_iff _ _).mpr
        (hmem hmodelPt.symm y.1
          ((Submodule.mem_torsionBy_iff _ _).mp y.2))⟩
      left_inv := fun x => Subtype.ext (hmodelPt.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (hmodelPt.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (map_add hmodelPt x.1 y.1) }
  let ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)
      ≃ₗ[ZMod p] ((W.map (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p) :=
    { ψ₀add with map_smul' := ZMod.map_smul ψ₀add.toAddMonoidHom }
  -- Step 3c-prep: the local valuation subring of the completed
  -- algebraic closure lies exactly over the completed integers (the
  -- `h𝒪`-hypothesis of the `GoodReduction` machinery)
  have h𝒪 : ((localValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).comap
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).toSubring
      = (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)).range := by
    ext c
    constructor
    · intro hc
      have h1 : IsIntegral
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (algebraMap
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) c) := hc
      have h2 := (isIntegral_algebraMap_iff
        (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).injective).mp h1
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      show _root_.IsIntegral _ _
      refine (isIntegral_algebraMap_iff
        (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).injective).mpr ?_
      exact isIntegral_algebraMap
  -- Step 3c-prep 3: integers prime to `q` are units of the completed
  -- integers (generalizing `isUnit_natCast_adicCompletionIntegers`)
  have hNatUnit : ∀ m : ℕ, ¬ ((q : ℤ) ∣ (m : ℤ)) →
      IsUnit ((m : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    intro m hm
    have hints : (Valued.v).Integers
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) :=
      Valuation.valuationSubring.integers _
    refine hints.isUnit_iff_valuation_eq_one.mpr ?_
    rw [map_natCast]
    have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (K := ℚ) (v := hq.toHeightOneSpectrumRingOfIntegersRat)
      ((m : ℕ) : NumberField.RingOfIntegers ℚ)
    push_cast at h2
    rw [h2, show ((m : ℕ) : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
        ((m : ℕ) : NumberField.RingOfIntegers ℚ) from (map_natCast _ m).symm,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    rw [Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hq]
    rwa [map_natCast]
  have hIntUnit : ∀ n : ℤ, ¬ ((q : ℤ) ∣ n) →
      IsUnit ((n : ℤ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    intro n hn
    have hnat := hNatUnit n.natAbs (by
      rwa [Int.dvd_natAbs])
    rcases Int.natAbs_eq n with he | he
    · rw [he, Int.cast_natCast]
      exact hnat
    · rw [he, Int.cast_neg, Int.cast_natCast]
      exact hnat.neg
  -- Step 3c-prep 4: the model over the completion is integral with unit
  -- discriminant, hence minimal with good reduction
  have hcompZ : (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)).comp
      (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) =
      algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    Subsingleton.elim _ _
  haveI hWvInt : WeierstrassCurve.IsIntegral
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    refine ⟨⟨W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), ?_⟩⟩
    show _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, hcompZ]
  -- Step 3c-prep 5: the model has unit discriminant valuation, hence is
  -- minimal with good reduction
  have hval1 : (IsDiscreteValuationRing.maximalIdeal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)).valuation
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Δ = 1 := by
    have hΔunit := hIntUnit W.Δ hqΔ
    have hΔeq : (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Δ =
        algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          ((W.Δ : ℤ) :
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      rw [WeierstrassCurve.map_Δ, ← hcompZ]
      rfl
    rw [hΔeq]
    obtain ⟨u, hu⟩ := hΔunit
    have h1 : (IsDiscreteValuationRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)).valuation
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) (u : _)) *
        (IsDiscreteValuationRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)).valuation
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) ((u⁻¹ : _ˣ) : _)) =
        1 := by
      rw [← map_mul, ← map_mul]
      norm_cast
      simp
    have h2 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (K := (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (u : _)
    have h3 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (K := (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ((u⁻¹ : _ˣ) : _)
    rw [← hu]
    refine le_antisymm h2 ?_
    rw [← h1]
    exact le_trans (mul_le_mul' le_rfl h3) (le_of_eq (mul_one _))
  haveI hWvMin : WeierstrassCurve.IsMinimal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    constructor
    refine ⟨?_, ?_⟩
    · simp only [one_smul]
      exact hWvInt
    · intro C' hC'
      have h2 : (WeierstrassCurve.valuation_Δ_aux
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          ((1 : WeierstrassCurve.VariableChange
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) •
            (W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))))) =
          ⟨1, le_rfl⟩ := by
        simp only [one_smul]
        refine Subtype.ext ?_
        rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
        exact hval1
      beta_reduce
      rw [h2]
      intro _
      rw [← Subtype.coe_le_coe]
      exact (WeierstrassCurve.valuation_Δ_aux
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (C' • (W.map (algebraMap ℤ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))))).2
  haveI hWvGood : WeierstrassCurve.HasGoodReduction
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) :=
    { goodReduction := hval1 }
  -- Step 3c-iv: transport the torsion along the embedding of algebraic
  -- closures into the completion — injective by `Point.map_injective`,
  -- bijective by the `p²`-count on both sides
  haveI hCZv : CharZero (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    charZero_of_injective_algebraMap
      (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).injective
  haveI : DecidableEq (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    Classical.typeDecidableEq _
  haveI hEllQ : (W.map (algebraMap ℤ (AlgebraicClosure ℚ))).IsElliptic :=
    (WeierstrassCurve.isElliptic_iff _).mpr (by
      rw [WeierstrassCurve.map_Δ]
      refine isUnit_iff_ne_zero.mpr (fun hz => hΔ0 ?_)
      exact (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int
        (hz.trans (map_zero _).symm))
  haveI hEllV : (W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic :=
    (WeierstrassCurve.isElliptic_iff _).mpr (by
      rw [WeierstrassCurve.map_Δ]
      refine isUnit_iff_ne_zero.mpr (fun hz => hΔ0 ?_)
      exact (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).injective_int
        (hz.trans (map_zero _).symm))
  have hcardQ : Nat.card ((W.map
      (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p) = p ^ 2 :=
    TorsionCard.card_torsionBy
      (W.map (algebraMap ℤ (AlgebraicClosure ℚ))) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hcardV : Nat.card ((W.map
      (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) =
      p ^ 2 :=
    TorsionCard.card_torsionBy
      (W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))) p
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  -- the point transport along the closure embedding
  set ιalg : (AlgebraicClosure ℚ) →ₐ[ℤ] (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    { toRingHom := AlgebraicClosure.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      commutes' := fun n => by
        show AlgebraicClosure.map _ (algebraMap ℤ _ n) = algebraMap ℤ _ n
        rw [eq_intCast (algebraMap ℤ (AlgebraicClosure ℚ)) n,
          eq_intCast (algebraMap ℤ (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) n,
          map_intCast] } with hιalgdef
  have hcollapseQ : (((W.map (algebraMap ℤ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)) :
        WeierstrassCurve (AlgebraicClosure ℚ)) =
      ((W⁄(AlgebraicClosure ℚ)) :
        WeierstrassCurve (AlgebraicClosure ℚ)) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  have hcollapseV : (((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :
        WeierstrassCurve (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) =
      ((W⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) :
        WeierstrassCurve (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  set Pmap : ((W.map (algebraMap ℤ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point →+
      ((W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point :=
    (((WeierstrassCurve.Affine.Point.equivOfEq
        hcollapseV.symm).toAddMonoidHom).comp
      ((WeierstrassCurve.Affine.Point.map (W' := W) (S := ℤ)
        ιalg).comp
        ((WeierstrassCurve.Affine.Point.equivOfEq
          hcollapseQ).toAddMonoidHom))) with hPmapdef
  have hPinj : Function.Injective Pmap := by
    simp only [hPmapdef, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom]
    exact ((WeierstrassCurve.Affine.Point.equivOfEq
        hcollapseV.symm).injective.comp
      ((WeierstrassCurve.Affine.Point.map_injective (W' := W)
        (f := ιalg)).comp
        (WeierstrassCurve.Affine.Point.equivOfEq
          hcollapseQ).injective))
  have hτmem : ∀ x : ((W.map (algebraMap ℤ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point,
      (p : ℤ) • x = 0 → (p : ℤ) • Pmap x = 0 := by
    intro x hx
    rw [← map_zsmul, hx, map_zero]
  set τ₀ : ((W.map (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p) →+
      ((W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    { toFun := fun x => ⟨Pmap x.1,
        (Submodule.mem_torsionBy_iff _ _).mpr (hτmem x.1
          ((Submodule.mem_torsionBy_iff _ _).mp x.2))⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1) } with hτ₀def
  have hτinj : Function.Injective τ₀ := by
    intro x y hxy
    apply Subtype.ext
    exact hPinj (congrArg Subtype.val hxy)
  have hτbij : Function.Bijective τ₀ := by
    haveI : Finite ((W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
      Nat.finite_of_card_ne_zero (by
        rw [hcardV]
        positivity)
    refine (Nat.bijective_iff_injective_and_card τ₀).mpr ⟨hτinj, ?_⟩
    rw [hcardQ, hcardV]
  set τadd : ((W.map (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p) ≃+
      ((W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    AddEquiv.ofBijective τ₀ hτbij with hτadddef
  set τ : ((W.map (algebraMap ℤ (AlgebraicClosure ℚ))).nTorsion p)
      ≃ₗ[ZMod p]
      ((W.map (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    { τadd with map_smul' := ZMod.map_smul τadd.toAddMonoidHom }
    with hτdef
  -- Step 3c-ii-a: every nonzero projective triple over the completed
  -- closure has a scaling with integral coordinates, one of them a unit
  -- of the valuation subring (divide by a dominant coordinate)
  have hdom : ∀ a b : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), a ≠ 0 →
      (∃ j : Bool, (if j then a else b) ≠ 0 ∧
        (if j then b else a) / (if j then a else b) ∈
          localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) := by
    intro a b ha
    by_cases hb : b = 0
    · exact ⟨true, ha, by simp [hb, zero_mem]⟩
    · rcases ValuationSubring.mem_or_inv_mem
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
        (b / a) with h | h
      · exact ⟨true, ha, by simpa using h⟩
      · refine ⟨false, hb, ?_⟩
        simpa [inv_div] using h
  -- upgraded form: the dominant element is one of the two inputs and
  -- dominates both
  have hdom' : ∀ a b : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), a ≠ 0 →
      ∃ c, (c = a ∨ c = b) ∧ c ≠ 0 ∧
        a / c ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat ∧
        b / c ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro a b ha
    obtain ⟨j, hjne, hjdom⟩ := hdom a b ha
    cases j with
    | true =>
      refine ⟨a, Or.inl rfl, ha, ?_, by simpa using hjdom⟩
      rw [div_self ha]; exact one_mem _
    | false =>
      refine ⟨b, Or.inr rfl, by simpa using hjne, by simpa using hjdom, ?_⟩
      rw [div_self (by simpa using hjne)]; exact one_mem _
  -- transitivity of division-domination
  have hdivtrans : ∀ a b c : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), b ≠ 0 →
      a / b ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat →
      b / c ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat →
      a / c ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro a b c hb hab hbc
    have hrw : a / c = a / b * (b / c) := by
      rw [div_mul_div_comm, mul_comm b c, mul_div_mul_right _ _ hb]
    rw [hrw]; exact mul_mem hab hbc
  -- Step 3c-ii-a: every projective triple with a nonzero coordinate has a
  -- dominant coordinate: all three ratios into it are integral
  have hnorm3 : ∀ P : Fin 3 → (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), (∃ i, P i ≠ 0) →
      ∃ j, P j ≠ 0 ∧ ∀ i, P i / P j ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro P hP
    obtain ⟨i, hi⟩ := hP
    obtain ⟨c₁, hc₁or, hc₁ne, hic₁, h0c₁⟩ := hdom' (P i) (P 0) hi
    obtain ⟨c₂, hc₂or, hc₂ne, hc₁c₂, h1c₂⟩ := hdom' c₁ (P 1) hc₁ne
    obtain ⟨c₃, hc₃or, hc₃ne, hc₂c₃, h2c₃⟩ := hdom' c₂ (P 2) hc₂ne
    have hc₁c₃ : c₁ / c₃ ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
      hdivtrans _ _ _ hc₂ne hc₁c₂ hc₂c₃
    have h0c₃ : P 0 / c₃ ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
      hdivtrans _ _ _ hc₁ne h0c₁ hc₁c₃
    have h1c₃ : P 1 / c₃ ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
      hdivtrans _ _ _ hc₂ne h1c₂ hc₂c₃
    have hic₃ : P i / c₃ ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
      hdivtrans _ _ _ hc₁ne hic₁ hc₁c₃
    have hall : ∀ k, P k / c₃ ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
      intro k
      fin_cases k
      · exact h0c₃
      · exact h1c₃
      · exact h2c₃
    have hc₃eq : ∃ j, c₃ = P j := by
      rcases hc₃or with rfl | rfl
      · rcases hc₂or with rfl | rfl
        · rcases hc₁or with rfl | rfl
          · exact ⟨i, rfl⟩
          · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    obtain ⟨j, rfl⟩ := hc₃eq
    exact ⟨j, hc₃ne, hall⟩
  -- Step 3c-ii-b: `p` is invertible in the residue field of the
  -- completed integers (`p` is a unit of `𝒪ᵥ` since `p ≠ q`)
  haveI hpres : NeZero ((p : ℕ) : IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    refine ⟨fun h0 => ?_⟩
    have hu : IsUnit ((p : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      GaloisRepresentation.isUnit_natCast_adicCompletionIntegers
        (Fact.out : p.Prime) hq (fun h => hqp h.symm)
    have hres := hu.map (IsLocalRing.residue
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    rw [map_natCast] at hres
    rw [h0] at hres
    exact not_isUnit_zero hres
  -- Step 3c-ii-c: the minimal model at `v`, base-changed to `Kᵥ`, is
  -- elliptic
  haveI hEllKv : (W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).IsElliptic :=
    (WeierstrassCurve.isElliptic_iff _).mpr (by
      rw [WeierstrassCurve.map_Δ]
      refine isUnit_iff_ne_zero.mpr (fun hz => hΔ0 ?_)
      exact (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)).injective_int
        (hz.trans (map_zero _).symm))
  -- Step 3c-ii-d: torsion abscissas of the model over the completed
  -- algebraic closure are integral for the local valuation subring
  have habs : ∀ {x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))}
      (h : ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular
        x y),
      ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        ((W.map (algebraMap ℤ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) = 0 →
      x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
    fun h htor => WeierstrassCurve.torsion_abscissa_mem
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
      h𝒪 h htor
  -- Step 3c-ii-e: torsion ordinates are likewise integral
  have hord : ∀ {x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))}
      (h : ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular
        x y),
      ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        ((W.map (algebraMap ℤ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) = 0 →
      y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
    fun h htor => WeierstrassCurve.torsion_ordinate_mem
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
      h𝒪 h htor
  -- Step 3c-ii-f: integers prime to `q` remain units in the local
  -- valuation subring of the completed algebraic closure (transport the
  -- `𝒪ᵥ`-unit through the lying-over identity `h𝒪`)
  have hIntUnitLoc : ∀ n : ℤ, ¬ ((q : ℤ) ∣ n) →
      IsUnit ((n : ℤ) :
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    intro n hn
    obtain ⟨u, hu⟩ := hIntUnit n hn
    have hprodO : (u : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) * ((u⁻¹ :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) = 1 := u.mul_inv
    -- the image of the inverse lies in the local valuation subring
    have hinvmem : algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
        (((u⁻¹ : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
      have hrange : (((u⁻¹ :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ∈
          (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)).range := ⟨_, rfl⟩
      rw [← h𝒪] at hrange
      exact hrange
    have hprodK : ((n : ℤ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) *
        (((u⁻¹ : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) = 1 := by
      have hcast := congrArg (fun z :
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) =>
          (z : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) hprodO
      push_cast at hcast
      rw [← hcast]
      push_cast [hu]
      ring
    have hfin := congrArg (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) hprodK
    rw [map_mul, map_one, map_intCast] at hfin
    refine isUnit_iff_exists.mpr ⟨⟨_, hinvmem⟩, ?_, ?_⟩
    · exact Subtype.ext hfin
    · refine Subtype.ext ?_
      show _ * ((n : ℤ) : (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) = 1
      rw [mul_comm]
      exact hfin
  -- Step 3c-ii-g: the reduced curve over the residue field of the local
  -- valuation subring is elliptic (its discriminant is the residue of a
  -- unit)
  haveI hEllRes : (W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic := by
    refine (WeierstrassCurve.isElliptic_iff _).mpr ?_
    rw [WeierstrassCurve.map_Δ]
    have hu := (hIntUnitLoc W.Δ hqΔ).map (IsLocalRing.residue
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))
    rw [map_intCast] at hu
    rwa [show algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) W.Δ
      = ((W.Δ : ℤ) : IsLocalRing.ResidueField
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))
      from eq_intCast _ _]
  -- Step 3c-ii-h: the coordinatewise residue of an integral solution of
  -- the Weierstrass equation is a nonsingular point of the reduced curve
  have hredNS : ∀ (x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
      (hx : x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
      (hy : y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat),
      ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Equation x y →
      (W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Nonsingular
        (IsLocalRing.residue
          (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
          (⟨x, hx⟩ : localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat))
        (IsLocalRing.residue
          (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
          (⟨y, hy⟩ : localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    intro x y hx hy heq
    haveI : ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine).IsElliptic :=
      inferInstanceAs ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic)
    refine (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := (W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine)).mp ?_
    rw [WeierstrassCurve.Affine.equation_iff] at heq ⊢
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast,
      map_intCast] at heq ⊢
    -- lift the equation to the valuation subring
    have heqO : (⟨y, hy⟩ : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) ^ 2 +
        ((W.a₁ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨x, hx⟩ * ⟨y, hy⟩ +
        ((W.a₃ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨y, hy⟩ =
        (⟨x, hx⟩ : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) ^ 3 +
        ((W.a₂ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨x, hx⟩ ^ 2 +
        ((W.a₄ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨x, hx⟩ +
        ((W.a₆ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) := by
      apply Subtype.ext
      push_cast
      exact heq
    have hres := congrArg (IsLocalRing.residue
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) heqO
    simp only [map_add, map_mul, map_pow, map_intCast] at hres
    exact hres
  -- Step 3c-ii-i: the reduction map on points — zero to zero, an
  -- integral affine point to its coordinatewise residue (non-integral
  -- points, which never arise on `p`-torsion, go to zero)
  let redFun : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point →
      (W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Point :=
    fun P => match P with
    | WeierstrassCurve.Affine.Point.zero => 0
    | WeierstrassCurve.Affine.Point.some x y h =>
      if hxy : x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat
          ∧ y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat
        then
        WeierstrassCurve.Affine.Point.some
          (IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            (⟨x, hxy.1⟩ : localValuationSubring
              hq.toHeightOneSpectrumRingOfIntegersRat))
          (IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            (⟨y, hxy.2⟩ : localValuationSubring
              hq.toHeightOneSpectrumRingOfIntegersRat))
          (hredNS x y hxy.1 hxy.2 h.1)
      else 0
  -- Step 3c-ii-j: computation rules for `redFun`
  have hred0 : redFun 0 = 0 := rfl
  have hredSome : ∀ {x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))}
      (h : ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular
        x y)
      (hx : x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
      (hy : y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat),
      redFun (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some
          (IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            ⟨x, hx⟩)
          (IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            ⟨y, hy⟩)
          (hredNS x y hx hy h.1) := by
    intro x y h hx hy
    show (if hxy : _ ∧ _ then _ else 0) = _
    rw [dif_pos ⟨hx, hy⟩]
  -- membership and residue-commutation for the negation ordinate
  have hnegYmem : ∀ (x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))),
      x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat →
      y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat →
      ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x y ∈
        localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro x y hx hy
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast,
      map_intCast]
    exact sub_mem (sub_mem (neg_mem hy)
      (mul_mem (intCast_mem _ _) hx)) (intCast_mem _ _)
  have hnegYres : ∀ (x y : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
      (hx : x ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
      (hy : y ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat),
      IsLocalRing.residue
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
        ⟨((W.map (algebraMap ℤ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x y,
          hnegYmem x y hx hy⟩ =
      (W.map (algebraMap ℤ (IsLocalRing.ResidueField
        (localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.negY
        (IsLocalRing.residue
          (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
          ⟨x, hx⟩)
        (IsLocalRing.residue
          (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
          ⟨y, hy⟩) := by
    intro x y hx hy
    have hsub : (⟨((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x y,
        hnegYmem x y hx hy⟩ : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) =
        -⟨y, hy⟩ - ((W.a₁ : ℤ) : localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨x, hx⟩ -
          ((W.a₃ : ℤ) : localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat) := by
      apply Subtype.ext
      push_cast
      simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.baseChange,
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast,
        map_intCast]
    rw [hsub]
    simp only [map_sub, map_neg, map_mul, map_intCast,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃, eq_intCast]
  -- Step 3c-ii-k: additivity of `redFun` on `p`-torsion — the zero and
  -- mutually-opposite cases; the generic slope case is the open frontier
  have hredAdd : ∀ (P Q : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point),
      ((p : ℕ) : ℤ) • P = 0 → ((p : ℕ) : ℤ) • Q = 0 →
      redFun (P + Q) = redFun P + redFun Q := by
    intro P Q hP hQ
    cases P with
    | zero =>
      rw [show (WeierstrassCurve.Affine.Point.zero : ((W.map (algebraMap ℤ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) = 0
        from rfl, zero_add, hred0, zero_add]
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        rw [show (WeierstrassCurve.Affine.Point.zero : ((W.map (algebraMap ℤ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) = 0
          from rfl, add_zero, hred0, add_zero]
      | some x₂ y₂ h₂ =>
        have hx₁ := habs h₁ hP
        have hy₁ := hord h₁ hP
        have hx₂ := habs h₂ hQ
        have hy₂ := hord h₂ hQ
        by_cases hopp : x₁ = x₂ ∧ y₁ = ((W.map (algebraMap ℤ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x₂ y₂
        · -- opposite points: both sums vanish
          rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hopp.1 hopp.2, hred0,
            hredSome h₁ hx₁ hy₁, hredSome h₂ hx₂ hy₂,
            WeierstrassCurve.Affine.Point.add_of_Y_eq]
          · exact congrArg _ (Subtype.ext hopp.1)
          · rw [← hnegYres x₂ y₂ hx₂ hy₂]
            exact congrArg _ (Subtype.ext hopp.2)
        · -- generic case: both sums are finite; the slope is integral
          -- and the addition formulas commute with the residue
          -- unit criterion: nonzero residue means unit
          have hunit : ∀ z : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat),
              (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) z ≠ 0 → IsUnit z := by
            intro z hz
            by_contra hu
            exact hz ((Ideal.Quotient.eq_zero_iff_mem).mpr
              ((IsLocalRing.mem_maximalIdeal _).mpr hu))
          -- residue of a subring unit's inverse is the inverse residue,
          -- and unit denominators make division integral: packaged as
          -- the slope triple below
          obtain ⟨hℓmem, hℓres, hoppbar⟩ :
              ∃ hm : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂ ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat,
              (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂, hm⟩ =
                (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.slope
                  ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                  ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩) ∧
              ¬(((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) = ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩) ∧
                ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) =
                  (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.negY
                    ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩)) := by
            by_cases hx12 : x₁ = x₂
            · -- tangent case: the ordinates agree and the doubling
              -- denominator has nonzero residue
              have hyy : y₁ = y₂ := by
                rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hx12
                  with h | h
                · exact h
                · exact absurd ⟨hx12, h⟩ hopp
              subst hx12
              subst hyy
              -- exclusion: the reduced ordinate is not the reduced
              -- negation (else the ordinate equality theorem forces the
              -- upstairs collision)
              have hyneg : ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) ≠
                  (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.negY
                    ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) := by
                intro hcol
                refine hopp ⟨rfl, ?_⟩
                refine WeierstrassCurve.torsion_ordinate_eq_of_residue_eq
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat)
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat)
                  (W.map (algebraMap ℤ
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))
                  p
                  (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat))
                  (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
                  (Fact.out : p.Prime) hodd h𝒪 h₁
                  ((WeierstrassCurve.Affine.nonsingular_neg _ _).mpr h₁)
                  hP hx₁ hy₁ (hnegYmem x₁ y₁ hx₁ hy₁) ?_
                rw [hnegYres x₁ y₁ hx₁ hy₁]
                exact hcol
              -- the doubling denominator as a unit of the subring
              have hdenU : IsUnit ((⟨y₁, hy₁⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) -
                  ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x₁ y₁, hnegYmem x₁ y₁ hx₁ hy₁⟩) := by
                refine hunit _ ?_
                rw [map_sub, hnegYres x₁ y₁ hx₁ hy₁]
                exact sub_ne_zero.mpr hyneg
              have hdenne : (y₁ - ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x₁ y₁) ≠ 0 := by
                intro h0
                apply hyneg
                have hyeq : (⟨y₁, hy₁⟩ : localValuationSubring
                    hq.toHeightOneSpectrumRingOfIntegersRat) =
                    ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x₁ y₁, hnegYmem x₁ y₁ hx₁ hy₁⟩ :=
                  Subtype.ext (sub_eq_zero.mp h0)
                nth_rewrite 1 [hyeq]
                rw [hnegYres x₁ y₁ hx₁ hy₁]
              obtain ⟨v, hv⟩ := hdenU
              -- the numerator of the tangent slope, as a subring element
              have hnummem : (3 * x₁ ^ 2 + 2 * ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₂ * x₁ + ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₄ -
                  ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₁ * y₁) ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
                simp only [WeierstrassCurve.baseChange,
                  WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
                  WeierstrassCurve.map_a₄, eq_intCast, map_intCast]
                refine sub_mem (add_mem (add_mem ?_ ?_) ?_) ?_
                · exact mul_mem (by
                    exact_mod_cast intCast_mem (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) 3) (pow_mem hx₁ 2)
                · exact mul_mem (mul_mem (by
                    exact_mod_cast intCast_mem (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) 2)
                    (intCast_mem _ _)) hx₁
                · exact intCast_mem _ _
                · exact mul_mem (intCast_mem _ _) hy₁
              -- the inverse of the denominator at the value level
              have hinvval : (((v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat))) =
                  (y₁ - ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY x₁ y₁)⁻¹ := by
                symm
                refine inv_eq_of_mul_eq_one_right ?_
                have hmulO := v.mul_inv
                rw [hv] at hmulO
                have := congrArg (fun z : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (z :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))) hmulO
                push_cast at this
                exact this
              -- the slope at the value level
              have hslopeval : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₁ y₁ y₁ =
                  ((((⟨3 * x₁ ^ 2 + 2 * ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₂ * x₁ + ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₄ -
                    ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₁ * y₁, hnummem⟩ *
                    (v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ)) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))) := by
                rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (by
                  intro hy0
                  exact hdenne (sub_eq_zero.mpr hy0))]
                push_cast
                rw [hinvval, div_eq_mul_inv]
              have hℓmem : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₁ y₁ y₁ ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
                rw [hslopeval]
                exact Subtype.coe_prop _
              refine ⟨hℓmem, ?_, ?_⟩
              · -- the residue of the slope is the reduced tangent slope
                have hsub : (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₁ y₁ y₁, hℓmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
                    ⟨3 * x₁ ^ 2 + 2 * ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₂ * x₁ + ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₄ -
                      ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₁ * y₁, hnummem⟩ * (v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :=
                  Subtype.ext hslopeval
                rw [hsub]
                -- reduced side: tangent slope with the same residue data
                rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
                -- the residue of the unit inverse is the inverse of the
                -- denominator's residue
                have hresinv : (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ((v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) =
                    (((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) -
                      (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.negY ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩)
                        ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩))⁻¹ := by
                  symm
                  refine inv_eq_of_mul_eq_one_right ?_
                  have hmulO := v.mul_inv
                  rw [hv] at hmulO
                  have hmapped := congrArg (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) hmulO
                  rw [map_mul, map_one, map_sub,
                    hnegYres x₁ y₁ hx₁ hy₁] at hmapped
                  exact hmapped
                rw [map_mul, hresinv, div_eq_mul_inv]
                congr 1
                -- residue of the numerator
                have hnumsub : (⟨3 * x₁ ^ 2 + 2 * ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₂ * x₁ +
                    ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₄ - ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.a₁ * y₁, hnummem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
                    3 * ⟨x₁, hx₁⟩ ^ 2 + 2 * ((W.a₂ : ℤ) : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) *
                      ⟨x₁, hx₁⟩ + ((W.a₄ : ℤ) : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) -
                      ((W.a₁ : ℤ) : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨y₁, hy₁⟩ := by
                  apply Subtype.ext
                  push_cast
                  simp only [WeierstrassCurve.baseChange,
                    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
                    WeierstrassCurve.map_a₄, eq_intCast, map_intCast]
                  norm_cast
                rw [hnumsub]
                simp only [map_add, map_sub, map_mul, map_pow,
                  map_intCast, map_ofNat, WeierstrassCurve.map_a₁,
                  WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
                  eq_intCast]
              · -- no reduced collision in the tangent case
                intro hcol
                exact hyneg hcol.2
            · -- chord case: the abscissas are distinct with distinct
              -- residues, so the chord denominator is a unit
              have hxres : ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ≠ ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩) :=
                WeierstrassCurve.torsion_abscissa_residue_ne
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat)
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat)
                  (W.map (algebraMap ℤ
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))
                  p
                  (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                    hq.toHeightOneSpectrumRingOfIntegersRat))
                  (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
                  (Fact.out : p.Prime) hodd h𝒪 h₁ h₂ hP hQ hx12 hx₁ hx₂
              have hdenU : IsUnit ((⟨x₁, hx₁⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) - ⟨x₂, hx₂⟩) := by
                refine hunit _ ?_
                rw [map_sub]
                exact sub_ne_zero.mpr hxres
              have hdenne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
              obtain ⟨v, hv⟩ := hdenU
              have hinvval : (((v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat))) =
                  (x₁ - x₂)⁻¹ := by
                symm
                refine inv_eq_of_mul_eq_one_right ?_
                have hmulO := v.mul_inv
                rw [hv] at hmulO
                have := congrArg (fun z : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (z :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))) hmulO
                push_cast at this
                exact this
              have hslopeval : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂ =
                  ((((⟨y₁ - y₂, sub_mem hy₁ hy₂⟩ *
                    (v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ)) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                      hq.toHeightOneSpectrumRingOfIntegersRat)))) := by
                rw [WeierstrassCurve.Affine.slope_of_X_ne hx12]
                push_cast
                rw [hinvval, div_eq_mul_inv]
              have hℓmem : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂ ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
                rw [hslopeval]
                exact Subtype.coe_prop _
              refine ⟨hℓmem, ?_, ?_⟩
              · have hsub : (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂, hℓmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
                    ⟨y₁ - y₂, sub_mem hy₁ hy₂⟩ * (v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :=
                  Subtype.ext hslopeval
                rw [hsub]
                rw [WeierstrassCurve.Affine.slope_of_X_ne hxres]
                have hresinv : (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ((v⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) =
                    (((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) - ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩))⁻¹ := by
                  symm
                  refine inv_eq_of_mul_eq_one_right ?_
                  have hmulO := v.mul_inv
                  rw [hv] at hmulO
                  have hmapped := congrArg (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) hmulO
                  rw [map_mul, map_one, map_sub] at hmapped
                  exact hmapped
                rw [show (⟨y₁ - y₂, sub_mem hy₁ hy₂⟩ : localValuationSubring
                    hq.toHeightOneSpectrumRingOfIntegersRat) =
                  (⟨y₁, hy₁⟩ : localValuationSubring
                    hq.toHeightOneSpectrumRingOfIntegersRat) - ⟨y₂, hy₂⟩
                  from rfl, map_mul, map_sub, hresinv, div_eq_mul_inv]
              · intro hcol
                exact hxres hcol.1
          -- final computation: both additions are `some` of the addition
          -- formulas, and the formulas commute with the residue
          have hsome : ∀ {xa xb ya yb : IsLocalRing.ResidueField
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)}
              {ha : (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Nonsingular xa ya} {hb : (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Nonsingular xb yb},
              xa = xb → ya = yb →
              (WeierstrassCurve.Affine.Point.some xa ya ha :
                (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Point) =
                WeierstrassCurve.Affine.Point.some xb yb hb := by
            intro xa xb ya yb ha hb hxab hyab
            subst hxab
            subst hyab
            rfl
          -- integrality of the addition formulas
          have haddXmem : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addX x₁ x₂
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂) ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
            simp only [WeierstrassCurve.Affine.addX,
              WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₂, eq_intCast, map_intCast]
            exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hℓmem 2)
              (mul_mem (intCast_mem _ _) hℓmem)) (intCast_mem _ _)) hx₁) hx₂
          have hnegAddYmem : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negAddY x₁ x₂ y₁
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂) ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
            simp only [WeierstrassCurve.Affine.negAddY]
            exact add_mem (mul_mem hℓmem (sub_mem haddXmem hx₁)) hy₁
          have haddYmem : ((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addY x₁ x₂ y₁
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂) ∈ localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat := by
            simp only [WeierstrassCurve.Affine.addY]
            exact hnegYmem _ _ haddXmem hnegAddYmem
          -- rewrite both floors to `some` of the formulas
          rw [WeierstrassCurve.Affine.Point.add_some hopp,
            hredSome (WeierstrassCurve.Affine.nonsingular_add h₁ h₂
              hopp) haddXmem haddYmem,
            hredSome h₁ hx₁ hy₁, hredSome h₂ hx₂ hy₂,
            WeierstrassCurve.Affine.Point.add_some hoppbar]
          -- the reduced abscissa of the sum
          have hXsub : (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addX x₁ x₂
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), haddXmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
              (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂, hℓmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ^ 2 +
              ((W.a₁ : ℤ) : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) * ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂, hℓmem⟩ -
              ((W.a₂ : ℤ) : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) - ⟨x₁, hx₁⟩ - ⟨x₂, hx₂⟩ := by
            apply Subtype.ext
            push_cast
            simp only [WeierstrassCurve.Affine.addX,
              WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₂, eq_intCast, map_intCast]
          have hXeq : (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addX x₁ x₂
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), haddXmem⟩ =
              (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.addX ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.slope ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                  ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩)) := by
            rw [hXsub, ← hℓres]
            simp only [map_add, map_sub, map_mul, map_pow, map_intCast,
              WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₂, eq_intCast]
          -- the reduced ordinate of the sum
          have hnegAddYsub : (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negAddY x₁ x₂ y₁
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), hnegAddYmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
              (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂, hℓmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) *
                (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addX x₁ x₂ (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), haddXmem⟩ -
                  ⟨x₁, hx₁⟩) + ⟨y₁, hy₁⟩ := by
            apply Subtype.ext
            push_cast
            simp only [WeierstrassCurve.Affine.negAddY]
          have hnegAddYeq : (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negAddY x₁ x₂ y₁
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), hnegAddYmem⟩ =
              (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.negAddY ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩)
                ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.slope ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                  ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩)) := by
            rw [hnegAddYsub, ← hℓres]
            simp only [map_add, map_sub, map_mul,
              WeierstrassCurve.Affine.negAddY]
            rw [hXeq, hℓres]
          have hYeq : (IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addY x₁ x₂ y₁
              (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), haddYmem⟩ =
              (W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.addY ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩)
                ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
              (localValuationSubring
                hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.slope ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩)
                  ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) ((IsLocalRing.residue
              (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩)) := by
            have haddYsub : (⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addY x₁ x₂ y₁
                (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂), haddYmem⟩ : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) =
                ⟨((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negY (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.addX x₁ x₂ (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂))
                  (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.negAddY x₁ x₂ y₁ (((W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.slope x₁ x₂ y₁ y₂)),
                  hnegYmem _ _ haddXmem hnegAddYmem⟩ := by
              apply Subtype.ext
              simp only [WeierstrassCurve.Affine.addY]
            rw [haddYsub, hnegYres _ _ haddXmem hnegAddYmem, hXeq,
              hnegAddYeq]
            simp only [WeierstrassCurve.Affine.addY]
          exact hsome hXeq hYeq
  -- the zero rule in constructor spelling
  have hred0' : redFun WeierstrassCurve.Affine.Point.zero = 0 := rfl
  -- Step 3c-ii-l: the reduction map is injective on `p`-torsion (the
  -- residue-injectivity theorems of the good-reduction machinery)
  have hredInj : ∀ (P Q : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point),
      ((p : ℕ) : ℤ) • P = 0 → ((p : ℕ) : ℤ) • Q = 0 →
      redFun P = redFun Q → P = Q := by
    intro P Q hP hQ hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x₂ y₂ h₂ =>
        rw [hred0'] at hPQ
        rw [hredSome h₂ (habs h₂ hQ) (hord h₂ hQ)] at hPQ
        exact absurd hPQ.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        rw [hred0'] at hPQ
        rw [hredSome h₁ (habs h₁ hP) (hord h₁ hP)] at hPQ
        exact absurd hPQ (WeierstrassCurve.Affine.Point.some_ne_zero _)
      | some x₂ y₂ h₂ =>
        have hx₁ := habs h₁ hP
        have hy₁ := hord h₁ hP
        have hx₂ := habs h₂ hQ
        have hy₂ := hord h₂ hQ
        rw [hredSome h₁ hx₁ hy₁, hredSome h₂ hx₂ hy₂] at hPQ
        obtain ⟨hrx, hry⟩ : ((IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₁, hx₁⟩) = ((IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨x₂, hx₂⟩) ∧
            ((IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₁, hy₁⟩) = ((IsLocalRing.residue
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ⟨y₂, hy₂⟩) := by
          injection hPQ with h1 h2
          exact ⟨h1, h2⟩
        have hxx : x₁ = x₂ := by
          by_contra hne
          exact WeierstrassCurve.torsion_abscissa_residue_ne
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)
            (W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))
            p
            (AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                  hq.toHeightOneSpectrumRingOfIntegersRat))
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            (Fact.out : p.Prime) hodd h𝒪 h₁ h₂ hP hQ hne hx₁ hx₂ hrx
        subst hxx
        have hyy : y₁ = y₂ :=
          WeierstrassCurve.torsion_ordinate_eq_of_residue_eq
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)
            (W.map (algebraMap ℤ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)))
            p
            (AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                  hq.toHeightOneSpectrumRingOfIntegersRat))
            (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
            (Fact.out : p.Prime) hodd h𝒪 h₁ h₂ hP hx₁ hy₁ hy₂ hry
        subst hyy
        rfl
  -- Step 3c-ii-m: membership from integrality — the valuation subring
  -- is integrally closed in the completed algebraic closure
  have hintmem : ∀ z : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), IsIntegral (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) z → z ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) := by
    intro z hz
    have hI := Valuation.valuationSubring.integers
      (v := (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat : ValuationSubring (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).valuation)
    rw [ValuationSubring.valuationSubring_valuation] at hI
    have hmem := hI.mem_of_integral hz
    rw [ValuationSubring.integer_valuation] at hmem
    exact hmem
  -- Step 3c-ii-n: the residue field of the local valuation subring is
  -- algebraically closed (monic lift, root upstairs, integrality,
  -- residue of the root)
  haveI hACres : IsAlgClosed (IsLocalRing.ResidueField (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    apply IsAlgClosed.of_exists_root
    intro f hmonic hirr
    -- lift to a monic polynomial over the subring
    obtain ⟨F, hFmap, hFdeg, hFmonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic
        ((Polynomial.mem_lifts f).mpr
          (Polynomial.map_surjective _ (IsLocalRing.residue_surjective) f))
        hmonic
    -- the coefficientwise inclusion into the field has a root
    have hdegne : (F.map (algebraMap (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective (Subtype.coe_injective)]
      rw [hFdeg]
      exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
      (k := (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) (F.map (algebraMap (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) hdegne
    -- the root is integral over the subring, hence lies in it
    have hzint : IsIntegral (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) z := by
      refine ⟨F, hFmonic, ?_⟩
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at hz
    have hzmem := hintmem z hzint
    -- its residue is a root of `f`
    refine ⟨IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨z, hzmem⟩, ?_⟩
    have hFz : Polynomial.eval (⟨z, hzmem⟩ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) F = 0 := by
      have hval : ((Polynomial.eval (⟨z, hzmem⟩ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) F : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
          (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = 0 := by
        show (algebraMap (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
          (Polynomial.eval (⟨z, hzmem⟩ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) F) = 0
        rw [← Polynomial.eval₂_at_apply
          (algebraMap (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) ⟨z, hzmem⟩]
        show Polynomial.eval₂ _ z F = 0
        rw [← Polynomial.eval_map]
        exact hz
      exact Subtype.ext hval
    rw [← hFmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hFz,
      map_zero]
  -- Step 3c-ii-o: the reduction map commutes with natural scalar
  -- multiples of torsion points (induction from additivity)
  have hredsmul : ∀ (n : ℕ) (P : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point),
      ((p : ℕ) : ℤ) • P = 0 →
      redFun ((n : ℤ) • P) = (n : ℤ) • redFun P := by
    intro n
    induction n with
    | zero =>
      intro P hP
      simp only [Nat.cast_zero, zero_zsmul]
      exact hred0
    | succ m ih =>
      intro P hP
      have hsmul : ((m + 1 : ℕ) : ℤ) • P = (m : ℤ) • P + P := by
        push_cast
        rw [add_zsmul, one_zsmul]
      have hmtor : ((p : ℕ) : ℤ) • ((m : ℤ) • P) = 0 := by
        rw [← mul_zsmul, mul_comm, mul_zsmul, hP, zsmul_zero]
      rw [hsmul, hredAdd _ _ hmtor hP, ih P hP]
      push_cast
      rw [add_zsmul, one_zsmul]
  -- the reduction of a `p`-torsion point is `p`-torsion
  have hredtor : ∀ (P : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point), ((p : ℕ) : ℤ) • P = 0 →
      ((p : ℕ) : ℤ) • redFun P = 0 := by
    intro P hP
    rw [← hredsmul p P hP, hP, hred0]
  -- Step 3c-ii-p: `p` is nonzero in the residue field, and the reduced
  -- curve has `p²` points of `p`-torsion over the (algebraically
  -- closed) residue field
  have hpresne : ((p : ℕ) : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) ≠ 0 := by
    have hqndvd : ¬ ((q : ℤ) ∣ ((p : ℕ) : ℤ)) := by
      intro hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp
        (Int.natCast_dvd_natCast.mp hdvd))
    have hu := (hIntUnitLoc ((p : ℕ) : ℤ) hqndvd).map
      (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))
    rw [map_intCast] at hu
    have hne := hu.ne_zero
    intro h0
    apply hne
    push_cast
    exact h0
  have hcardRes : Nat.card ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) =
      p ^ 2 :=
    TorsionCard.card_torsionBy (W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))) p hpresne
  -- Step 3c-ii-q: carrier collapses — the torsion carrier of the model
  -- over the completed closure is the double base change, and the
  -- reduced curve's torsion carrier is the reduced curve itself
  have hcupEq : (((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :
      WeierstrassCurve (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) =
      ((W.map (algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    show (W.map _).map _ = (W.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  have hidRes : (((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))))⁄(IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) :
      WeierstrassCurve (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) = W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  -- Step 3c-ii-r: the reduction as a homomorphism between the
  -- `p`-torsion modules
  set eup := WeierstrassCurve.Affine.Point.equivOfEq hcupEq with heupdef
  set edn := WeierstrassCurve.Affine.Point.equivOfEq hidRes with hedndef
  have hredE0 : ∀ x : ((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p),
      ((p : ℕ) : ℤ) • (edn.symm (redFun (eup x.1))) = 0 := by
    intro x
    have htor : ((p : ℕ) : ℤ) • (eup x.1) = 0 :=
      hmem eup x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2)
    have := hredtor (eup x.1) htor
    rw [← map_zsmul edn.symm, this, map_zero]
  set redE : ((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) →+
      ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    { toFun := fun x => ⟨edn.symm (redFun (eup x.1)),
        (Submodule.mem_torsionBy_iff _ _).mpr (hredE0 x)⟩
      map_zero' := by
        refine Subtype.ext ?_
        show edn.symm (redFun (eup 0)) = 0
        rw [map_zero eup, hred0, map_zero]
      map_add' := by
        intro x y
        refine Subtype.ext ?_
        show edn.symm (redFun (eup (x.1 + y.1))) =
          edn.symm (redFun (eup x.1)) + edn.symm (redFun (eup y.1))
        rw [map_add eup, hredAdd (eup x.1) (eup y.1)
          (hmem eup x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2))
          (hmem eup y.1 ((Submodule.mem_torsionBy_iff _ _).mp y.2)),
          map_add] } with hredEdef
  -- Step 3c-ii-s: the reduction is injective on `p`-torsion, hence a
  -- `ZMod p`-linear equivalence by the matching `p²` counts
  have hredEinj : Function.Injective redE := by
    intro x y hxy
    have h1 : edn.symm (redFun (eup x.1)) = edn.symm (redFun (eup y.1)) :=
      congrArg Subtype.val hxy
    have h2 : redFun (eup x.1) = redFun (eup y.1) := edn.symm.injective h1
    have h3 : eup x.1 = eup y.1 :=
      hredInj (eup x.1) (eup y.1)
        (hmem eup x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2))
        (hmem eup y.1 ((Submodule.mem_torsionBy_iff _ _).mp y.2)) h2
    exact Subtype.ext (eup.injective h3)
  have hredEbij : Function.Bijective redE := by
    haveI : Finite ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
      Nat.finite_of_card_ne_zero (by
        rw [hcardRes]
        positivity)
    refine (Nat.bijective_iff_injective_and_card redE).mpr ⟨hredEinj, ?_⟩
    rw [hcardV, hcardRes]
  set redEadd : ((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) ≃+
      ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    AddEquiv.ofBijective redE hredEbij with hredEadddef
  set redL : ((W.map (algebraMap ℤ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) ≃ₗ[ZMod p]
      ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) :=
    { redEadd with map_smul' := ZMod.map_smul redEadd.toAddMonoidHom }
    with hredLdef
  -- Step 3c-iii-a: `q` is not a unit of the completed integers (its
  -- valuation is strictly below one at the `q`-adic place)
  have hqNotUnit : ¬ IsUnit ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    have hints : (Valued.v).Integers (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) :=
      Valuation.valuationSubring.integers _
    intro hu
    have h1 := hints.isUnit_iff_valuation_eq_one.mp hu
    rw [map_natCast] at h1
    have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (K := ℚ) (v := hq.toHeightOneSpectrumRingOfIntegersRat)
      ((q : ℕ) : NumberField.RingOfIntegers ℚ)
    push_cast at h2
    rw [h2, show ((q : ℕ) : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
        ((q : ℕ) : NumberField.RingOfIntegers ℚ) from (map_natCast _ q).symm,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff] at h1
    apply h1
    rw [Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hq]
    rw [map_natCast]
  -- Step 3c-iii-b: `q` vanishes in the residue field of the local
  -- valuation subring (a unit inverse would descend through `h𝒪`)
  have hqZeroRes : ((q : ℕ) : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) = 0 := by
    by_contra h0
    -- the residue being nonzero makes `q` a unit of the local subring
    have huloc : IsUnit ((q : ℕ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      by_contra hnu
      apply h0
      have hmem : ((q : ℕ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ∈
          IsLocalRing.maximalIdeal (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [show ((q : ℕ) : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) =
        IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ((q : ℕ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))
        from (map_natCast _ q).symm]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    -- descend the inverse through the lying-over identity
    obtain ⟨u, hu⟩ := huloc
    have hinvv : (((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) =
        (((q : ℕ) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))))⁻¹ := by
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      have hmulO := u.mul_inv
      rw [hu] at hmulO
      have := congrArg (fun z : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (z : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) hmulO
      push_cast at this
      exact this
    have hqK : ((q : ℕ) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      (map_natCast _ q).symm
    have hinvmem2 : algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))⁻¹) ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) := by
      rw [map_inv₀, ← hqK, ← hinvv]
      exact Subtype.coe_prop _
    have hrange : (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))⁻¹) ∈
        (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).range := by
      have hcomap : (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))⁻¹) ∈
          ((localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat).comap (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).toSubring :=
        hinvmem2
      rw [h𝒪] at hcomap
      exact hcomap
    obtain ⟨y, hy⟩ := hrange
    apply hqNotUnit
    refine isUnit_iff_exists.mpr ⟨y, ?_, ?_⟩
    · apply Subtype.ext
      have hqKv : ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
      show (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) * (y : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1
      rw [show (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) by push_cast; rfl]
      rw [show ((y : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) y from rfl, hy]
      exact mul_inv_cancel₀ hqKv
    · apply Subtype.ext
      have hqKv : ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
      show (y : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) * (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1
      rw [show (((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) by push_cast; rfl]
      rw [show ((y : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) y from rfl, hy]
      exact inv_mul_cancel₀ hqKv
  -- the residue field has characteristic `q`
  haveI hCharRes : CharP (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) q := by
    have h := CharP.ringChar_of_prime_eq_zero hq hqZeroRes
    haveI := ringChar.charP (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))
    exact CharP.congr _ h
  -- Step 3c-iii-c: the residue field of the completed integers also has
  -- characteristic `q`
  have hqZeroKv : ((q : ℕ) : IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 0 := by
    rw [show ((q : ℕ) : IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) =
      IsLocalRing.residue (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ((q : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      from (map_natCast _ q).symm]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr hqNotUnit)
  haveI hCharKv : CharP (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) q := by
    have h := CharP.ringChar_of_prime_eq_zero hq hqZeroKv
    haveI := ringChar.charP (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    exact CharP.congr _ h
  -- Step 3c-iii-d: the residue field of the completed integers has `q`
  -- elements, hence is `ZMod q`
  have hcardKv : Nat.card (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = q := by
    have h1 := GaloisRepresentation.natCard_residue_quotient_toHeightOneSpectrum hq
    have hunder2 : ((IsLocalRing.maximalIdeal (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).under (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = IsLocalRing.maximalIdeal (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
        (IsLocalRing.maximalIdeal (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))))
    rw [hunder2] at h1
    exact h1
  have ebij : Function.Bijective
      (ZMod.castHom (dvd_refl q) (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    haveI : Finite (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardKv]; exact hq.ne_zero)
    refine (Nat.bijective_iff_injective_and_card _).mpr
      ⟨(ZMod.castHom (dvd_refl q)
        (IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).injective, ?_⟩
    rw [Nat.card_zmod, hcardKv]
  set eKv : ZMod q ≃+* IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) :=
    RingEquiv.ofBijective _ ebij with heKvdef
  -- Step 3c-iii-e: the inclusion of the completed integers into the
  -- local valuation subring, as a ring homomorphism
  set ov2ol : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+* (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) :=
    { toFun := fun a => ⟨algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)), by
        have hmem : (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) ∈ (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).range := ⟨a, rfl⟩
        rw [← h𝒪] at hmem
        exact hmem⟩
      map_one' := Subtype.ext (by
        show algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ((1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1
        rw [show ((1 : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1 from rfl, map_one])
      map_mul' := fun a b => Subtype.ext (by push_cast; ring)
      map_zero' := Subtype.ext (by
        show algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ((0 : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 0
        rw [show ((0 : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 0 from rfl, map_zero])
      map_add' := fun a b => Subtype.ext (by push_cast; ring) }
    with hov2oldef
  -- it kills the maximal ideal (nonzero residue would descend an
  -- inverse through the lying-over identity, as before)
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat),
      (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)).comp ov2ol a = 0 := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]
    by_contra h0
    have huloc : IsUnit (ov2ol a) := by
      by_contra hnu
      exact h0 ((Ideal.Quotient.eq_zero_iff_mem).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
    obtain ⟨u, hu⟩ := huloc
    have haK : ((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0 := by
      intro hz
      exact ha0 (Subtype.ext hz)
    have hinvv : (((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) =
        (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁻¹ := by
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      have hmulO := u.mul_inv
      rw [hu] at hmulO
      have := congrArg (fun z : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (z : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) hmulO
      push_cast at this
      exact this
    have hinvmem2 : algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁻¹) ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) := by
      rw [map_inv₀, ← hinvv]
      exact Subtype.coe_prop _
    have hrange : (((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁻¹) ∈ (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).range := by
      have hcomap : (((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁻¹) ∈
          ((localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat).comap (algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).toSubring := hinvmem2
      rw [h𝒪] at hcomap
      exact hcomap
    obtain ⟨y, hy⟩ := hrange
    have haunit : IsUnit a := by
      refine isUnit_iff_exists.mpr ⟨y, ?_, ?_⟩
      · apply Subtype.ext
        show ((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) * (y : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1
        rw [show ((y : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) y from rfl, hy]
        exact mul_inv_cancel₀ haK
      · apply Subtype.ext
        show (y : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) * ((a : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = 1
        rw [show ((y : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) y from rfl, hy]
        exact inv_mul_cancel₀ haK
    exact ((IsLocalRing.mem_maximalIdeal _).mp ha) haunit
  -- the induced map of residue fields, and the `ZMod q`-algebra
  set ρres : IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+* (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    Ideal.Quotient.lift _ ((IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)).comp ov2ol) hkill
    with hρresdef
  letI algZq : Algebra (ZMod q) (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (ρres.comp (eKv : ZMod q →+* IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).toAlgebra
  -- Step 3c-iii-f: the residue field is algebraic over `ZMod q` — every
  -- element is the residue of an integral element, whose monic
  -- annihilator descends through `𝔽_q = ZMod q`
  haveI halgZq : Algebra.IsAlgebraic (ZMod q) (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective (R := (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) x
    have hz : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ((w : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) := w.2
    obtain ⟨F, hFmonic, hFeval⟩ := hz
    refine ⟨(F.map (IsLocalRing.residue (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).map
      ((eKv.symm : IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+* ZMod q)), ?_, ?_⟩
    · exact ((hFmonic.map _).map _).ne_zero
    · -- the two double-map compositions collapse
      have hcomp1 : ((algebraMap (ZMod q) (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))).comp
          ((eKv.symm : IsLocalRing.ResidueField (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+* ZMod q))).comp
          (IsLocalRing.residue (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) =
          ρres.comp (IsLocalRing.residue (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) := by
        refine RingHom.ext fun a => ?_
        show ρres (eKv (eKv.symm (IsLocalRing.residue _ a))) = _
        rw [eKv.apply_symm_apply]
        rfl
      have hcomp2 : ρres.comp (IsLocalRing.residue (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) =
          (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)).comp ov2ol := by
        refine RingHom.ext fun a => ?_
        show Ideal.Quotient.lift _ _ hkill (Ideal.Quotient.mk _ a) = _
        rw [Ideal.Quotient.lift_mk]
      -- evaluate through the homomorphisms
      have hevalO : Polynomial.eval₂ ov2ol w F = 0 := by
        apply Subtype.coe_injective
        show ((localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat).subtype)
            (Polynomial.eval₂ ov2ol w F) =
          ((localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat).subtype) 0
        rw [Polynomial.hom_eval₂, map_zero]
        rw [show ((localValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat).subtype).comp ov2ol =
            algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) from RingHom.ext fun a => by
          rw [IsScalarTower.algebraMap_eq (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))]
          rfl]
        exact hFeval
      show Polynomial.aeval (IsLocalRing.residue _ w) _ = 0
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map,
        hcomp1, hcomp2, ← Polynomial.hom_eval₂, hevalO, map_zero]
  -- Step 3c-iii-g: the residue field is an algebraic closure of
  -- `ZMod q`; identify it with `AlgebraicClosure (ZMod q)`
  haveI hAlgClo : IsAlgClosure (ZMod q) (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    ⟨hACres, halgZq⟩
  set identA : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) ≃ₐ[ZMod q] (AlgebraicClosure (ZMod q)) :=
    IsAlgClosure.equiv (ZMod q) (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) (AlgebraicClosure (ZMod q)) with hidentAdef
  -- the identification as a `ℤ`-algebra homomorphism (the manual
  -- `commutes'` avoids the `ℤ`-algebra instance diamond)
  set identZ : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) →ₐ[ℤ] (AlgebraicClosure (ZMod q)) :=
    { toRingHom := identA.toAlgHom.toRingHom
      commutes' := fun n => by
        show identA.toAlgHom.toRingHom ((algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) n) = _
        rw [eq_intCast (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))), eq_intCast (algebraMap ℤ (AlgebraicClosure (ZMod q))),
          map_intCast] }
    with hidentZdef
  -- the transported point homomorphism (the model `W` is defined over
  -- `ℤ`)
  set imap : ((W⁄(IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) :
      WeierstrassCurve (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point →+
      ((W⁄(AlgebraicClosure (ZMod q))) : WeierstrassCurve (AlgebraicClosure (ZMod q))).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (S := ℤ)
      identZ with himapdef
  -- carrier collapses on both sides
  have hEq1 : (((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))))⁄(IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) :
      WeierstrassCurve (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) = (W⁄(IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    show (W.map _).map _ = W.map _
    rw [WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  have hEq2 : (((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))))⁄(AlgebraicClosure (ZMod q))) :
      WeierstrassCurve (AlgebraicClosure (ZMod q))) = (W⁄(AlgebraicClosure (ZMod q))) := by
    show ((W.map _).map _).map _ = W.map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    exact congrArg W.map (Subsingleton.elim _ _)
  -- membership: the composite carries `p`-torsion to `p`-torsion
  have hidmem : ∀ x : ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p),
      ((p : ℕ) : ℤ) • ((WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)
        (imap ((WeierstrassCurve.Affine.Point.equivOfEq hEq1) x.1))) = 0 := by
    intro x
    have h1 : ((p : ℕ) : ℤ) •
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1) x.1) = 0 :=
      hmem _ x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2)
    have h2 : ((p : ℕ) : ℤ) •
        (imap ((WeierstrassCurve.Affine.Point.equivOfEq hEq1) x.1)) = 0 := by
      rw [← map_zsmul imap, h1, map_zero]
    rw [← map_zsmul (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm),
      h2, map_zero]
  set ident₀ : ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) →+
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p) :=
    { toFun := fun x => ⟨(WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)
        (imap ((WeierstrassCurve.Affine.Point.equivOfEq hEq1) x.1)),
        (Submodule.mem_torsionBy_iff _ _).mpr (hidmem x)⟩
      map_zero' := Subtype.ext (by
        show (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)
          (imap ((WeierstrassCurve.Affine.Point.equivOfEq hEq1) 0)) = 0
        rw [map_zero, map_zero, map_zero])
      map_add' := fun x y => Subtype.ext (by
        show (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)
          (imap ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
            (x.1 + y.1))) = _
        rw [map_add, map_add, map_add]
        rfl) }
    with hident₀def
  have hidentinj : Function.Injective ident₀ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    have h2 := (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm).injective h1
    rw [himapdef] at h2
    have h3 := WeierstrassCurve.Affine.Point.map_injective
      (f := identZ) h2
    exact Subtype.ext ((WeierstrassCurve.Affine.Point.equivOfEq hEq1).injective h3)
  have hcardBar : Nat.card ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p) =
      p ^ 2 := by
    haveI : (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic :=
      inferInstance
    refine TorsionCard.card_torsionBy _ p ?_
    haveI : CharP (AlgebraicClosure (ZMod q)) q :=
      charP_of_injective_algebraMap
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
    exact CharP.cast_ne_zero_of_ne_of_prime (R := (AlgebraicClosure (ZMod q)))
      (Fact.out : p.Prime) hqp
  have hidentbij : Function.Bijective ident₀ := by
    haveI : Finite ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p) :=
      Nat.finite_of_card_ne_zero (by rw [hcardBar]; positivity)
    refine (Nat.bijective_iff_injective_and_card ident₀).mpr ⟨hidentinj, ?_⟩
    rw [hcardRes, hcardBar]
  set identL : ((W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).nTorsion p) ≃ₗ[ZMod p]
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion p) :=
    { AddEquiv.ofBijective ident₀ hidentbij with
      map_smul' := ZMod.map_smul (AddEquiv.ofBijective ident₀
        hidentbij).toAddMonoidHom }
    with hidentLdef
  -- Step 3c-iv: assemble the equivalence and reduce the node to the
  -- Frobenius-compatibility equation
  refine ⟨(((ψ₀.trans τ).trans redL).trans identL), ?_⟩
  -- Step 3c-v-a: the arithmetic Frobenius stabilizes the local
  -- valuation subring, and its residue action is the `q`-power map
  have hfrobmem : ∀ z : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), z ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) → (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) :=
    fun z hz => IsIntegral.map
      (((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom.restrictScalars (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) (hz : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) z)
  have hfrobres : ∀ (z : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) (hz : z ∈ (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)),
      IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨(Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z, hfrobmem z hz⟩ =
      (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨z, hz⟩) ^ q := by
    intro z hz
    have harith := Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob
      (v := hq.toHeightOneSpectrumRingOfIntegersRat)
    have hcardq :=
      GaloisRepresentation.natCard_residue_quotient_toHeightOneSpectrum hq
    have hc := harith (⟨z, hz⟩ : IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
    rw [hcardq] at hc
    -- name the congruence subject abstractly (its value is the
    -- Frobenius difference)
    obtain ⟨dic, hdicval, hdicmem⟩ : ∃ dic : IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)),
        (dic.1 = (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z - z ^ q) ∧
        dic ∈ IsLocalRing.maximalIdeal (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :=
      ⟨_, rfl, hc⟩
    have hdval : ((⟨(Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z, hfrobmem z hz⟩ - ⟨z, hz⟩ ^ q : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :
        (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z - z ^ q := by
      push_cast
      rfl
    -- the difference is not a unit of the local subring (same carrier
    -- as the integral closure)
    have hdnu : ¬ IsUnit (⟨(Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z, hfrobmem z hz⟩ - ⟨z, hz⟩ ^ q :
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      intro hu
      obtain ⟨u, hu'⟩ := hu
      have hicnu : ¬ IsUnit dic :=
        (IsLocalRing.mem_maximalIdeal _).mp hdicmem
      apply hicnu
      have hinvmem : (((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) ∈
          integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
        ((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)).2
      refine isUnit_iff_exists.mpr
        ⟨⟨((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)), hinvmem⟩, ?_, ?_⟩
      · apply Subtype.ext
        show dic.1 * (((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = 1
        rw [hdicval, ← hdval]
        have hmul := u.mul_inv
        rw [hu'] at hmul
        exact_mod_cast congrArg (fun w : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (w : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) hmul
      · apply Subtype.ext
        show (((u⁻¹ : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) * dic.1 = 1
        rw [hdicval, ← hdval]
        have hmul := u.inv_mul
        rw [hu'] at hmul
        exact_mod_cast congrArg (fun w : (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) => (w : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))) hmul
    -- hence the residues agree
    have hd0 : IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
        (⟨(Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z, hfrobmem z hz⟩ - ⟨z, hz⟩ ^ q) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hdnu)
    rw [map_sub, map_pow, sub_eq_zero] at hd0
    exact hd0
  -- Step 3c-v-b: the `q`-power Frobenius of the residue field as a
  -- `ℤ`-algebra homomorphism
  set frobZ : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) →ₐ[ℤ] (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    { toRingHom := frobenius (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) q
      commutes' := fun n => by
        show frobenius (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)) q ((algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))) n) = _
        rw [eq_intCast (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))), map_intCast] }
    with hfrobZdef
  -- proof-irrelevant congruence for reduced points (top-level copy)
  have hsome' : ∀ {xa xb ya yb : (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat))}
      {ha : (W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Nonsingular xa ya}
      {hb : (W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Nonsingular xb yb},
      xa = xb → ya = yb →
      (WeierstrassCurve.Affine.Point.some xa ya ha :
        (W.map (algebraMap ℤ (IsLocalRing.ResidueField
      (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)))).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some xb yb hb := by
    intro xa xb ya yb ha hb hxab hyab
    subst hxab
    subst hyab
    rfl
  -- Step 3c-v-c: the reduction map intertwines the arithmetic Frobenius
  -- with the `q`-power Frobenius
  have hredfrob : ∀ P : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point, ((p : ℕ) : ℤ) • P = 0 →
      redFun (WeierstrassCurve.Affine.Point.map
        (W' := W.map (algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) (S := (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
        ((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom P) =
      WeierstrassCurve.Affine.Point.map (W' := W) (S := ℤ) frobZ
        (redFun P) := by
    intro P hP
    cases P with
    | zero => rfl
    | some z w h =>
      have hz := habs h hP
      have hw := hord h hP
      -- torsion of the mapped point
      have hP' : ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.map
          (W' := W.map (algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) (S := (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
          ((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom
          (WeierstrassCurve.Affine.Point.some z w h)) = 0 := by
        rw [← map_zsmul, hP, map_zero]
      rw [WeierstrassCurve.Affine.Point.map_some] at hP' ⊢
      have hz' := habs _ hP'
      have hw' := hord _ hP'
      rw [hredSome ((WeierstrassCurve.Affine.baseChange_nonsingular
          (W := (W.map (algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine)
          (f := ((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom) ((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).injective z w).mpr h)
          hz' hw', hredSome h hz hw]
      refine hsome' ?_ ?_
      · show IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom z, hz'⟩ =
          frobZ (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨z, hz⟩)
        rw [show frobZ (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨z, hz⟩) =
          (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨z, hz⟩) ^ q from rfl]
        exact hfrobres z hz
      · show IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom w, hw'⟩ =
          frobZ (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨w, hw⟩)
        rw [show frobZ (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨w, hw⟩) =
          (IsLocalRing.residue (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat) ⟨w, hw⟩) ^ q from rfl]
        exact hfrobres w hw
  -- Step 3c-v-d: the chosen embedding of algebraic closures intertwines
  -- the global Frobenius with the arithmetic Frobenius (coordinatewise)
  have hlift : ∀ z : AlgebraicClosure ℚ,
      AlgebraicClosure.map (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) _ _
      (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat z) =
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure.map (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) _ _
      (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) z) := by
    intro z
    unfold GaloisRepresentation.globalFrob
    exact Field.absoluteGaloisGroup.lift_map (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) _ _
      (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) z
  -- Step 3c-v-e: assembly — destructure the torsion element, convert
  -- the Galois image pointwise, and compute both value chains
  intro x
  obtain ⟨P, hPmem⟩ := x
  have hPtor : ((p : ℕ) : ℤ) • P = 0 :=
    (Submodule.mem_torsionBy_iff _ _).mp hPmem
  cases P with
  | zero =>
    -- the zero-value computes through every layer
    refine Subtype.ext ?_
    have h1 : (E.galoisRep p hppos (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)
        ⟨WeierstrassCurve.Affine.Point.zero, hPmem⟩) =
        ⟨WeierstrassCurve.Affine.Point.zero, hPmem⟩ := Subtype.ext rfl
    rw [h1]
    show (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
          WeierstrassCurve.Affine.Point.zero))))))) =
      WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
        (frobAlgHom q)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
          WeierstrassCurve.Affine.Point.zero))))))))
    have h0 : (WeierstrassCurve.Affine.Point.zero : ((E.map (algebraMap ℚ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point) = 0 :=
      rfl
    rw [h0, map_zero hmodelPt, map_zero Pmap, map_zero eup, hred0,
      map_zero edn.symm,
      map_zero (WeierstrassCurve.Affine.Point.equivOfEq hEq1),
      map_zero imap,
      map_zero (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)]
    exact (map_zero (WeierstrassCurve.Affine.Point.map (W' := Wbar)
      (S := ZMod q) (frobAlgHom q))).symm
  | some a b hab =>
    -- convert the Galois image to its coordinatewise form
    obtain ⟨hns1, hm1, hgx⟩ : ∃ h' m',
        (E.galoisRep p hppos (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)
          ⟨WeierstrassCurve.Affine.Point.some a b hab, hPmem⟩) =
        ⟨WeierstrassCurve.Affine.Point.some
          (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat a)
          (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat b) h', m'⟩ :=
      ⟨_, _, Subtype.ext rfl⟩
    rw [hgx]
    refine Subtype.ext ?_
    -- both sides as value chains on literal points
    show (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
          (WeierstrassCurve.Affine.Point.some
            (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat a)
            (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat b) hns1)))))))) =
      WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
        (frobAlgHom q)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
          (WeierstrassCurve.Affine.Point.some a b hab)))))))))
    -- unfold the model identification and push both chains to the
    -- reduction layer
    have hmodelPtdef : hmodelPt = ((WeierstrassCurve.Affine.Point.equivOfEq
        (hid (E.map (algebraMap ℚ (AlgebraicClosure ℚ))))).trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))).symm.trans
        ((WeierstrassCurve.Affine.Point.equivOfEq hmapbar).trans
          (WeierstrassCurve.Affine.Point.equivOfEq
            (hid (W.map (algebraMap ℤ (AlgebraicClosure ℚ)))).symm)))) :=
      rfl
    have hevcsymm : ∀ (c d : AlgebraicClosure ℚ)
        (h : (E.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).toAffine.Nonsingular c d),
        (WeierstrassCurve.Affine.Point.equivVariableChange
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))).symm
          (WeierstrassCurve.Affine.Point.some c d h) =
        WeierstrassCurve.Affine.Point.mapVariableChangeFun
          ((C.map (algebraMap ℚ (AlgebraicClosure ℚ))) •
            (E.map (algebraMap ℚ (AlgebraicClosure ℚ))))
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹
          (WeierstrassCurve.Affine.Point.equivOfEq
            (inv_smul_smul (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))
              (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))).symm
            (WeierstrassCurve.Affine.Point.some c d h)) :=
      fun _ _ _ => rfl
    have heqsymm : ∀ {F : Type} [inst : Field F]
        {V V' : WeierstrassCurve F} (h : V = V'),
        (WeierstrassCurve.Affine.Point.equivOfEq h).symm =
        WeierstrassCurve.Affine.Point.equivOfEq h.symm := by
      intro F _ V V' h
      subst h
      rfl
    -- torsion of the mid-chain image, tracked to the literal point
    have hPtor2 : ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.some a b
        hab : ((E.map (algebraMap ℚ
          (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point) = 0 := hPtor
    have htor2 : ((p : ℕ) : ℤ) • (eup (Pmap (hmodelPt
        (WeierstrassCurve.Affine.Point.some a b hab)))) = 0 := by
      rw [← map_zsmul eup, ← map_zsmul Pmap, ← map_zsmul hmodelPt, hPtor2,
        map_zero, map_zero, map_zero]
    -- σ-fixedness of the inverse variable-change entries
    have hCinv : (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹ =
        (C⁻¹).map (algebraMap ℚ (AlgebraicClosure ℚ)) :=
      (map_inv (WeierstrassCurve.VariableChange.mapHom
        (algebraMap ℚ (AlgebraicClosure ℚ))) C).symm
    have hσfix : ∀ w : ℚ, (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) (algebraMap ℚ (AlgebraicClosure ℚ) w) =
        algebraMap ℚ (AlgebraicClosure ℚ) w := fun w => AlgEquiv.commutes _ w
    -- the embedded coordinates of the σ-image are the arithmetic
    -- Frobenius of the embedded coordinates
    have hbridge : ∀ z : (AlgebraicClosure ℚ), ιalg ((GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) z) = (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) (ιalg z) := by
      intro z
      have hAM : (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) =
          (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) _ _
            (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
              (NumberField.RingOfIntegers ℚ) ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) :=
        Subsingleton.elim _ _
      show AlgebraicClosure.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) ((GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) z) =
        (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) (AlgebraicClosure.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) z)
      rw [hAM]
      exact hlift z
    have hXc : ιalg (↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 2 * (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) a +
        (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.r) =
        (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) (ιalg (↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 2 * a +
        (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.r)) := by
      rw [← hbridge]
      refine congrArg ιalg ?_
      rw [hCinv]
      simp only [WeierstrassCurve.VariableChange.map_u,
        WeierstrassCurve.VariableChange.map_r, Units.coe_map,
        MonoidHom.coe_coe, map_add, map_mul, map_pow, hσfix]
    have hYc : ιalg (↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 3 * (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) b +
        ↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 2 *
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.s * (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) a +
        (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.t) =
        (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat) (ιalg (↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 3 * b +
        ↑(C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.u ^ 2 *
          (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.s * a +
        (C.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁻¹.t)) := by
      rw [← hbridge]
      refine congrArg ιalg ?_
      rw [hCinv]
      simp only [WeierstrassCurve.VariableChange.map_u,
        WeierstrassCurve.VariableChange.map_r,
        WeierstrassCurve.VariableChange.map_s,
        WeierstrassCurve.VariableChange.map_t, Units.coe_map,
        MonoidHom.coe_coe, map_add, map_mul, map_pow, hσfix]
    -- some-congruence at the completed-closure curve
    have hsomeCUP : ∀ {xa xb ya yb : (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))}
        {ha : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular xa ya} {hb : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Nonsingular xb yb},
        xa = xb → ya = yb →
        (WeierstrassCurve.Affine.Point.some xa ya ha : ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) =
          WeierstrassCurve.Affine.Point.some xb yb hb := by
      intro xa xb ya yb ha hb hxab hyab
      subst hxab
      subst hyab
      rfl
    -- destructure the two mid-chain values (they are finite points)
    rcases hch1 : eup (Pmap (hmodelPt (WeierstrassCurve.Affine.Point.some
        ((GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) a) ((GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) b) hns1))) with _ | ⟨X1, Y1, pf1⟩
    · exfalso
      simp only [hmodelPtdef, AddEquiv.trans_apply,
        WeierstrassCurve.Affine.Point.equivOfEq_some, hevcsymm,
        WeierstrassCurve.Affine.Point.mapVariableChangeFun_some,
        hPmapdef, heupdef, hedndef, himapdef, heqsymm,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        WeierstrassCurve.Affine.Point.map_some, reduceCtorEq] at hch1
    rcases hch2 : eup (Pmap (hmodelPt
        (WeierstrassCurve.Affine.Point.some a b hab))) with _ | ⟨X2, Y2, pf2⟩
    · exfalso
      simp only [hmodelPtdef, AddEquiv.trans_apply,
        WeierstrassCurve.Affine.Point.equivOfEq_some, hevcsymm,
        WeierstrassCurve.Affine.Point.mapVariableChangeFun_some,
        hPmapdef, heupdef, hedndef, himapdef, heqsymm,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        WeierstrassCurve.Affine.Point.map_some, reduceCtorEq] at hch2
    -- torsion of the plain mid-point
    rw [hch2] at htor2
    -- coordinate identifications from the normalized chain values
    simp only [hmodelPtdef, AddEquiv.trans_apply,
        WeierstrassCurve.Affine.Point.equivOfEq_some, hevcsymm,
        WeierstrassCurve.Affine.Point.mapVariableChangeFun_some,
        hPmapdef, heupdef, hedndef, himapdef, heqsymm,
        AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        WeierstrassCurve.Affine.Point.map_some] at hch1 hch2
    injection hch1 with hX1 hY1
    injection hch2 with hX2 hY2
    -- the σ-side point is the Frobenius image of the plain point
    have hswap : (WeierstrassCurve.Affine.Point.some X1 Y1 pf1 :
        ((W.map (algebraMap ℤ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point) = WeierstrassCurve.Affine.Point.map
        (W' := W.map (algebraMap ℤ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) (S := (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
        ((Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).toAlgHom
        (WeierstrassCurve.Affine.Point.some X2 Y2 pf2) := by
      refine hsomeCUP ?_ ?_
      · rw [← hX1, ← hX2]
        exact hXc
      · rw [← hY1, ← hY2]
        exact hYc
    rw [hswap, hredfrob _ htor2]
    rw [hredSome pf2 (habs pf2 htor2) (hord pf2 htor2)]
    -- push the residue-field Frobenius through the outer layers
    have hsomeFbar : ∀ {xa xb ya yb : (AlgebraicClosure (ZMod q))}
        {ha : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q))))⁄(AlgebraicClosure (ZMod q))).toAffine.Nonsingular xa ya} {hb : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q))))⁄(AlgebraicClosure (ZMod q))).toAffine.Nonsingular xb yb},
        xa = xb → ya = yb →
        (WeierstrassCurve.Affine.Point.some xa ya ha : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q))))⁄(AlgebraicClosure (ZMod q))).toAffine.Point) =
          WeierstrassCurve.Affine.Point.some xb yb hb := by
      intro xa xb ya yb ha hb hxab hyab
      subst hxab
      subst hyab
      rfl
    simp only [hedndef, himapdef, heqsymm,
      WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.map_some]
    refine hsomeFbar ?_ ?_
    · show identZ (frobenius _ q ((IsLocalRing.residue _) ⟨X2, _⟩)) =
        frobenius _ q (identZ ((IsLocalRing.residue _) ⟨X2, _⟩))
      rw [frobenius_def, frobenius_def, map_pow]
    · show identZ (frobenius _ q ((IsLocalRing.residue _) ⟨Y2, _⟩)) =
        frobenius _ q (identZ ((IsLocalRing.residue _) ⟨Y2, _⟩))
      rw [frobenius_def, frobenius_def, map_pow]


set_option maxHeartbeats 4000000 in
set_option warn.sorry false in
/-- **The `μ_p`-valued Weil pairing over a finite field** (sorry node —
the canonical arithmetic input): on the `p`-torsion of an elliptic
curve over `𝔽_q` (`p ≠ q`) there is a multiplicatively bilinear,
alternating, nondegenerate pairing valued in the `p`-th roots of unity
of `𝔽̄_q`, natural for the `q`-power Frobenius:
`e(Fx, Fy) = F(e(x, y))`. This is Silverman AEC III.8.1 together with
Galois-equivariance III.8.1(e) specialized to Frobenius. -/
theorem exists_weilPairing_mu (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hqp : q ≠ p) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) → ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) → (AlgebraicClosure (ZMod q))ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x, x ≠ 0 → ∃ y, e x y ≠ 1) ∧
      (∀ x y, (e x y) ^ p = 1) ∧
      (∀ x y, e (frobeniusTorsionEnd q Wbar p x)
          (frobeniusTorsionEnd q Wbar p y) =
        Units.map (frobAlgHom q).toRingHom.toMonoidHom (e x y)) := by
  classical
  -- ============================================================
  -- CONSTRUCTION PLAN (Silverman AEC III.8, divisor-theoretic):
  -- the coordinate ring of the base-changed curve is a Dedekind
  -- domain (N1, regularity from Δ ≠ 0 via the trace/norm integral-
  -- closure computation over k[X]); its class group carries the
  -- points (mathlib `Point.toClass`, injective); for a p-torsion
  -- point the p-th power of its point ideal is principal with a
  -- Miller generator f_P; the pairing is the evaluation ratio
  -- e(P,Q) = f_P(D_Q)/f_Q(D_P), well-defined and bilinear by Weil
  -- reciprocity (N5) with the infinite place handled by the degree
  -- bookkeeping of the norm form (N2); alternation, nondegeneracy
  -- and Frobenius naturality follow from the construction.
  -- ============================================================
  -- N1: the coordinate ring of the base-changed curve is Dedekind
  set Wb : WeierstrassCurve (AlgebraicClosure (ZMod q)) :=
    Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) with hWbdef
  -- the conjugation of the coordinate ring over `k[X]`: the quadratic
  -- `Y² + A·Y − G` has second root `−A − Y`
  have hPeq0 : Wb.toAffine.polynomial = Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C Wb.a₁ * Polynomial.X +
        Polynomial.C Wb.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 +
        Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) := rfl
  have hrel2 : (AdjoinRoot.root Wb.toAffine.polynomial) ^ 2 +
      AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) *
        AdjoinRoot.root Wb.toAffine.polynomial -
      AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
          Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) = 0 := by
    show (AdjoinRoot.mk Wb.toAffine.polynomial Polynomial.X) ^ 2 +
      AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.C (Polynomial.C Wb.a₁ * Polynomial.X +
          Polynomial.C Wb.a₃)) *
        AdjoinRoot.mk Wb.toAffine.polynomial Polynomial.X -
      AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.C (Polynomial.X ^ 3 +
          Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
          Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) = 0
    rw [← map_pow, ← map_mul, ← map_add, ← map_sub, ← hPeq0]
    exact AdjoinRoot.mk_self
  have hconjrel : Wb.toAffine.polynomial.eval₂
      (Algebra.ofId (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing)
      (- (AdjoinRoot.of Wb.toAffine.polynomial
          (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) -
        AdjoinRoot.root Wb.toAffine.polynomial) = 0 := by
    show Polynomial.aeval (- (AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) -
        AdjoinRoot.root Wb.toAffine.polynomial) Wb.toAffine.polynomial = 0
    suffices h : Polynomial.aeval (- (AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) -
        AdjoinRoot.root Wb.toAffine.polynomial)
        (Polynomial.X ^ 2 +
          Polynomial.C (Polynomial.C Wb.a₁ * Polynomial.X +
            Polynomial.C Wb.a₃) * Polynomial.X -
          Polynomial.C (Polynomial.X ^ 3 +
            Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
            Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) = 0 by
      rwa [← hPeq0] at h
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, AdjoinRoot.algebraMap_eq]
    simp only [map_add, map_mul, map_pow] at hrel2 ⊢
    linear_combination hrel2
  set conj : Wb.toAffine.CoordinateRing →ₐ[Polynomial (AlgebraicClosure (ZMod q))]
      Wb.toAffine.CoordinateRing :=
    AdjoinRoot.liftAlgHom Wb.toAffine.polynomial
      (Algebra.ofId (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing)
      (- (AdjoinRoot.of Wb.toAffine.polynomial
          (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) -
        AdjoinRoot.root Wb.toAffine.polynomial) hconjrel with hconjdef
  -- the conjugation fixes the base and sends the root to the second root
  have hconj_root : conj (AdjoinRoot.root Wb.toAffine.polynomial) =
      - (AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) -
      AdjoinRoot.root Wb.toAffine.polynomial := by
    rw [hconjdef]
    exact AdjoinRoot.lift_root hconjrel
  have hconj_of : ∀ z : Polynomial (AlgebraicClosure (ZMod q)),
      conj (AdjoinRoot.of Wb.toAffine.polynomial z) =
      AdjoinRoot.of Wb.toAffine.polynomial z := fun z =>
    conj.commutes z
  -- every element decomposes over the power basis `{1, Y}`
  have hdecomp : ∀ z : Wb.toAffine.CoordinateRing, ∃ pq :
      Polynomial (AlgebraicClosure (ZMod q)) × Polynomial (AlgebraicClosure (ZMod q)),
      z = AdjoinRoot.of Wb.toAffine.polynomial pq.1 +
        AdjoinRoot.of Wb.toAffine.polynomial pq.2 *
          AdjoinRoot.root Wb.toAffine.polynomial := by
    intro z
    have hsum := (WeierstrassCurve.Affine.CoordinateRing.basis
      Wb.toAffine).sum_repr z
    rw [Fin.sum_univ_two] at hsum
    rw [WeierstrassCurve.Affine.CoordinateRing.basis_apply,
      WeierstrassCurve.Affine.CoordinateRing.basis_apply,
      show (AdjoinRoot.powerBasis' (
        WeierstrassCurve.Affine.monic_polynomial)).gen =
        AdjoinRoot.root Wb.toAffine.polynomial from rfl] at hsum
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      Algebra.smul_def, AdjoinRoot.algebraMap_eq, mul_one] at hsum
    exact ⟨⟨(WeierstrassCurve.Affine.CoordinateRing.basis
        Wb.toAffine).repr z 0,
      (WeierstrassCurve.Affine.CoordinateRing.basis Wb.toAffine).repr z 1⟩,
      hsum.symm⟩
  -- the norm `z · conj z` lands in the base
  have hnorm : ∀ z : Wb.toAffine.CoordinateRing, ∃ n : Polynomial (AlgebraicClosure (ZMod q)),
      z * conj z = AdjoinRoot.of Wb.toAffine.polynomial n := by
    intro z
    obtain ⟨⟨pp, qq⟩, hz⟩ := hdecomp z
    refine ⟨pp ^ 2 - pp * qq * (Polynomial.C Wb.a₁ * Polynomial.X +
        Polynomial.C Wb.a₃) - qq ^ 2 * (Polynomial.X ^ 3 +
        Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆), ?_⟩
    rw [hz]
    rw [map_add, map_mul, hconj_of, hconj_of, hconj_root]
    simp only [map_sub, map_pow, map_mul, map_add]
    simp only [map_add, map_mul, map_pow] at hrel2
    linear_combination (-(AdjoinRoot.of Wb.toAffine.polynomial qq ^ 2)) *
      hrel2
  haveI hDD : IsDedekindDomain Wb.toAffine.CoordinateRing := by
    -- Krull–Akizuki frame: the coordinate ring is the integral closure
    -- of `k[X]` (a PID) in the function field, which is a finite
    -- separable quadratic extension of `k(X)`
    haveI : FaithfulSMul (Polynomial (AlgebraicClosure (ZMod q)))
        (FractionRing Wb.toAffine.CoordinateRing) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      have h1 : Function.Injective (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing) :=
        AdjoinRoot.of.injective_of_degree_ne_zero (by
          rw [WeierstrassCurve.Affine.degree_polynomial]
          norm_num)
      rw [IsScalarTower.algebraMap_eq (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing)]
      exact (IsFractionRing.injective Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)).comp h1
    letI : Algebra (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
        (FractionRing Wb.toAffine.CoordinateRing) :=
      FractionRing.liftAlgebra _ _
    have hspan : Submodule.span (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
        ({1, algebraMap Wb.toAffine.CoordinateRing
          (FractionRing Wb.toAffine.CoordinateRing)
          (AdjoinRoot.root Wb.toAffine.polynomial)} :
          Set (FractionRing Wb.toAffine.CoordinateRing)) = ⊤ := by
      -- the images of `1` and the root span the fraction field over
      -- `k(X)`: clear denominators with the conjugate norm
      have hofinj : Function.Injective
          (AdjoinRoot.of Wb.toAffine.polynomial) :=
        AdjoinRoot.of.injective_of_degree_ne_zero (by
          rw [WeierstrassCurve.Affine.degree_polynomial]
          norm_num)
      have hconj_conj : ∀ z : Wb.toAffine.CoordinateRing,
          conj (conj z) = z := by
        intro z
        obtain ⟨⟨pp, qq⟩, rfl⟩ := hdecomp z
        rw [map_add, map_mul, hconj_of, hconj_of, hconj_root, map_add,
          map_mul, hconj_of, hconj_of, map_sub, map_neg, hconj_of,
          hconj_root]
        ring
      have hconjinj : Function.Injective conj := fun a b hab => by
        have := congrArg conj hab
        rwa [hconj_conj, hconj_conj] at this
      rw [eq_top_iff]
      intro ξ _
      obtain ⟨c, d, hd, hξ⟩ := IsFractionRing.div_surjective
        (A := Wb.toAffine.CoordinateRing) ξ
      have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
      have hcd0 : conj d ≠ 0 := fun h =>
        hd0 (hconjinj (h.trans (map_zero conj).symm))
      obtain ⟨n, hn⟩ := hnorm d
      have hn0 : n ≠ 0 := by
        intro h0
        have h1 := hn
        rw [h0, map_zero] at h1
        exact (mul_ne_zero hd0 hcd0) h1
      obtain ⟨⟨p', q'⟩, hcd⟩ := hdecomp (c * conj d)
      -- rewrite the fraction with denominator `of n`
      have hξ2 : ξ = algebraMap Wb.toAffine.CoordinateRing
          (FractionRing Wb.toAffine.CoordinateRing) (c * conj d) /
          algebraMap Wb.toAffine.CoordinateRing
          (FractionRing Wb.toAffine.CoordinateRing)
          (AdjoinRoot.of Wb.toAffine.polynomial n) := by
        rw [← hn, ← hξ]
        rw [map_mul, map_mul]
        rw [div_mul_eq_div_div_swap]
        congr 1
        rw [mul_div_assoc, div_self (fun h => hcd0
          ((IsFractionRing.injective Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing))
            (h.trans (map_zero (algebraMap Wb.toAffine.CoordinateRing
              (FractionRing Wb.toAffine.CoordinateRing))).symm))),
          mul_one]
      -- distribute and read off the span membership
      rw [hξ2, hcd, map_add, map_mul, add_div]
      refine Submodule.add_mem _ ?_ ?_
      · have hpiece : algebraMap Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing)
            (AdjoinRoot.of Wb.toAffine.polynomial p') /
            algebraMap Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing)
            (AdjoinRoot.of Wb.toAffine.polynomial n) =
            (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
              (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) p' /
            algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
              (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) n) •
            (1 : FractionRing Wb.toAffine.CoordinateRing) := by
          rw [Algebra.smul_def, mul_one, map_div₀]
          rw [← IsScalarTower.algebraMap_apply,
            ← IsScalarTower.algebraMap_apply]
          rfl
        rw [hpiece]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · have hpiece : algebraMap Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing)
            (AdjoinRoot.of Wb.toAffine.polynomial q') *
            algebraMap Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing)
            (AdjoinRoot.root Wb.toAffine.polynomial) /
            algebraMap Wb.toAffine.CoordinateRing
            (FractionRing Wb.toAffine.CoordinateRing)
            (AdjoinRoot.of Wb.toAffine.polynomial n) =
            (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
              (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) q' /
            algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
              (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) n) •
            (algebraMap Wb.toAffine.CoordinateRing
              (FractionRing Wb.toAffine.CoordinateRing)
              (AdjoinRoot.root Wb.toAffine.polynomial)) := by
          rw [Algebra.smul_def, map_div₀]
          rw [← IsScalarTower.algebraMap_apply,
            ← IsScalarTower.algebraMap_apply]
          rw [mul_div_right_comm]
          rfl
        rw [hpiece]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    haveI hfd : FiniteDimensional (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
        (FractionRing Wb.toAffine.CoordinateRing) := by
      refine ⟨⟨{1, algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)}, ?_⟩⟩
      rw [show (↑({1, algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)} :
        Finset (FractionRing Wb.toAffine.CoordinateRing)) :
        Set (FractionRing Wb.toAffine.CoordinateRing)) =
        ({1, algebraMap Wb.toAffine.CoordinateRing
          (FractionRing Wb.toAffine.CoordinateRing)
          (AdjoinRoot.root Wb.toAffine.polynomial)} :
          Set (FractionRing Wb.toAffine.CoordinateRing)) by simp]
      exact hspan
    haveI hsep : Algebra.IsSeparable (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
        (FractionRing Wb.toAffine.CoordinateRing) := by
      -- the quadratic over `k(X)` annihilating the root image
      set A' : (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) := algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)
        with hA'def
      set G' : (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) := algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)
        with hG'def
      set Qpoly : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) := Polynomial.X ^ 2 +
        Polynomial.C A' * Polynomial.X - Polynomial.C G' with hQdef
      -- the root image satisfies it
      have hrootL : Polynomial.aeval (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) Qpoly = 0 := by
        rw [hQdef]
        simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
          Polynomial.aeval_C]
        have := congrArg (algebraMap Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing)) hrel2
        simp only [map_add, map_sub, map_mul, map_pow, map_zero] at this
        rw [hA'def, hG'def]
        simp only [map_add, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing),
          IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
            Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing),
          AdjoinRoot.algebraMap_eq]
        linear_combination this
      -- the quadratic is separable
      have hQsep : Qpoly.Separable := by
        have hderiv : Polynomial.derivative Qpoly =
            Polynomial.C 2 * Polynomial.X + Polynomial.C A' := by
          rw [hQdef]
          simp only [Polynomial.derivative_sub, Polynomial.derivative_add,
            Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
            Polynomial.derivative_X, Polynomial.derivative_C,
            Nat.cast_ofNat, mul_one, sub_zero]
          ring
        by_cases hq2 : (q : ℕ) = 2
        · -- characteristic two: the derivative is the unit constant `A'`
          haveI hchar2 : CharP (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) 2 := by
            haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
              charP_of_injective_algebraMap
                (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
            haveI h2 : CharP (Polynomial (AlgebraicClosure (ZMod q))) q :=
              charP_of_injective_algebraMap
                (Polynomial.C_injective) q
            haveI h3 : CharP (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) q :=
              charP_of_injective_algebraMap
                (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) q
            exact CharP.congr q hq2
          have h20 : (2 : (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = 0 := by
            exact_mod_cast CharP.cast_eq_zero (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) 2
          have hA'ne : A' ≠ 0 := by
            rw [hA'def]
            intro h0
            have hApoly0 : (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) = (0 : Polynomial (AlgebraicClosure (ZMod q))) :=
              (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))))
                (h0.trans (map_zero _).symm)
            -- then `a₁ = a₃ = 0`, forcing `Δ = 0` in characteristic two
            have ha1 : Wb.a₁ = 0 := by
              have := congrArg (fun f => Polynomial.coeff f 1) hApoly0
              simpa using this
            have ha3 : Wb.a₃ = 0 := by
              have := congrArg (fun f => Polynomial.coeff f 0) hApoly0
              simpa using this
            have hq2F : (2 : (AlgebraicClosure (ZMod q))) = 0 := by
              haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                charP_of_injective_algebraMap
                  (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
              haveI h2 : CharP (AlgebraicClosure (ZMod q)) 2 := CharP.congr q hq2
              exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod q)) 2
            have hΔ0 : Wb.Δ = 0 := by
              rw [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
                WeierstrassCurve.b₄, WeierstrassCurve.b₆,
                WeierstrassCurve.b₈, ha1, ha3]
              linear_combination (8 * Wb.a₂ ^ 2 * Wb.a₄ ^ 2 -
                32 * Wb.a₂ ^ 3 * Wb.a₆ - 32 * Wb.a₄ ^ 3 +
                144 * Wb.a₂ * Wb.a₄ * Wb.a₆ - 216 * Wb.a₆ ^ 2) * hq2F
            haveI : Wb.IsElliptic := by
              rw [hWbdef]
              infer_instance
            exact (WeierstrassCurve.isElliptic_iff Wb).mp
              (by infer_instance) |>.ne_zero hΔ0
          rw [Polynomial.separable_def, hderiv]
          rw [show Polynomial.C (2 : (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = 0 by rw [h20, map_zero],
            zero_mul, zero_add]
          refine ⟨0, Polynomial.C A'⁻¹, ?_⟩
          rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hA'ne,
            map_one]
        · -- characteristic away from two: explicit Bézout certificate
          have h2F : (2 : (AlgebraicClosure (ZMod q))) ≠ 0 := by
            haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
              charP_of_injective_algebraMap
                (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
            exact CharP.cast_ne_zero_of_ne_of_prime (R := (AlgebraicClosure (ZMod q)))
              Nat.prime_two (fun h => hq2 h)
          have hD'ne : A' ^ 2 + 4 * G' ≠ 0 := by
            rw [hA'def, hG'def, ← map_pow, ← map_ofNat
              (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) 4, ← map_mul, ← map_add]
            intro h0
            have hpoly0 : (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 + 4 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) = (0 : Polynomial (AlgebraicClosure (ZMod q))) :=
              (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))))
                (h0.trans (map_zero _).symm)
            -- the cubic coefficient is `4 ≠ 0`
            have hc3 := congrArg (fun f => Polynomial.coeff f 3) hpoly0
            simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
              Polynomial.coeff_zero, Polynomial.coeff_X_pow,
              Polynomial.coeff_C_mul, Polynomial.coeff_C,
              Polynomial.coeff_X] at hc3
            have hA2deg : (((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) : Polynomial (AlgebraicClosure (ZMod q))) ^ 2).coeff 3 = 0 := by
              refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
              have h1 : ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) : Polynomial (AlgebraicClosure (ZMod q))).natDegree ≤ 1 := by
                refine le_trans (Polynomial.natDegree_add_le _ _)
                  (max_le ?_ ?_)
                · exact le_trans Polynomial.natDegree_mul_le (by simp)
                · simp
              have h2 := Polynomial.natDegree_pow_le
                (p := ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) : Polynomial (AlgebraicClosure (ZMod q)))) (n := 2)
              omega
            rw [hA2deg] at hc3
            norm_num at hc3
            exact (mul_ne_zero h2F h2F) (by
              have h4 : (4 : (AlgebraicClosure (ZMod q))) = 2 * 2 := by norm_num
              rw [← h4]
              exact_mod_cast hc3)
          rw [Polynomial.separable_def, hderiv]
          refine ⟨Polynomial.C (-(4 * (A' ^ 2 + 4 * G')⁻¹)),
            Polynomial.C ((A' ^ 2 + 4 * G')⁻¹) *
              (Polynomial.C 2 * Polynomial.X + Polynomial.C A'), ?_⟩
          rw [hQdef]
          have hDinv : (A' ^ 2 + 4 * G') * (A' ^ 2 + 4 * G')⁻¹ = 1 :=
            mul_inv_cancel₀ hD'ne
          have hDinvC := congrArg (Polynomial.C :
            (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) → Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) hDinv
          simp only [map_mul, map_add, map_pow, map_one, map_ofNat] at hDinvC
          simp only [map_neg, map_mul, map_ofNat]
          linear_combination hDinvC
      -- the root image is separable, and it generates the field
      have hryint : IsIntegral (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) :=
        Algebra.IsIntegral.isIntegral _
      have hrysep : IsSeparable (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) :=
        hQsep.of_dvd (minpoly.dvd _ _ hrootL)
      have hadj : IntermediateField.adjoin (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) {((algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) : (FractionRing Wb.toAffine.CoordinateRing))} = ⊤ := by
        rw [eq_top_iff]
        intro ξ _
        have h1 : Submodule.span (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
            ({1, (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial))} : Set (FractionRing Wb.toAffine.CoordinateRing)) ≤
            Subalgebra.toSubmodule
              (IntermediateField.adjoin (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                {((algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) : (FractionRing Wb.toAffine.CoordinateRing))}).toSubalgebra := by
          rw [Submodule.span_le]
          rintro z hz
          rcases hz with rfl | hz
          · exact (IntermediateField.adjoin _ _).one_mem
          · rw [Set.mem_singleton_iff] at hz
            subst hz
            exact IntermediateField.mem_adjoin_simple_self _ _
        exact h1 (by rw [hspan]; exact Submodule.mem_top)
      haveI hadjsep : Algebra.IsSeparable (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
          (IntermediateField.adjoin (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) {((algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) : (FractionRing Wb.toAffine.CoordinateRing))}) :=
        (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
          _ _).mpr hrysep
      exact Algebra.IsSeparable.of_algHom _ _
        ((IntermediateField.equivOfEq hadj.symm).toAlgHom.comp
          IntermediateField.topEquiv.symm.toAlgHom)
    haveI hic : IsIntegralClosure Wb.toAffine.CoordinateRing
        (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing Wb.toAffine.CoordinateRing) := by
      haveI hfinC : Module.Finite (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing :=
        Module.Finite.of_basis
          (WeierstrassCurve.Affine.CoordinateRing.basis Wb.toAffine)
      refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨?_, ?_⟩⟩
      · -- the hard direction: an integral element of the function field
        -- lies in the coordinate ring (normality)
        intro hx
        -- decompose over the spanning set
        have hxmem : x ∈ Submodule.span (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) ({1, (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial))} : Set (FractionRing Wb.toAffine.CoordinateRing)) := by
          rw [hspan]
          exact Submodule.mem_top
        obtain ⟨sc, tc, hst⟩ := Submodule.mem_span_pair.mp hxmem
        -- the element-level root relation over `L`
        have hryel : (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) ^ 2 +
            algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing) (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
              (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * (algebraMap Wb.toAffine.CoordinateRing
        (FractionRing Wb.toAffine.CoordinateRing)
        (AdjoinRoot.root Wb.toAffine.polynomial)) -
            algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing) (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
              (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) = 0 := by
          have := congrArg (algebraMap Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing)) hrel2
          simp only [map_add, map_sub, map_mul, map_pow, map_zero,
            ← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing),
            IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
              Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing),
            AdjoinRoot.algebraMap_eq] at this ⊢
          linear_combination this
        -- the monic quadratic relation satisfied by `x`
        have hxquad : x ^ 2 -
            algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing) (2 * sc - tc *
              algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * x +
            algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing) (sc ^ 2 - sc * tc *
              algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) - tc ^ 2 *
              algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) = 0 := by
          rw [← hst]
          simp only [Algebra.smul_def, mul_one, map_sub, map_add, map_mul,
            map_pow, map_ofNat,
            ← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing),
            IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
              Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing),
            AdjoinRoot.algebraMap_eq]
          simp only [map_add, map_mul, map_pow,
            ← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing),
            IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
              Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing),
            AdjoinRoot.algebraMap_eq] at hryel
          linear_combination (algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing) tc) ^ 2 * hryel
        -- the annihilating quadratic over `k(X)` and the minimal
        -- polynomial's integral coefficients
        set τ : (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) := 2 * sc - tc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) with hτdef
        set ν : (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) := sc ^ 2 - sc * tc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) - tc ^ 2 * (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) with hνdef
        have hxK : IsIntegral (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x := hx.tower_top
        have hxaeval : Polynomial.aeval x (Polynomial.X ^ 2 -
            Polynomial.C τ * Polynomial.X + Polynomial.C ν) = 0 := by
          simp only [map_add, map_sub, map_mul, map_pow,
            Polynomial.aeval_X, Polynomial.aeval_C]
          exact hxquad
        have hdvd : minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x ∣ (Polynomial.X ^ 2 -
            Polynomial.C τ * Polynomial.X + Polynomial.C ν) :=
          minpoly.dvd _ _ hxaeval
        have hcoeffs : ∀ n, (minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).coeff n ∈
            (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).range := by
          intro n
          rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) hx,
            Polynomial.coeff_map]
          exact ⟨_, rfl⟩
        -- the annihilating quadratic is monic of degree two
        have hqmonic : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
            Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).Monic := by
          rw [show (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
            Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = Polynomial.X ^ 2 -
            (Polynomial.C τ * Polynomial.X - Polynomial.C ν) from by ring]
          refine Polynomial.monic_X_pow_sub ?_
          rw [sub_eq_add_neg, ← Polynomial.C_neg]
          refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
          norm_num
        have hqdeg : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
            Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).natDegree = 2 := by
          have h1 : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
              Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).natDegree ≤ 2 := by
            refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
            · refine le_trans (Polynomial.natDegree_sub_le _ _)
                (max_le ?_ ?_)
              · simp
              · refine le_trans Polynomial.natDegree_mul_le ?_
                simp
            · simp
          have h2 : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
              Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).coeff 2 ≠ 0 := by
            simp [Polynomial.coeff_add, Polynomial.coeff_sub]
          exact le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero h2)
        -- degree dichotomy for the minimal polynomial
        have hd1 : 1 ≤ (minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).natDegree := minpoly.natDegree_pos hxK
        have hd2 : (minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).natDegree ≤ 2 := by
          have := Polynomial.natDegree_le_of_dvd hdvd hqmonic.ne_zero
          omega
        have hmono := minpoly.monic hxK
        rcases (show (minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).natDegree = 1 ∨
            (minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).natDegree = 2 by omega) with hdeg | hdeg
        · -- linear case: `x` lies in `k(X)` and is integral, so it is
          -- the image of a polynomial
          have hlin := hmono.eq_X_add_C hdeg
          have haev := minpoly.aeval (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x
          rw [hlin] at haev
          simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haev
          obtain ⟨c₀, hc₀⟩ := hcoeffs 0
          have hxval : x = algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing)
              (- ((minpoly (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) x).coeff 0)) := by
            rw [map_neg]
            exact eq_neg_of_add_eq_zero_left haev
          refine ⟨AdjoinRoot.of Wb.toAffine.polynomial (-c₀), ?_⟩
          rw [hxval, ← hc₀, ← map_neg (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))))
            c₀, ← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
            (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing), IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
            Wb.toAffine.CoordinateRing (FractionRing Wb.toAffine.CoordinateRing), AdjoinRoot.algebraMap_eq]
        · -- quadratic case: the minimal polynomial IS the quadratic
          obtain ⟨u, hu⟩ := hdvd
          have hune0 : u ≠ 0 := by
            intro h0
            rw [h0, mul_zero] at hu
            exact hqmonic.ne_zero hu
          have hudeg : u.natDegree = 0 := by
            have := Polynomial.natDegree_mul (minpoly.ne_zero hxK) hune0
            rw [← hu, hqdeg, hdeg] at this
            omega
          have humonic : u.Monic := by
            have hlead := congrArg Polynomial.leadingCoeff hu
            rw [Polynomial.leadingCoeff_mul, hqmonic.leadingCoeff,
              hmono.leadingCoeff, one_mul] at hlead
            exact hlead.symm
          have hu1 : u = 1 := humonic.natDegree_eq_zero.mp hudeg
          rw [hu1, mul_one] at hu
          -- extract the coefficients
          have hτmem : τ ∈ (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).range := by
            have h1 := hcoeffs 1
            rw [← hu] at h1
            have hc1 : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
                Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).coeff 1 = -τ := by
              simp [Polynomial.coeff_add, Polynomial.coeff_sub]
            rw [hc1] at h1
            obtain ⟨w, hw⟩ := h1
            exact ⟨-w, by rw [map_neg, hw, neg_neg]⟩
          have hνmem : ν ∈ (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).range := by
            have h0 := hcoeffs 0
            rw [← hu] at h0
            have hc0 : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X +
                Polynomial.C ν : Polynomial (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))).coeff 0 = ν := by
              simp [Polynomial.coeff_add, Polynomial.coeff_sub]
            rw [hc0] at h0
            exact h0
          -- the discriminant identity: `τ² − 4ν = tc² · (A² + 4G)`
          obtain ⟨τ₀, hτ₀⟩ := hτmem
          obtain ⟨ν₀, hν₀⟩ := hνmem
          have hkey : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
              (τ₀ ^ 2 - 4 * ν₀) = tc ^ 2 *
              algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 + 4 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) := by
            rw [map_sub, map_pow, map_mul, hτ₀, hν₀, hτdef, hνdef]
            simp only [map_add, map_pow, map_mul, map_ofNat]
            ring
          by_cases hq2 : (q : ℕ) = 2
          · -- characteristic-two branch
            haveI hchar2K : CharP (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) 2 := by
              haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                charP_of_injective_algebraMap
                  (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
              haveI h2 : CharP (Polynomial (AlgebraicClosure (ZMod q))) q :=
                charP_of_injective_algebraMap Polynomial.C_injective q
              haveI h3 : CharP (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) q :=
                charP_of_injective_algebraMap
                  (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) q
              exact CharP.congr q hq2
            have h2K : (2 : (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = 0 := by
              exact_mod_cast CharP.cast_eq_zero (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) 2
            -- in characteristic two the discriminant identity collapses
            -- to `τ₀ = tc · A` (fully decomposed atoms)
            have hτtcA : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ =
                tc * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) := by
              have h4K : (4 : (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = 0 := by
                have h44 : (4 : (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) = 2 * 2 := by norm_num
                rw [h44, h2K, mul_zero]
              have hk := hkey
              simp only [map_sub, map_add, map_mul, map_pow,
                map_ofNat] at hk
              have hsq : (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ -
                  tc * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) ^ 2 =
                  0 := by
                simp only [map_add, map_mul]
                linear_combination hk +
                  (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) ν₀ + tc ^ 2 *
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 3 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₂) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 2 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₄) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₆))) * h4K +
                  (tc ^ 2 * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₁) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₃)) ^ 2 -
                  algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ * tc *
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₁) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                      (Polynomial.C Wb.a₃))) * h2K
              have h0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
              exact sub_eq_zero.mp h0
            -- `tc` is a polynomial image (easy when `a₁ = 0`; the
            -- singular-point contradiction otherwise)
            have htcrange : ∃ t₀ : Polynomial (AlgebraicClosure (ZMod q)), tc =
                algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) t₀ := by
              by_cases ha1 : Wb.a₁ = 0
              · -- `A` is the nonzero constant `a₃`
                have ha3 : Wb.a₃ ≠ 0 := by
                  intro ha3
                  have hq2F : (2 : (AlgebraicClosure (ZMod q))) = 0 := by
                    haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                      charP_of_injective_algebraMap
                        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
                    haveI h2 : CharP (AlgebraicClosure (ZMod q)) 2 := CharP.congr q hq2
                    exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod q)) 2
                  have hΔ0 : Wb.Δ = 0 := by
                    rw [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
                      WeierstrassCurve.b₄, WeierstrassCurve.b₆,
                      WeierstrassCurve.b₈, ha1, ha3]
                    linear_combination (8 * Wb.a₂ ^ 2 * Wb.a₄ ^ 2 -
                      32 * Wb.a₂ ^ 3 * Wb.a₆ - 32 * Wb.a₄ ^ 3 +
                      144 * Wb.a₂ * Wb.a₄ * Wb.a₆ - 216 * Wb.a₆ ^ 2) *
                      hq2F
                  haveI : Wb.IsElliptic := by
                    rw [hWbdef]; infer_instance
                  exact ((WeierstrassCurve.isElliptic_iff Wb).mp
                    inferInstance).ne_zero hΔ0
                refine ⟨τ₀ * Polynomial.C (Wb.a₃⁻¹ * Wb.a₁ * 0 + Wb.a₃⁻¹),
                  ?_⟩
                have hAconst : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                    (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) = algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                    (Polynomial.C Wb.a₃) := by
                  rw [ha1]
                  norm_num
                have hA3ne : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                    (Polynomial.C Wb.a₃) ≠ 0 := by
                  intro h0
                  apply ha3
                  have h1 := (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q)))
                    (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) (h0.trans (map_zero _).symm)
                  exact Polynomial.C_eq_zero.mp h1
                have := hτtcA
                rw [hAconst] at this
                rw [map_mul]
                rw [show (Polynomial.C (Wb.a₃⁻¹ * Wb.a₁ * 0 + Wb.a₃⁻¹) :
                  Polynomial (AlgebraicClosure (ZMod q))) = Polynomial.C (Wb.a₃⁻¹) from by
                  norm_num]
                have hinv : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                    (Polynomial.C (Wb.a₃⁻¹)) = (algebraMap
                    (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃))⁻¹ := by
                  refine (inv_eq_of_mul_eq_one_right ?_).symm
                  rw [← map_mul, ← Polynomial.C_mul,
                    mul_inv_cancel₀ ha3, Polynomial.C_1, map_one]
                rw [hinv, this, mul_assoc,
                  mul_inv_cancel₀ hA3ne, mul_one]
              · -- the hard subcase: `a₁ ≠ 0` — the Taylor/singularity
                -- argument
                -- `w := sc · A` is integral over `k[X]`
                have hwint : IsIntegral (Polynomial (AlgebraicClosure (ZMod q)))
                    (sc * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) := by
                  refine ⟨Polynomial.X ^ 2 -
                    Polynomial.C (τ₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X -
                    Polynomial.C ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 * ν₀ + τ₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)),
                    ?_, ?_⟩
                  · rw [show (Polynomial.X ^ 2 -
                      Polynomial.C (τ₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X -
                      Polynomial.C ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 * ν₀ + τ₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) :
                      Polynomial (Polynomial (AlgebraicClosure (ZMod q)))) = Polynomial.X ^ 2 -
                      (Polynomial.C (τ₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X +
                      Polynomial.C ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 * ν₀ + τ₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)))
                      from by ring]
                    refine Polynomial.monic_X_pow_sub ?_
                    refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
                    norm_num
                  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
                      Polynomial.eval₂_mul, Polynomial.eval₂_X,
                      Polynomial.eval₂_C]
                    simp only [map_mul, map_add, map_pow]
                    have hνd := hνdef
                    simp only [map_add, map_mul, map_pow] at hνd
                    have hτA := hτtcA
                    simp only [map_add, map_mul] at hτA
                    linear_combination (- (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2) *
                      hν₀ + (- (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2) *
                      hνd + (- sc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2 -
                      (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ + tc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃))) *
                      (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 3 +
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₂) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 2 +
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₄) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₆))) * hτA
                obtain ⟨w₀, hw₀⟩ :=
                  IsIntegrallyClosed.isIntegral_iff.mp hwint
                -- the polynomial identity `A²ν₀ = w₀² − w₀τ₀A − τ₀²G`
                have hstar : w₀ ^ 2 - τ₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) * w₀ -
                    ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 * ν₀ + τ₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) = 0 := by
                  apply IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                  simp only [map_sub, map_add, map_mul, map_pow, map_zero]
                  have hνd := hνdef
                  simp only [map_add, map_mul, map_pow] at hνd
                  have hτA := hτtcA
                  simp only [map_add, map_mul] at hτA
                  have hw := hw₀
                  simp only [map_add, map_mul] at hw
                  linear_combination (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) w₀ + sc *
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) - algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ *
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃))) * hw +
                    (- (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2) * hν₀ +
                    (- (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2) * hνd +
                    (- sc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) ^ 2 -
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ + tc * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) *
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃))) *
                    (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 3 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₂) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 2 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₄) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₆))) * hτA
                -- characteristic-two facts in the base field
                have ha1' : Wb.a₁ ≠ 0 := ha1
                have h2F0 : (2 : (AlgebraicClosure (ZMod q))) = 0 := by
                  haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                    charP_of_injective_algebraMap
                      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
                  haveI h2 : CharP (AlgebraicClosure (ZMod q)) 2 := CharP.congr q hq2
                  exact_mod_cast CharP.cast_eq_zero (AlgebraicClosure (ZMod q)) 2
                -- the root of the linear form
                set r : (AlgebraicClosure (ZMod q)) := Wb.a₃ * Wb.a₁⁻¹ with hrdef
                have hAr : Polynomial.eval r (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) = 0 := by
                  simp only [Polynomial.eval_add, Polynomial.eval_mul,
                    Polynomial.eval_C, Polynomial.eval_X, hrdef]
                  field_simp
                  linear_combination Wb.a₃ * h2F0
                -- `A` divides `τ₀` (else the reduced curve is singular)
                have hdvdAτ : (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ∣ τ₀ := by
                  by_contra hAndvd
                  have hτr : Polynomial.eval r τ₀ ≠ 0 := by
                    intro h0
                    apply hAndvd
                    have hAfac : ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) : Polynomial (AlgebraicClosure (ZMod q))) =
                        Polynomial.C Wb.a₁ * (Polynomial.X -
                          Polynomial.C r) := by
                      rw [hrdef]
                      rw [mul_sub, ← Polynomial.C_mul]
                      congr 1
                      rw [← Polynomial.C_neg]
                      congr 1
                      field_simp
                      linear_combination Wb.a₃ * h2F0
                    rw [hAfac]
                    exact (IsUnit.mul_left_dvd (Polynomial.isUnit_C.mpr
                      (isUnit_iff_ne_zero.mpr ha1'))).mpr
                      ((Polynomial.dvd_iff_isRoot).mpr h0)
                  -- evaluation of the identity at `r`
                  have hE1 := congrArg (Polynomial.eval r) hstar
                  simp only [Polynomial.eval_sub, Polynomial.eval_add,
                    Polynomial.eval_mul, Polynomial.eval_pow,
                    Polynomial.eval_zero, hAr, mul_zero, zero_mul,
                    sub_zero] at hE1
                  -- derivative of the identity, evaluated at `r`
                  have hE2 := congrArg (Polynomial.eval r)
                    (congrArg Polynomial.derivative hstar)
                  simp only [Polynomial.derivative_sub,
                    Polynomial.derivative_add, Polynomial.derivative_mul,
                    Polynomial.derivative_pow, Polynomial.derivative_C,
                    Polynomial.derivative_X, Polynomial.derivative_zero,
                    Polynomial.eval_sub, Polynomial.eval_add,
                    Polynomial.eval_mul, Polynomial.eval_pow,
                    Polynomial.eval_zero,
                    Polynomial.eval_C, Polynomial.eval_X,
                    hAr, mul_zero, zero_mul,
                    add_zero, zero_add, mul_one] at hE2
                  simp only [Polynomial.eval_X, Polynomial.eval_C] at hE1
                  push_cast at hE1 hE2
                  -- normalized evaluation identities
                  have hE1' : Polynomial.eval r w₀ ^ 2 =
                      Polynomial.eval r τ₀ ^ 2 *
                      (r ^ 3 + Wb.a₂ * r ^ 2 + Wb.a₄ * r + Wb.a₆) := by
                    linear_combination hE1
                  have hE2' : Wb.a₁ * Polynomial.eval r τ₀ *
                      Polynomial.eval r w₀ = Polynomial.eval r τ₀ ^ 2 *
                      (r ^ 2 + Wb.a₄) := by
                    linear_combination (- 1 : (AlgebraicClosure (ZMod q))) * hE2 +
                      (Polynomial.eval r w₀ *
                        Polynomial.eval r (Polynomial.derivative w₀) -
                      Polynomial.eval r τ₀ *
                        Polynomial.eval r (Polynomial.derivative τ₀) *
                        (r ^ 3 + Wb.a₂ * r ^ 2 + Wb.a₄ * r + Wb.a₆) -
                      Polynomial.eval r τ₀ ^ 2 * (r ^ 2 + Wb.a₂ * r) -
                      Polynomial.eval r τ₀ ^ 2 * r ^ 2 -
                      Polynomial.eval r τ₀ ^ 2 * Wb.a₄) * h2F0
                  -- the singular point
                  set y₀ : (AlgebraicClosure (ZMod q)) := (r ^ 2 + Wb.a₄) * Wb.a₁⁻¹ with hy₀def
                  have hwe : Polynomial.eval r w₀ =
                      Polynomial.eval r τ₀ * y₀ := by
                    refine mul_left_cancel₀
                      (a := Wb.a₁ * Polynomial.eval r τ₀)
                      (mul_ne_zero ha1' hτr) ?_
                    rw [hE2', hy₀def]
                    field_simp
                  have hy₀sq : y₀ ^ 2 =
                      r ^ 3 + Wb.a₂ * r ^ 2 + Wb.a₄ * r + Wb.a₆ := by
                    have h1 := hE1'
                    rw [hwe] at h1
                    have h2 : Polynomial.eval r τ₀ ^ 2 * y₀ ^ 2 =
                        Polynomial.eval r τ₀ ^ 2 *
                        (r ^ 3 + Wb.a₂ * r ^ 2 + Wb.a₄ * r + Wb.a₆) := by
                      linear_combination h1
                    exact mul_left_cancel₀ (pow_ne_zero 2 hτr) h2
                  have hArval : Wb.a₁ * r + Wb.a₃ = 0 := by
                    simpa using hAr
                  -- the point lies on the curve …
                  haveI : Wb.IsElliptic := by rw [hWbdef]; infer_instance
                  have hEqn : Wb.toAffine.Equation r y₀ := by
                    rw [WeierstrassCurve.Affine.equation_iff]
                    linear_combination hy₀sq + y₀ * hArval
                  -- … and is nonsingular, but both partials vanish
                  have hNS := WeierstrassCurve.Affine.equation_iff_nonsingular
                    (W := Wb.toAffine).mp hEqn
                  rcases (WeierstrassCurve.Affine.nonsingular_iff' _ _).mp
                    hNS with ⟨-, hX | hY⟩
                  · apply hX
                    rw [hy₀def]
                    field_simp
                    linear_combination (Wb.a₂ * r * Wb.a₁ +
                      r ^ 2 * Wb.a₁ - Wb.a₃ * Wb.a₁ * Wb.a₁⁻¹ *
                      Wb.toAffine.a₂ - Wb.a₃ * Wb.a₁⁻¹ * Wb.toAffine.a₂ -
                      Wb.a₃ ^ 2 * Wb.a₁ * Wb.a₁⁻¹ ^ 2 -
                      Wb.a₃ ^ 2 * Wb.a₁⁻¹ ^ 2) * h2F0
                  · apply hY
                    linear_combination y₀ * h2F0 + hArval
                obtain ⟨t₀', ht₀'⟩ := hdvdAτ
                have hAK : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ≠
                    0 := by
                  intro h0
                  have h1 := (IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q)))
                    (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) (h0.trans (map_zero _).symm)
                  have h2 := congrArg (fun f => Polynomial.coeff f 1) h1
                  simp at h2
                  exact ha1' h2
                refine ⟨t₀', ?_⟩
                have := hτtcA
                rw [ht₀', map_mul] at this
                field_simp at this
                exact this.symm
            obtain ⟨t₀, ht₀⟩ := htcrange
            -- `sc` is integral over `k[X]` via its monic quadratic
            have hscint : IsIntegral (Polynomial (AlgebraicClosure (ZMod q))) sc := by
              refine ⟨Polynomial.X ^ 2 -
                Polynomial.C (t₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X -
                Polynomial.C (ν₀ + t₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)), ?_, ?_⟩
              · rw [show (Polynomial.X ^ 2 -
                  Polynomial.C (t₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X -
                  Polynomial.C (ν₀ + t₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆)) :
                  Polynomial (Polynomial (AlgebraicClosure (ZMod q)))) = Polynomial.X ^ 2 -
                  (Polynomial.C (t₀ * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃)) * Polynomial.X +
                  Polynomial.C (ν₀ + t₀ ^ 2 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆))) from by ring]
                refine Polynomial.monic_X_pow_sub ?_
                refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
                norm_num
              · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
                  Polynomial.eval₂_mul, Polynomial.eval₂_X,
                  Polynomial.eval₂_C]
                simp only [map_mul, map_add, map_pow]
                have hνd := hνdef
                simp only [map_add, map_mul, map_pow] at hνd
                linear_combination - hν₀ - hνd +
                  ((algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₃)) * sc +
                  (tc + algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) t₀) * (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 3 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₂) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X ^ 2 +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₄) * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) Polynomial.X +
                    algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₆))) * ht₀
            obtain ⟨s₀, hs₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hscint
            refine ⟨AdjoinRoot.of Wb.toAffine.polynomial s₀ +
              AdjoinRoot.of Wb.toAffine.polynomial t₀ *
                AdjoinRoot.root Wb.toAffine.polynomial, ?_⟩
            have hofL : ∀ z : Polynomial (AlgebraicClosure (ZMod q)),
                algebraMap Wb.toAffine.CoordinateRing
                  (FractionRing Wb.toAffine.CoordinateRing)
                  (AdjoinRoot.of Wb.toAffine.polynomial z) =
                algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing)
                  (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) z) := fun z => by
              rw [← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                (FractionRing Wb.toAffine.CoordinateRing),
                IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
                  Wb.toAffine.CoordinateRing
                  (FractionRing Wb.toAffine.CoordinateRing),
                AdjoinRoot.algebraMap_eq]
            rw [← hst, ← hs₀, ht₀]
            simp only [map_add, map_mul, hofL, Algebra.smul_def, mul_one]
          · -- reduced-fraction descent against the squarefree cubic
            have hDsf : Squarefree ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 + 4 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) :
                Polynomial (AlgebraicClosure (ZMod q))) := by
              have h2F : (2 : (AlgebraicClosure (ZMod q))) ≠ 0 := by
                haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                  charP_of_injective_algebraMap
                    (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
                exact CharP.cast_ne_zero_of_ne_of_prime (R := (AlgebraicClosure (ZMod q)))
                  Nat.prime_two (fun h => hq2 h)
              have h4F : (4 : (AlgebraicClosure (ZMod q))) ≠ 0 := by
                have : (4 : (AlgebraicClosure (ZMod q))) = 2 * 2 := by norm_num
                rw [this]
                exact mul_ne_zero h2F h2F
              have hWbΔ : Wb.Δ ≠ 0 := by
                haveI : Wb.IsElliptic := by
                  rw [hWbdef]; infer_instance
                exact ((WeierstrassCurve.isElliptic_iff Wb).mp
                  inferInstance).ne_zero
              -- the polynomial is the `b`-cubic
              have hDeq : ((Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 + 4 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) : Polynomial (AlgebraicClosure (ZMod q))) =
                  (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ : Cubic (AlgebraicClosure (ZMod q))).toPoly := by
                rw [Cubic.toPoly]
                simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
                  WeierstrassCurve.b₆, map_add, map_mul, map_pow, map_ofNat]
                ring
              -- its discriminant is `16Δ ≠ 0`
              have hdisc16 : (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ :
                  Cubic (AlgebraicClosure (ZMod q))).discr = 16 * Wb.Δ := by
                rw [Cubic.discr, WeierstrassCurve.Δ]
                linear_combination (4 * Wb.b₂ ^ 2) *
                  (WeierstrassCurve.b_relation Wb)
              have hdisc : (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ :
                  Cubic (AlgebraicClosure (ZMod q))).discr ≠ 0 := by
                rw [hdisc16]
                refine mul_ne_zero ?_ hWbΔ
                have : (16 : (AlgebraicClosure (ZMod q))) = 4 * 4 := by norm_num
                rw [this]
                exact mul_ne_zero h4F h4F
              -- squarefree via nodup roots and separability
              have hne0 : (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ :
                  Cubic (AlgebraicClosure (ZMod q))).toPoly ≠ 0 := by
                intro h0
                have := Cubic.coeff_eq_a (P := (⟨4, Wb.b₂, 2 * Wb.b₄,
                  Wb.b₆⟩ : Cubic (AlgebraicClosure (ZMod q))))
                rw [h0] at this
                simp at this
                exact h4F this.symm
              have hsplits : ((⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ :
                  Cubic (AlgebraicClosure (ZMod q))).toPoly.map (RingHom.id (AlgebraicClosure (ZMod q)))).Splits :=
                IsAlgClosed.splits _
              have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup
                (P := (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ : Cubic (AlgebraicClosure (ZMod q))))
                (φ := RingHom.id (AlgebraicClosure (ZMod q))) (by
                  show (4 : (AlgebraicClosure (ZMod q))) ≠ 0
                  exact h4F) hsplits).mp hdisc
              rw [hDeq]
              refine Polynomial.Separable.squarefree ?_
              refine (Polynomial.nodup_roots_iff_of_splits hne0 ?_).mp ?_
              · have := hsplits
                rwa [Polynomial.map_id] at this
              · have hmap : (Cubic.map (RingHom.id (AlgebraicClosure (ZMod q)))
                    (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ : Cubic (AlgebraicClosure (ZMod q)))).toPoly =
                    (⟨4, Wb.b₂, 2 * Wb.b₄, Wb.b₆⟩ :
                      Cubic (AlgebraicClosure (ZMod q))).toPoly := by
                  rw [Cubic.map_toPoly, Polynomial.map_id]
                rw [Cubic.roots, hmap] at hnodup
                exact hnodup
            obtain ⟨nn, dd, hrel, hmk⟩ :=
              IsFractionRing.exists_reduced_fraction
                (A := Polynomial (AlgebraicClosure (ZMod q))) (K := (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))) tc
            obtain ⟨ww, hww⟩ : ∃ ww, algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                (τ₀ ^ 2 - 4 * ν₀) = tc ^ 2 *
                algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) ww ∧ ww =
                (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) ^ 2 + 4 * (Polynomial.X ^ 3 + Polynomial.C Wb.a₂ * Polynomial.X ^ 2 +
        Polynomial.C Wb.a₄ * Polynomial.X + Polynomial.C Wb.a₆) := ⟨_, hkey, rfl⟩
            obtain ⟨hww1, hww2⟩ := hww
            -- clear denominators: `dd² ∣ nn² · D`
            have hmkdiv : tc = algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) nn /
                algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) dd := by
              rw [← hmk, IsFractionRing.mk'_eq_div]
            have hdd0 : (dd : Polynomial (AlgebraicClosure (ZMod q))) ≠ 0 :=
              nonZeroDivisors.ne_zero dd.2
            have hddK : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) dd ≠ 0 :=
              fun h => hdd0 ((IsFractionRing.injective _ _)
                (h.trans (map_zero _).symm))
            have hpolyeq : nn ^ 2 * ww = (dd : Polynomial (AlgebraicClosure (ZMod q))) ^ 2 *
                (τ₀ ^ 2 - 4 * ν₀) := by
              apply IsFractionRing.injective (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
              rw [map_mul, map_mul, map_pow, map_pow, hww1, hmkdiv]
              field_simp
            have hdvd2 : (dd : Polynomial (AlgebraicClosure (ZMod q))) ^ 2 ∣ nn ^ 2 * ww :=
              ⟨_, hpolyeq⟩
            have hddD : (dd : Polynomial (AlgebraicClosure (ZMod q))) ^ 2 ∣ ww := by
              have hdvd2' : (dd : Polynomial (AlgebraicClosure (ZMod q))) ^ 2 ∣ ww * nn ^ 2 :=
                (mul_comm (nn ^ 2) ww) ▸ hdvd2
              exact (hrel.symm.pow (n := 2) (m := 2)).dvd_of_dvd_mul_right
                hdvd2'
            have hdunit : IsUnit ((dd : Polynomial (AlgebraicClosure (ZMod q)))) := by
              refine hDsf ((dd : Polynomial (AlgebraicClosure (ZMod q)))) ?_
              rw [← hww2, ← sq]
              exact hddD
            -- so `tc` is the image of a polynomial
            obtain ⟨ee, hee⟩ := hdunit.exists_right_inv
            have hinvdd : (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
                (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) dd)⁻¹ =
                algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
                  (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) ee := by
              refine inv_eq_of_mul_eq_one_right ?_
              rw [← map_mul, hee, map_one]
            have htcmem : tc = algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
                (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (nn * ee) := by
              rw [hmkdiv, div_eq_mul_inv, hinvdd, ← map_mul]
            -- recover `sc` (2 is invertible away from characteristic two)
            have h2F : (2 : (AlgebraicClosure (ZMod q))) ≠ 0 := by
              haveI h1 : CharP (AlgebraicClosure (ZMod q)) q :=
                charP_of_injective_algebraMap
                  (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
              exact CharP.cast_ne_zero_of_ne_of_prime (R := (AlgebraicClosure (ZMod q)))
                Nat.prime_two (fun h => hq2 h)
            have h2img : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                (Polynomial.C (2 : (AlgebraicClosure (ZMod q)))) = 2 := by
              rw [map_ofNat Polynomial.C 2, map_ofNat]
            have h2sc : 2 * sc = algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) τ₀ +
                tc * algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃) := by
              rw [hτ₀, hτdef]
              ring
            have hscmem : sc = algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                (Polynomial.C ((2 : (AlgebraicClosure (ZMod q)))⁻¹) *
                  (τ₀ + (nn * ee) * (Polynomial.C Wb.a₁ * Polynomial.X + Polynomial.C Wb.a₃))) := by
              rw [map_mul, map_add, map_mul, ← htcmem, ← h2sc]
              have h1 : algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                  (Polynomial.C ((2 : (AlgebraicClosure (ZMod q)))⁻¹)) * 2 = 1 := by
                rw [← h2img, ← map_mul, ← Polynomial.C_mul,
                  inv_mul_cancel₀ h2F, Polynomial.C_1, map_one]
              rw [← mul_assoc, h1, one_mul]
            -- assemble the coordinate-ring witness
            refine ⟨AdjoinRoot.of Wb.toAffine.polynomial
              (Polynomial.C ((2 : (AlgebraicClosure (ZMod q)))⁻¹) *
                (τ₀ + (nn * ee) * (Polynomial.C Wb.a₁ * Polynomial.X +
                  Polynomial.C Wb.a₃))) +
              AdjoinRoot.of Wb.toAffine.polynomial (nn * ee) *
                AdjoinRoot.root Wb.toAffine.polynomial, ?_⟩
            have hofL : ∀ z : Polynomial (AlgebraicClosure (ZMod q)),
                algebraMap Wb.toAffine.CoordinateRing
                  (FractionRing Wb.toAffine.CoordinateRing)
                  (AdjoinRoot.of Wb.toAffine.polynomial z) =
                algebraMap (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) (FractionRing Wb.toAffine.CoordinateRing)
                  (algebraMap (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q)))) z) := fun z => by
              rw [← IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q))) (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
                (FractionRing Wb.toAffine.CoordinateRing),
                IsScalarTower.algebraMap_apply (Polynomial (AlgebraicClosure (ZMod q)))
                  Wb.toAffine.CoordinateRing
                  (FractionRing Wb.toAffine.CoordinateRing),
                AdjoinRoot.algebraMap_eq]
            rw [← hst, hscmem, htcmem]
            simp only [map_add, map_mul, hofL, Algebra.smul_def, mul_one]
      · rintro ⟨y, rfl⟩
        exact IsIntegral.map (IsScalarTower.toAlgHom (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing
          (FractionRing Wb.toAffine.CoordinateRing))
          (Algebra.IsIntegral.isIntegral y)
    exact IsIntegralClosure.isDedekindDomain (Polynomial (AlgebraicClosure (ZMod q)))
      (FractionRing (Polynomial (AlgebraicClosure (ZMod q))))
      (FractionRing Wb.toAffine.CoordinateRing)
      Wb.toAffine.CoordinateRing
  -- units of the coordinate ring are the nonzero constants (the norm
  -- has degree zero, forcing the basis components down)
  have hCunits : ∀ u : Wb.toAffine.CoordinateRing, IsUnit u →
      ∃ c : (AlgebraicClosure (ZMod q)), c ≠ 0 ∧ u = AdjoinRoot.of Wb.toAffine.polynomial
        (Polynomial.C c) := by
    intro u hu
    obtain ⟨pp, qq, rfl⟩ :=
      WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
    -- the norm of a unit is a unit of `k[X]`, so it has degree zero
    obtain ⟨v, hv⟩ := hu
    have hnu : IsUnit (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (pp • 1 + qq • AdjoinRoot.mk Wb.toAffine.polynomial
          Polynomial.X)) := by
      refine isUnit_iff_exists.mpr ⟨Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        ((v⁻¹ : Wb.toAffine.CoordinateRingˣ) :
          Wb.toAffine.CoordinateRing), ?_, ?_⟩
      · rw [← map_mul]
        rw [show (pp • 1 + qq • AdjoinRoot.mk Wb.toAffine.polynomial
          Polynomial.X) * ((v⁻¹ : Wb.toAffine.CoordinateRingˣ) :
          Wb.toAffine.CoordinateRing) = ((v * v⁻¹ :
          Wb.toAffine.CoordinateRingˣ) : Wb.toAffine.CoordinateRing)
          from by rw [Units.val_mul, hv]]
        rw [mul_inv_cancel, Units.val_one, map_one]
      · rw [← map_mul]
        rw [show ((v⁻¹ : Wb.toAffine.CoordinateRingˣ) :
          Wb.toAffine.CoordinateRing) * (pp • 1 + qq •
          AdjoinRoot.mk Wb.toAffine.polynomial Polynomial.X) =
          ((v⁻¹ * v : Wb.toAffine.CoordinateRingˣ) :
          Wb.toAffine.CoordinateRing) from by rw [Units.val_mul, hv]]
        rw [inv_mul_cancel, Units.val_one, map_one]
    have hdeg0 : (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (pp • 1 + qq • AdjoinRoot.mk Wb.toAffine.polynomial
          Polynomial.X)).degree = 0 :=
      Polynomial.degree_eq_zero_of_isUnit hnu
    rw [WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis]
      at hdeg0
    -- the max forces `qq = 0` and `pp` constant
    have hqq : qq = 0 := by
      by_contra hqq0
      have h1 : (2 • qq.degree + 3 : WithBot ℕ) ≤ 0 := by
        rw [← hdeg0]
        exact le_max_right _ _
      have h2 : (0 : WithBot ℕ) ≤ 2 • qq.degree + 3 := by
        have h3 : (0 : WithBot ℕ) ≤ qq.degree :=
          Polynomial.zero_le_degree_iff.mpr hqq0
        calc (0 : WithBot ℕ) ≤ 2 • qq.degree := by
              rw [show (2 : ℕ) • qq.degree = qq.degree + qq.degree from
                two_nsmul qq.degree]
              exact le_trans h3 (le_add_of_nonneg_left h3)
          _ ≤ 2 • qq.degree + 3 := le_add_of_nonneg_right (by norm_num)
      have h4 : (2 • qq.degree + 3 : WithBot ℕ) = 0 := le_antisymm h1 h2
      have h5 : (0 : WithBot ℕ) < 2 • qq.degree + 3 := by
        refine lt_of_lt_of_le (by norm_num : (0 : WithBot ℕ) < 3) ?_
        refine le_add_of_nonneg_left ?_
        rw [show (2 : ℕ) • qq.degree = qq.degree + qq.degree from
          two_nsmul qq.degree]
        have h3 : (0 : WithBot ℕ) ≤ qq.degree :=
          Polynomial.zero_le_degree_iff.mpr hqq0
        exact le_trans h3 (le_add_of_nonneg_left h3)
      exact absurd h4 (ne_of_gt h5)
    have hpp : pp.degree = 0 := by
      rw [hqq] at hdeg0
      simp only [Polynomial.degree_zero] at hdeg0
      have : (2 • pp.degree : WithBot ℕ) = 0 := by
        rw [← hdeg0]
        rw [max_eq_left]
        rw [show (2 : ℕ) • (⊥ : WithBot ℕ) + 3 = ⊥ from by rfl]
        exact bot_le
      rw [two_nsmul, Nat.WithBot.add_eq_zero_iff] at this
      exact this.1
    -- conclude: `pp` is the constant `c`
    have hppC : pp = Polynomial.C (pp.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (le_of_eq hpp)
    refine ⟨pp.coeff 0, ?_, ?_⟩
    · intro h0
      have hppz : pp = 0 := by rw [hppC, h0, Polynomial.C_0]
      have hz : (pp • 1 + qq • AdjoinRoot.mk Wb.toAffine.polynomial
          Polynomial.X : Wb.toAffine.CoordinateRing) = 0 := by
        rw [hppz, hqq, zero_smul, zero_smul, add_zero]
      exact Units.ne_zero v (hv.trans hz)
    · conv_lhs => rw [hqq, zero_smul, add_zero, hppC]
      rw [Algebra.smul_def, mul_one]
      rfl
  -- Miller generators: the `p`-th power of a torsion point's ideal
  -- class is principal
  have hgen : ∀ (x y : (AlgebraicClosure (ZMod q))) (h : Wb.toAffine.Nonsingular x y),
      ((p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        Wb.toAffine.Point) = 0) →
      (((WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h ^ p :
        (FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)ˣ) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField) :
        Submodule Wb.toAffine.CoordinateRing
          Wb.toAffine.FunctionField).IsPrincipal := by
    intro x y h htor
    have hclass := congrArg WeierstrassCurve.Affine.Point.toClass htor
    rw [map_zsmul, map_zero] at hclass
    have hmk : ((p : ℤ) •
        (WeierstrassCurve.Affine.Point.toClass
          (WeierstrassCurve.Affine.Point.some x y h)) :
        Additive (ClassGroup Wb.toAffine.CoordinateRing)) =
        Additive.ofMul ((ClassGroup.mk Wb.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h)) ^
          (p : ℤ)) := by
      rfl
    rw [hmk] at hclass
    have h1 : (ClassGroup.mk Wb.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h)) ^ (p : ℤ) =
        1 := by
      have := congrArg Additive.toMul hclass
      simpa using this
    rw [zpow_natCast, ← map_pow] at h1
    exact ClassGroup.mk_eq_one_iff.mp h1
  -- point evaluation is `AdjoinRoot.evalEval` (mathlib); the curve has
  -- points outside any finite set of abscissas (algebraically closed
  -- base: the quadratic in `Y` always has a root)
  have hpoints : ∀ S : Finset (AlgebraicClosure (ZMod q)), ∃ x₀ ∉ S, ∃ y₀,
      Wb.toAffine.Nonsingular x₀ y₀ := by
    intro S
    obtain ⟨x₀, hx₀⟩ := S.exists_notMem
    -- solve the quadratic in `y` at `x₀`
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
      (Wb.toAffine.polynomial.map (Polynomial.evalRingHom x₀)) (by
        rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero]
        · rw [WeierstrassCurve.Affine.degree_polynomial]
          norm_num
        · rw [show Wb.toAffine.polynomial.leadingCoeff =
            (1 : Polynomial (AlgebraicClosure (ZMod q))) from
            WeierstrassCurve.Affine.monic_polynomial]
          simp)
    refine ⟨x₀, hx₀, y₀, ?_⟩
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular]
    rw [WeierstrassCurve.Affine.Equation]
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hy₀
    rw [show Wb.toAffine.polynomial.evalEval x₀ y₀ =
      Wb.toAffine.polynomial.eval₂ (Polynomial.evalRingHom x₀) y₀ from
      (Polynomial.eval₂_evalRingHom x₀ ▸ rfl)]
    exact hy₀
  -- two-point Miller generators: if `p(P₁ − P₂) = 0` then
  -- `(I_{P₁} I_{P₂}⁻¹)^p` is principal
  have hgen2 : ∀ (x₁ y₁ x₂ y₂ : (AlgebraicClosure (ZMod q)))
      (h₁ : Wb.toAffine.Nonsingular x₁ y₁)
      (h₂ : Wb.toAffine.Nonsingular x₂ y₂),
      ((p : ℤ) • ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
        Wb.toAffine.Point) - WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
        = 0) →
      ((((WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁ *
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂)⁻¹) ^ p :
        (FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)ˣ) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField) :
        Submodule Wb.toAffine.CoordinateRing
          Wb.toAffine.FunctionField).IsPrincipal := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ htor
    have hclass := congrArg WeierstrassCurve.Affine.Point.toClass htor
    rw [map_zsmul, map_sub, map_zero] at hclass
    have hmk : ((p : ℤ) •
        ((WeierstrassCurve.Affine.Point.toClass
          (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)) -
        (WeierstrassCurve.Affine.Point.toClass
          (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂))) :
        Additive (ClassGroup Wb.toAffine.CoordinateRing)) =
        Additive.ofMul (((ClassGroup.mk Wb.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁)) *
        (ClassGroup.mk Wb.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂))⁻¹) ^
          (p : ℤ)) := by
      rfl
    rw [hmk] at hclass
    have h1 : (ClassGroup.mk Wb.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁)) ^ p *
        ((ClassGroup.mk Wb.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂)) ^ p)⁻¹ =
        1 := by
      have := congrArg Additive.toMul hclass
      simpa using this
    rw [← map_pow, ← map_pow, ← map_inv, ← map_mul] at h1
    rw [show (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁ *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂)⁻¹) ^ p =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₁ ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h₂ ^ p)⁻¹ from by
      rw [mul_pow, inv_pow]]
    exact ClassGroup.mk_eq_one_iff.mp h1
  -- Weil reciprocity on the affine line: the double-product swap identity
  -- `prod_{a in roots F} G(a) = (-1)^(deg F * deg G) * prod_{b in roots G} F(b)`
  -- for monic polynomials over the algebraically closed base
  have hcard : ∀ H : Polynomial (AlgebraicClosure (ZMod q)),
      Multiset.card H.roots = H.natDegree := fun H =>
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits H)
  have hevalprod : ∀ (H : Polynomial (AlgebraicClosure (ZMod q))), H.Monic →
      ∀ a : (AlgebraicClosure (ZMod q)),
      H.eval a = (H.roots.map fun b => a - b).prod := by
    intro H hH a
    conv_lhs => rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      hH (hcard H)]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => by
      simp)
  have hrecP1 : ∀ F G : Polynomial (AlgebraicClosure (ZMod q)), F.Monic → G.Monic →
      (F.roots.map G.eval).prod =
        (-1) ^ (F.natDegree * G.natDegree) * (G.roots.map F.eval).prod := by
    intro F G hF hG
    calc (F.roots.map G.eval).prod
        = (F.roots.map fun a => (G.roots.map fun b => a - b).prod).prod :=
          congrArg Multiset.prod
            (Multiset.map_congr rfl fun a _ => hevalprod G hG a)
      _ = (G.roots.map fun b => (F.roots.map fun a => a - b).prod).prod :=
          Multiset.prod_map_prod_map F.roots G.roots
      _ = (G.roots.map fun b =>
            ((-1 : (AlgebraicClosure (ZMod q))) ^ F.natDegree *
              (F.roots.map fun a => b - a).prod)).prod := by
          refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
          have hneg : (F.roots.map fun a => a - b) =
              (F.roots.map fun a => b - a).map Neg.neg := by
            rw [Multiset.map_map]
            exact Multiset.map_congr rfl fun a _ => by simp
          rw [hneg, Multiset.prod_map_neg, Multiset.card_map, hcard F]
      _ = (-1) ^ (F.natDegree * G.natDegree) * (G.roots.map F.eval).prod := by
          rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
            ← pow_mul, hcard G]
          exact congrArg _ (congrArg Multiset.prod
            (Multiset.map_congr rfl fun b _ => (hevalprod F hF b).symm))
  -- the line identity: the ideal of the line through `P`, `Q` (in the
  -- generic-slope case) is exactly `I_P * I_Q * I_{-(P + Q)}` -- the affine
  -- divisor of the line function, with no point at infinity anywhere
  have hline : ∀ (x₁ y₁ x₂ y₂ : (AlgebraicClosure (ZMod q)))
      (h₁ : Wb.toAffine.Nonsingular x₁ y₁)
      (h₂ : Wb.toAffine.Nonsingular x₂ y₂)
      (hxy : ¬(x₁ = x₂ ∧ y₁ = Wb.toAffine.negY x₂ y₂)),
      WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
        (WeierstrassCurve.Affine.linePolynomial x₁ y₁
          (Wb.toAffine.slope x₁ x₂ y₁ y₂)) =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₁
        (Polynomial.C y₁) *
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
        (Polynomial.C y₂) *
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
        (Polynomial.C (Wb.toAffine.negY
          (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
          (Wb.toAffine.addY x₁ x₂ y₁ (Wb.toAffine.slope x₁ x₂ y₁ y₂)))) := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hxy
    classical
    have hns₃ := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy
    have key := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal
      (W := Wb.toAffine) h₁.left h₂.left hxy
    have hneg := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
      (W := Wb.toAffine) hns₃
    rw [← hneg] at key
    have hI₃ : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
        (Polynomial.C (Wb.toAffine.addY x₁ x₂ y₁
          (Wb.toAffine.slope x₁ x₂ y₁ y₂))) ≠ 0 := by
      intro h0
      have hmem : WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂)) ∈
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
            (Polynomial.C (Wb.toAffine.addY x₁ x₂ y₁
              (Wb.toAffine.slope x₁ x₂ y₁ y₂))) :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h0] at hmem
      exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
        (W' := Wb.toAffine) _ ((Submodule.mem_bot _).mp hmem)
    refine mul_left_cancel₀ hI₃ ?_
    calc WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
          (Polynomial.C (Wb.toAffine.addY x₁ x₂ y₁
            (Wb.toAffine.slope x₁ x₂ y₁ y₂))) *
        WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial x₁ y₁
            (Wb.toAffine.slope x₁ x₂ y₁ y₂))
        = WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
            (WeierstrassCurve.Affine.linePolynomial x₁ y₁
              (Wb.toAffine.slope x₁ x₂ y₁ y₂)) *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
            (Polynomial.C (Wb.toAffine.addY x₁ x₂ y₁
              (Wb.toAffine.slope x₁ x₂ y₁ y₂))) := mul_comm _ _
      _ = WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
            (Polynomial.C (Wb.toAffine.negY
              (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
              (Wb.toAffine.addY x₁ x₂ y₁ (Wb.toAffine.slope x₁ x₂ y₁ y₂)))) *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
            (Polynomial.C (Wb.toAffine.addY x₁ x₂ y₁
              (Wb.toAffine.slope x₁ x₂ y₁ y₂))) *
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₁
            (Polynomial.C y₁) *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
            (Polynomial.C y₂)) := key.symm
      _ = _ := by ring
  -- root-product transform: for a monic split cubic `H` and `c ≠ 0`,
  -- `prod_{b in roots H} (c b + d) = -c^3 H(z)` where `z = -d/c`
  have hcubtrans : ∀ (H : Polynomial (AlgebraicClosure (ZMod q))), H.Monic → H.natDegree = 3 →
      ∀ (c d z : (AlgebraicClosure (ZMod q))), d = -c * z →
      (H.roots.map (fun b => c * b + d)).prod = - c ^ 3 * H.eval z := by
    intro H hH hdeg c d z hd
    calc (H.roots.map fun b => c * b + d).prod
        = (H.roots.map fun b => c * (b - z)).prod :=
          congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => by
            rw [hd]; ring)
      _ = c ^ 3 * (H.roots.map fun b => b - z).prod := by
          rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
            hcard H, hdeg]
      _ = c ^ 3 * ((-1) ^ 3 * (H.roots.map fun b => z - b).prod) := by
          have hneg : (H.roots.map fun b => b - z) =
              (H.roots.map fun b => z - b).map Neg.neg := by
            rw [Multiset.map_map]
            exact Multiset.map_congr rfl fun a _ => by simp
          rw [hneg, Multiset.prod_map_neg, Multiset.card_map, hcard H, hdeg]
      _ = - c ^ 3 * H.eval z := by rw [← hevalprod H hH z]; ring
  -- line-line Weil reciprocity core: for two non-vertical lines
  -- `y = l_i x + n_i` with distinct slopes, the product of the values of
  -- line 1 at the affine intersection points of line 2 with the curve equals
  -- MINUS the product of the values of line 2 at those of line 1 -- via the
  -- shared intersection point `z` of the two lines and Vieta
  have hlinerec : ∀ (l₁ n₁ l₂ n₂ : (AlgebraicClosure (ZMod q))), l₁ ≠ l₂ →
      ∀ C₁ C₂ : Polynomial (AlgebraicClosure (ZMod q)),
      C₁ = Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₁ ^ 2 - Wb.toAffine.a₁ * l₁)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₁ * n₁ - Wb.toAffine.a₁ * n₁
            - Wb.toAffine.a₃ * l₁) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₁ ^ 2 - Wb.toAffine.a₃ * n₁) →
      C₂ = Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₂ ^ 2 - Wb.toAffine.a₁ * l₂)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₂ * n₂ - Wb.toAffine.a₁ * n₂
            - Wb.toAffine.a₃ * l₂) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₂ ^ 2 - Wb.toAffine.a₃ * n₂) →
      (C₂.roots.map (fun b => (l₂ - l₁) * b + (n₂ - n₁))).prod =
        - (C₁.roots.map (fun a => (l₁ - l₂) * a + (n₁ - n₂))).prod := by
    intro l₁ n₁ l₂ n₂ hl C₁ C₂ hC₁ hC₂
    have hsub : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    set z : (AlgebraicClosure (ZMod q)) := (n₁ - n₂) / (l₂ - l₁) with hz
    have hkey : l₁ * z + n₁ = l₂ * z + n₂ := by
      rw [hz]; field_simp; ring
    have hmon₁ : C₁.Monic := by rw [hC₁]; monicity!
    have hmon₂ : C₂.Monic := by rw [hC₂]; monicity!
    have hdeg₁ : C₁.natDegree = 3 := by rw [hC₁]; compute_degree!
    have hdeg₂ : C₂.natDegree = 3 := by rw [hC₂]; compute_degree!
    have ht₂ := hcubtrans C₂ hmon₂ hdeg₂ (l₂ - l₁) (n₂ - n₁) z (by
      rw [hz]; field_simp; ring)
    have ht₁ := hcubtrans C₁ hmon₁ hdeg₁ (l₁ - l₂) (n₁ - n₂) z (by
      rw [hz]; field_simp; ring)
    have heq : C₁.eval z = C₂.eval z := by
      rw [hC₁, hC₂]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      linear_combination (-(l₁ * z + n₁) - (l₂ * z + n₂)
        - Wb.toAffine.a₁ * z - Wb.toAffine.a₃) * hkey
    rw [ht₂, ht₁, heq]
    ring
  -- norm-evaluation compatibility: the norm of `f = a + b y` down to `k[x]`,
  -- evaluated at an abscissa `x₀` of a curve point `(x₀, y₀)`, is the product
  -- of the values of `f` at the two fiber points `(x₀, y₀)` and
  -- `(x₀, -y₀ - a₁x₀ - a₃)`
  have hnormeval : ∀ (a b : Polynomial (AlgebraicClosure (ZMod q))) (x₀ y₀ : (AlgebraicClosure (ZMod q))),
      Wb.toAffine.Equation x₀ y₀ →
      Polynomial.eval x₀ (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (a • (1 : Wb.toAffine.CoordinateRing) +
          b • AdjoinRoot.mk Wb.toAffine.polynomial Polynomial.X)) =
      (a.eval x₀ + b.eval x₀ * y₀) *
        (a.eval x₀ + b.eval x₀ * Wb.toAffine.negY x₀ y₀) := by
    intro a b x₀ y₀ hE
    have heq := (WeierstrassCurve.Affine.equation_iff (W := Wb.toAffine) x₀ y₀).mp hE
    rw [show (AdjoinRoot.mk Wb.toAffine.polynomial Polynomial.X :
        Wb.toAffine.CoordinateRing) =
      WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine Polynomial.X from rfl]
    rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      WeierstrassCurve.Affine.negY]
    linear_combination (b.eval x₀) ^ 2 * heq
  -- point ideals are maximal: the quotient by `XYIdeal x₀ (C y₀)` is the
  -- base field, via mathlib's `quotientXYIdealEquiv`
  have hXYmax : ∀ (x₀ y₀ : (AlgebraicClosure (ZMod q))), Wb.toAffine.Equation x₀ y₀ →
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C y₀)).IsMaximal := by
    intro x₀ y₀ hE
    refine Ideal.Quotient.maximal_of_isField _ ?_
    exact (WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv
      (W' := Wb.toAffine) hE).toMulEquiv.isField
      (Field.toIsField (AlgebraicClosure (ZMod q)))
  -- every maximal ideal of the coordinate ring contains a vertical `x - c`:
  -- the norm of a nonzero member is a nonzero polynomial of `k[x]` lying in
  -- the (prime) contraction, which therefore contains a linear factor
  have hlinfac : ∀ M : Ideal Wb.toAffine.CoordinateRing, M.IsMaximal →
      ∃ c : (AlgebraicClosure (ZMod q)), algebraMap (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing
        (Polynomial.X - Polynomial.C c) ∈ M := by
    intro M hM
    obtain ⟨x₁, -, y₁, hns₁⟩ := hpoints ∅
    have hbot : M ≠ ⊥ := by
      intro hMbot
      have hXYm := hXYmax x₁ y₁ hns₁.left
      have hbotmax : (⊥ : Ideal Wb.toAffine.CoordinateRing).IsMaximal := hMbot ▸ hM
      have hEq := hbotmax.eq_of_le hXYm.ne_top bot_le
      refine WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
        (W' := Wb.toAffine) x₁ ?_
      have hmem : WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine x₁ ∈
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₁
            (Polynomial.C y₁) :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [← hEq] at hmem
      exact (Submodule.mem_bot _).mp hmem
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨a, b, rfl⟩ :=
      WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
        (W' := Wb.toAffine) f
    -- the norm is nonzero
    have hab : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hf0
    have hN0 : Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (a • (1 : Wb.toAffine.CoordinateRing) +
          b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
            Polynomial.X) ≠ 0 := by
      intro h0
      have hdeg := WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis
        (W' := Wb.toAffine) a b
      rw [h0, Polynomial.degree_zero] at hdeg
      rcases max_eq_bot.mp hdeg.symm with ⟨ha, hb⟩
      have h2 : ∀ d : WithBot ℕ, 2 • d = ⊥ → d = ⊥ := by
        intro d hd
        cases d with
        | bot => rfl
        | coe n => simp [two_smul, WithBot.add_eq_bot] at hd
      refine hab ⟨Polynomial.degree_eq_bot.mp (h2 _ ha),
        Polynomial.degree_eq_bot.mp (h2 _ ?_)⟩
      rcases WithBot.add_eq_bot.mp hb with h | h
      · exact h
      · exact absurd h (by simp)
    -- the norm lies in `M` (it is `f` times the explicit conjugate) hence in
    -- the contraction, which is prime; the norm splits into linear factors,
    -- so one linear factor lies in the contraction
    have hmkf : WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
        (Polynomial.C a + Polynomial.C b * Polynomial.X) =
        a • (1 : Wb.toAffine.CoordinateRing) +
          b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
            Polynomial.X := by
      rw [map_add, map_mul, Algebra.smul_def, Algebra.smul_def,
        AdjoinRoot.algebraMap_eq, mul_one]
      rfl
    have hNfM : algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing
        (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
          (a • (1 : Wb.toAffine.CoordinateRing) +
            b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
              Polynomial.X)) ∈ M := by
      rw [AdjoinRoot.algebraMap_eq,
        WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis]
      rw [map_mul, hmkf]
      exact M.mul_mem_right _ hfM
    have hprime : (M.comap (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing)).IsPrime :=
      Ideal.IsPrime.comap _ (hK := hM.isPrime)
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (p := Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (a • (1 : Wb.toAffine.CoordinateRing) +
          b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
            Polynomial.X)) (hcard _)
    have hmemfac : Polynomial.C (Algebra.norm
          (Polynomial (AlgebraicClosure (ZMod q)))
          (a • (1 : Wb.toAffine.CoordinateRing) +
            b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
              Polynomial.X)).leadingCoeff *
        ((Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
          (a • (1 : Wb.toAffine.CoordinateRing) +
            b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
              Polynomial.X)).roots.map
          (fun r => Polynomial.X - Polynomial.C r)).prod ∈
        M.comap (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing) := by
      rw [hfac]
      exact Ideal.mem_comap.mpr hNfM
    rcases hprime.mem_or_mem hmemfac with hlc | hprod
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hlc
        ((Polynomial.isUnit_C).mpr (IsUnit.mk0 _
          (Polynomial.leadingCoeff_ne_zero.mpr hN0)))) hprime.ne_top
    · obtain ⟨g, hg, hgM⟩ :=
        (hprime.multiset_prod_mem_iff_exists_mem _).mp hprod
      obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hg
      exact ⟨c, Ideal.mem_comap.mp hgM⟩
  -- polynomial scalars die modulo a maximal ideal containing the matching
  -- vertical: `g • z ≡ g(c) • z` modulo `M` when `x - c ∈ M`
  have hkill : ∀ (M : Ideal Wb.toAffine.CoordinateRing) (c : (AlgebraicClosure (ZMod q))),
      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing
        (Polynomial.X - Polynomial.C c) ∈ M →
      ∀ g : Polynomial (AlgebraicClosure (ZMod q)),
      Ideal.Quotient.mk M (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing (g - Polynomial.C (g.eval c))) = 0 := by
    intro M c hc g
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot
      (p := g - Polynomial.C (g.eval c)) (a := c)).mpr (by simp)
    rw [hh, map_mul]
    exact M.mul_mem_right _ hc
  -- residue-field finiteness: modulo a maximal ideal containing a vertical,
  -- the quotient is spanned over the base field by the images of the basis
  -- `{1, y}`, hence a finite module
  have hresfin : ∀ (M : Ideal Wb.toAffine.CoordinateRing) (c : (AlgebraicClosure (ZMod q))),
      algebraMap (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing
        (Polynomial.X - Polynomial.C c) ∈ M →
      Module.Finite (AlgebraicClosure (ZMod q)) (Wb.toAffine.CoordinateRing ⧸ M) := by
    intro M c hc
    have hsplit : ∀ (g : Polynomial (AlgebraicClosure (ZMod q))) (z : Wb.toAffine.CoordinateRing),
        Ideal.Quotient.mk M (g • z) =
          g.eval c • Ideal.Quotient.mk M z := by
      intro g z
      have h1 : g • z = (g - Polynomial.C (g.eval c)) • z +
          (Polynomial.C (g.eval c)) • z := by
        rw [← add_smul, sub_add_cancel]
      rw [h1, map_add]
      have h2 : Ideal.Quotient.mk M ((g - Polynomial.C (g.eval c)) • z) = 0 := by
        rw [Algebra.smul_def, map_mul, hkill M c hc g, zero_mul]
      rw [h2, zero_add, Algebra.smul_def, map_mul]
      rw [show algebraMap (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing
          (Polynomial.C (g.eval c)) =
        algebraMap (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing (g.eval c) from
        (IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q)) (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing (g.eval c)).symm]
      rw [← Ideal.Quotient.algebraMap_eq]
      rw [← IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing
        (Wb.toAffine.CoordinateRing ⧸ M) (g.eval c)]
      rw [← Algebra.smul_def]
    refine ⟨⟨{Ideal.Quotient.mk M 1, Ideal.Quotient.mk M
      (WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine Polynomial.X)},
      ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, b, rfl⟩ :=
      WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
        (W' := Wb.toAffine) w
    rw [map_add, hsplit a 1, hsplit b _]
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · simp
    · simp
  -- CLASSIFICATION: every maximal ideal of the coordinate ring is a point
  -- ideal `XYIdeal x₀ (C y₀)` at a point of the curve
  have hmax : ∀ M : Ideal Wb.toAffine.CoordinateRing, M.IsMaximal →
      ∃ (x₀ y₀ : (AlgebraicClosure (ZMod q))), Wb.toAffine.Equation x₀ y₀ ∧
        M = WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₀) := by
    intro M hM
    obtain ⟨c, hc⟩ := hlinfac M hM
    haveI := hM
    letI : Field (Wb.toAffine.CoordinateRing ⧸ M) := Ideal.Quotient.field M
    haveI := hresfin M c hc
    haveI : Algebra.IsIntegral (AlgebraicClosure (ZMod q)) (Wb.toAffine.CoordinateRing ⧸ M) :=
      Algebra.IsIntegral.of_finite _ _
    have hbij : Function.Bijective (algebraMap (AlgebraicClosure (ZMod q))
        (Wb.toAffine.CoordinateRing ⧸ M)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    obtain ⟨y₀, hy₀⟩ := hbij.2 (Ideal.Quotient.mk M
      (WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine Polynomial.X))
    -- the two coordinate classes lie in `M`
    have hXmem : WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine c ∈
        M := by
      show AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.C (Polynomial.X - Polynomial.C c)) ∈ M
      exact hc
    have hYmem : WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
        (Polynomial.C y₀) ∈ M := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show Ideal.Quotient.mk M (AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.X - Polynomial.C (Polynomial.C y₀))) = 0
      rw [map_sub, map_sub]
      rw [show (AdjoinRoot.mk Wb.toAffine.polynomial)
          (Polynomial.C (Polynomial.C y₀)) =
        algebraMap (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing y₀ from by
        rw [IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q))
          (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing, Polynomial.algebraMap_eq,
          AdjoinRoot.algebraMap_eq]
        rfl]
      rw [← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing
          (Wb.toAffine.CoordinateRing ⧸ M) y₀]
      rw [Ideal.Quotient.algebraMap_eq, hy₀, sub_self]
    -- the point satisfies the equation: Taylor-decompose the Weierstrass
    -- polynomial at `(c, y₀)` and push into the quotient
    have hEq : Wb.toAffine.Equation c y₀ := by
      obtain ⟨B, hB⟩ := (Polynomial.dvd_iff_isRoot
        (p := Wb.toAffine.polynomial -
          Polynomial.C (Wb.toAffine.polynomial.eval (Polynomial.C y₀)))
        (a := Polynomial.C y₀)).mpr (by
          simp [Polynomial.IsRoot, Polynomial.eval_sub])
      obtain ⟨A, hA⟩ := (Polynomial.dvd_iff_isRoot
        (p := Wb.toAffine.polynomial.eval (Polynomial.C y₀) -
          Polynomial.C ((Wb.toAffine.polynomial.eval
            (Polynomial.C y₀)).eval c)) (a := c)).mpr (by
          simp [Polynomial.IsRoot, Polynomial.eval_sub])
      have hpoly : Wb.toAffine.polynomial =
          Polynomial.C (Polynomial.C ((Wb.toAffine.polynomial.eval
            (Polynomial.C y₀)).eval c)) +
          Polynomial.C ((Polynomial.X - Polynomial.C c) * A) +
          (Polynomial.X - Polynomial.C (Polynomial.C y₀)) * B := by
        rw [show (Polynomial.X - Polynomial.C c) * A =
          Wb.toAffine.polynomial.eval (Polynomial.C y₀) -
            Polynomial.C ((Wb.toAffine.polynomial.eval
              (Polynomial.C y₀)).eval c) from hA.symm]
        rw [show (Polynomial.X - Polynomial.C (Polynomial.C y₀)) * B =
          Wb.toAffine.polynomial -
            Polynomial.C (Wb.toAffine.polynomial.eval (Polynomial.C y₀))
          from hB.symm]
        rw [Polynomial.C_sub]
        ring
      have h0 : Ideal.Quotient.mk M (AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.C (Polynomial.C ((Wb.toAffine.polynomial.eval
            (Polynomial.C y₀)).eval c)) +
          Polynomial.C ((Polynomial.X - Polynomial.C c) * A) +
          (Polynomial.X - Polynomial.C (Polynomial.C y₀)) * B)) = 0 := by
        rw [← hpoly, AdjoinRoot.mk_self, map_zero]
      simp only [map_add, map_mul] at h0
      have hz1 : Ideal.Quotient.mk M ((AdjoinRoot.mk Wb.toAffine.polynomial)
          (Polynomial.C (Polynomial.X - Polynomial.C c))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hXmem
      have hz2 : Ideal.Quotient.mk M ((AdjoinRoot.mk Wb.toAffine.polynomial)
          (Polynomial.X - Polynomial.C (Polynomial.C y₀))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hYmem
      rw [hz1, hz2, zero_mul, zero_mul, add_zero, add_zero] at h0
      rw [show (AdjoinRoot.mk Wb.toAffine.polynomial)
          (Polynomial.C (Polynomial.C ((Wb.toAffine.polynomial.eval
            (Polynomial.C y₀)).eval c))) =
        algebraMap (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing
          ((Wb.toAffine.polynomial.eval (Polynomial.C y₀)).eval c) from by
        rw [IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q))
          (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing, Polynomial.algebraMap_eq,
          AdjoinRoot.algebraMap_eq]
        rfl] at h0
      rw [← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (AlgebraicClosure (ZMod q)) Wb.toAffine.CoordinateRing
          (Wb.toAffine.CoordinateRing ⧸ M)] at h0
      have hval : (Wb.toAffine.polynomial.eval (Polynomial.C y₀)).eval c = 0 :=
        (map_eq_zero_iff _ (algebraMap (AlgebraicClosure (ZMod q)) _).injective).mp h0
      exact hval
    refine ⟨c, y₀, hEq, ((hXYmax c y₀ hEq).eq_of_le hM.ne_top ?_).symm⟩
    rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hXmem
    · exact hYmem
  -- principal-divisor factorization: every nonzero element's span is a
  -- product of point ideals with multiplicity -- its affine divisor
  have hfactor : ∀ f : Wb.toAffine.CoordinateRing, f ≠ 0 →
      ∃ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
        (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) ∧
        Ideal.span {f} =
          (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2))).prod := by
    intro f hf
    classical
    have hspan : Ideal.span {f} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hf
    have hprodeq := Ideal.prod_normalizedFactors_eq_self hspan
    -- each normalized factor is maximal, hence a point ideal by `hmax`
    have hptfun : ∀ I ∈ UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {f}), ∃ (x₀ y₀ : (AlgebraicClosure (ZMod q))),
        Wb.toAffine.Equation x₀ y₀ ∧
        I = WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₀) := by
      intro I hI
      have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor I hI
      have hmaximal : I.IsMaximal :=
        ((Ideal.prime_iff_isPrime hprime.ne_zero).mp hprime).isMaximal
          hprime.ne_zero
      exact hmax I hmaximal
    refine ⟨(UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {f})).attach.map (fun I =>
        ((hptfun I.1 I.2).choose, (hptfun I.1 I.2).choose_spec.choose)), ?_, ?_⟩
    · intro P hP
      obtain ⟨I, -, hIP⟩ := Multiset.mem_map.mp hP
      rw [← hIP]
      exact (hptfun I.1 I.2).choose_spec.choose_spec.1
    · have hMeq : ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {f})).attach.map (fun I =>
          ((hptfun I.1 I.2).choose,
            (hptfun I.1 I.2).choose_spec.choose))).map
          (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2)) =
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {f}) := by
        rw [Multiset.map_map]
        exact (Multiset.map_congr rfl (fun I _ =>
          (hptfun I.1 I.2).choose_spec.choose_spec.2.symm)).trans
          (Multiset.attach_map_val _)
      rw [hMeq]
      exact hprodeq.symm
  -- the kernel of evaluation at a curve point is exactly the point ideal
  have hker : ∀ (x₀ y₀ : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x₀ y₀),
      RingHom.ker (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
        (x := x₀) (y := y₀) hE) =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C y₀) := by
    intro x₀ y₀ hE
    have hsurj : Function.Surjective
        (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          (x := x₀) (y := y₀) hE) := by
      intro a
      refine ⟨AdjoinRoot.mk _ (Polynomial.C (Polynomial.C a)), ?_⟩
      rw [AdjoinRoot.evalEval_mk]
      simp [Polynomial.evalEval]
    have hkermax : (RingHom.ker (AdjoinRoot.evalEval
        (p := Wb.toAffine.polynomial) (x := x₀) (y := y₀) hE)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ hsurj
    have hsub : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C y₀) ≤
        RingHom.ker (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          (x := x₀) (y := y₀) hE) := by
      rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
      rintro z (rfl | rfl) <;>
        rw [SetLike.mem_coe, RingHom.mem_ker]
      · show AdjoinRoot.evalEval hE (AdjoinRoot.mk _
          (Polynomial.C (Polynomial.X - Polynomial.C x₀))) = 0
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval]
      · show AdjoinRoot.evalEval hE (AdjoinRoot.mk _
          (Polynomial.X - Polynomial.C (Polynomial.C y₀))) = 0
        rw [AdjoinRoot.evalEval_mk]
        simp [Polynomial.evalEval]
    exact ((hXYmax x₀ y₀ hE).eq_of_le hkermax.ne_top hsub).symm
  -- the point determines the point ideal and conversely
  have hXYinj : ∀ (x₀ y₀ x₁ y₁ : (AlgebraicClosure (ZMod q))), Wb.toAffine.Equation x₀ y₀ →
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C y₀) =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₁
        (Polynomial.C y₁) →
      x₀ = x₁ ∧ y₀ = y₁ := by
    intro x₀ y₀ x₁ y₁ hE₀ hId
    have hX1 : WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine x₁ ∈
        RingHom.ker (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          (x := x₀) (y := y₀) hE₀) := by
      rw [hker x₀ y₀ hE₀, hId]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have hY1 : WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
        (Polynomial.C y₁) ∈
        RingHom.ker (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          (x := x₀) (y := y₀) hE₀) := by
      rw [hker x₀ y₀ hE₀, hId]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    rw [RingHom.mem_ker] at hX1 hY1
    constructor
    · rw [show WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine x₁ =
        AdjoinRoot.mk _ (Polynomial.C (Polynomial.X - Polynomial.C x₁))
        from rfl, AdjoinRoot.evalEval_mk] at hX1
      simp [Polynomial.evalEval] at hX1
      exact sub_eq_zero.mp (by simpa using hX1)
    · rw [show WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (Polynomial.C y₁) =
        AdjoinRoot.mk _ (Polynomial.X - Polynomial.C (Polynomial.C y₁))
        from rfl, AdjoinRoot.evalEval_mk] at hY1
      simp [Polynomial.evalEval] at hY1
      exact sub_eq_zero.mp (by simpa using hY1)
  -- nonvanishing off the divisor: a nonzero function does not vanish at any
  -- curve point outside its divisor
  have hoffdiv : ∀ (f : Wb.toAffine.CoordinateRing),
      ∀ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {f} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      ∀ (x₂ y₂ : (AlgebraicClosure (ZMod q))) (hE₂ : Wb.toAffine.Equation x₂ y₂), (x₂, y₂) ∉ D →
      AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE₂ f ≠ 0 := by
    intro f D hDeq hDfac x₂ y₂ hE₂ hQD h0
    have hfker : f ∈ RingHom.ker (AdjoinRoot.evalEval
        (p := Wb.toAffine.polynomial) hE₂) := h0
    rw [hker x₂ y₂ hE₂] at hfker
    have hdvd : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
        (Polynomial.C y₂) ∣
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod := by
      rw [← hDfac]
      exact Ideal.dvd_iff_le.mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr hfker)
    have hQnz : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
        (Polynomial.C y₂) ≠ ⊥ := by
      intro hb
      have hmem : WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          x₂ ∈ WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
            (Polynomial.C y₂) := Ideal.subset_span (Set.mem_insert _ _)
      rw [hb] at hmem
      exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
        (W' := Wb.toAffine) x₂ ((Submodule.mem_bot _).mp hmem)
    have hQprime : Prime (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        Wb.toAffine x₂ (Polynomial.C y₂)) :=
      (Ideal.prime_iff_isPrime hQnz).mpr (hXYmax x₂ y₂ hE₂).isPrime
    obtain ⟨I, hImem, hIdvd⟩ := hQprime.exists_mem_multiset_dvd hdvd
    obtain ⟨P, hPD, rfl⟩ := Multiset.mem_map.mp hImem
    have hPeq := (hXYmax P.1 P.2 (hDeq P hPD)).eq_of_le
      (hXYmax x₂ y₂ hE₂).ne_top (Ideal.le_of_dvd hIdvd)
    obtain ⟨hx, hy⟩ := hXYinj P.1 P.2 x₂ y₂ (hDeq P hPD) hPeq
    exact hQD (by rw [← hx, ← hy]; exact hPD)
  haveI : Module.Free (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing :=
    Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis
      Wb.toAffine)
  haveI : Module.Finite (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis
      Wb.toAffine)
  -- norms of ideal members stay in the ideal's contraction
  have hNle : ∀ I : Ideal Wb.toAffine.CoordinateRing,
      Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q))) I ≤
        I.comap (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing) := by
    intro I
    rw [Ideal.relNorm_apply, Ideal.span_le]
    rintro n ⟨z, hzI, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    obtain ⟨a, b, rfl⟩ :=
      WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
        (W' := Wb.toAffine) z
    rw [show Algebra.intNorm (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing = Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) from
      Algebra.intNorm_eq_norm (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing]
    rw [AdjoinRoot.algebraMap_eq,
      WeierstrassCurve.Affine.CoordinateRing.coe_norm_smul_basis]
    rw [map_mul]
    refine I.mul_mem_right _ ?_
    rw [show (AdjoinRoot.mk Wb.toAffine.polynomial)
        (Polynomial.C a + Polynomial.C b * Polynomial.X) =
      a • (1 : Wb.toAffine.CoordinateRing) +
        b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
          Polynomial.X from by
      rw [map_add, map_mul, Algebra.smul_def, Algebra.smul_def,
        AdjoinRoot.algebraMap_eq, mul_one]
      rfl]
    exact hzI
  -- THE NORM OF A POINT IDEAL IS ITS VERTICAL: relNorm of `XYIdeal x₀ (C y₀)`
  -- is `span {X - C x₀}` -- the ideal-theoretic pushforward of a point to
  -- its abscissa, with inertia degree one pinned by the conjugate product
  have hnormpt : ∀ (x₀ y₀ : (AlgebraicClosure (ZMod q))), Wb.toAffine.Nonsingular x₀ y₀ →
      Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q)))
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₀)) =
      Ideal.span {Polynomial.X - Polynomial.C x₀} := by
    intro x₀ y₀ hns
    have hE := hns.left
    have hEneg : Wb.toAffine.Equation x₀ (Wb.toAffine.negY x₀ y₀) :=
      (WeierstrassCurve.Affine.equation_neg x₀ y₀).mpr hE
    haveI hpmax : (Ideal.span {Polynomial.X - Polynomial.C x₀} :
        Ideal (Polynomial (AlgebraicClosure (ZMod q)))).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Polynomial.irreducible_X_sub_C x₀)
    -- the contraction of either fiber point ideal is the vertical
    have hcomapEq : ∀ y₁ : (AlgebraicClosure (ZMod q)), Wb.toAffine.Equation x₀ y₁ →
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₁)).comap (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
            Wb.toAffine.CoordinateRing) =
        Ideal.span {Polynomial.X - Polynomial.C x₀} := by
      intro y₁ hE₁
      haveI : ((WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₁)).comap (algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
            Wb.toAffine.CoordinateRing)).IsPrime :=
        Ideal.IsPrime.comap _ (hK := (hXYmax x₀ y₁ hE₁).isPrime)
      refine (hpmax.eq_of_le ‹Ideal.IsPrime _›.ne_top ?_).symm
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Ideal.mem_comap]
      exact Ideal.subset_span (Set.mem_insert _ _)
    haveI hlies : (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        x₀ (Polynomial.C y₀)).LiesOver
        (Ideal.span {Polynomial.X - Polynomial.C x₀}) :=
      ⟨(hcomapEq y₀ hE).symm⟩
    haveI hliesneg : (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        Wb.toAffine x₀ (Polynomial.C (Wb.toAffine.negY x₀ y₀))).LiesOver
        (Ideal.span {Polynomial.X - Polynomial.C x₀}) :=
      ⟨(hcomapEq _ hEneg).symm⟩
    obtain ⟨t, ht⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C (Wb.toAffine.negY x₀ y₀)))
      (Ideal.span {Polynomial.X - Polynomial.C x₀})
    obtain ⟨u, hu⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
        (Polynomial.C y₀))
      (Ideal.span {Polynomial.X - Polynomial.C x₀})
    -- the conjugate product is the extended vertical, of norm the square
    have hXid : Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q)))
        (WeierstrassCurve.Affine.CoordinateRing.XIdeal Wb.toAffine x₀) =
        Ideal.span {(Polynomial.X - Polynomial.C x₀) ^ 2} := by
      rw [show WeierstrassCurve.Affine.CoordinateRing.XIdeal Wb.toAffine x₀ =
        Ideal.span {algebraMap (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing (Polynomial.X - Polynomial.C x₀)}
        from rfl]
      rw [Ideal.relNorm_singleton]
      rw [show Algebra.intNorm (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing = Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) from
        Algebra.intNorm_eq_norm (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing]
      rw [Algebra.norm_algebraMap]
      rw [show Module.finrank (Polynomial (AlgebraicClosure (ZMod q)))
          Wb.toAffine.CoordinateRing = 2 from by
        rw [Module.finrank_eq_card_basis
          (WeierstrassCurve.Affine.CoordinateRing.basis Wb.toAffine)]
        simp]
    have hmul : Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q)))
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C (Wb.toAffine.negY x₀ y₀))) *
        Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q)))
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₀
          (Polynomial.C y₀)) =
        Ideal.span {(Polynomial.X - Polynomial.C x₀) ^ 2} := by
      rw [← hXid, ← map_mul,
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul hns]
    rw [ht, hu, ← pow_add, Ideal.span_singleton_pow] at hmul
    -- compare exponents through degrees of associated generators
    have hassoc := Ideal.span_singleton_eq_span_singleton.mp hmul
    have hXc0 : (Polynomial.X - Polynomial.C x₀ : Polynomial (AlgebraicClosure (ZMod q))) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero x₀
    have hd1 : t + u ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hassoc.dvd (pow_ne_zero _ hXc0)
      simpa [Polynomial.natDegree_pow] using this
    have hd2 : 2 ≤ t + u := by
      have := Polynomial.natDegree_le_of_dvd hassoc.symm.dvd
        (pow_ne_zero _ hXc0)
      simpa [Polynomial.natDegree_pow] using this
    -- neither exponent is zero: the relNorm sits inside the proper vertical
    have hu1 : u ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top] at hu
      have := hNle (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        Wb.toAffine x₀ (Polynomial.C y₀))
      rw [hu, hcomapEq y₀ hE, top_le_iff] at this
      exact hpmax.ne_top this
    have ht1 : t ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top] at ht
      have := hNle (WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        Wb.toAffine x₀ (Polynomial.C (Wb.toAffine.negY x₀ y₀)))
      rw [ht, hcomapEq _ hEneg, top_le_iff] at this
      exact hpmax.ne_top this
    have : u = 1 := by omega
    rw [hu, this, pow_one]
  -- the norm of a function factors over the verticals of its divisor
  have hNfac : ∀ (f : Wb.toAffine.CoordinateRing)
      (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {f} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      Ideal.span {Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) f} =
        (D.map (fun P => Ideal.span
          {Polynomial.X - Polynomial.C P.1})).prod := by
    intro f D hDeq hDfac
    have hrel := congrArg (Ideal.relNorm (Polynomial (AlgebraicClosure (ZMod q)))) hDfac
    rw [Ideal.relNorm_singleton, map_multiset_prod, Multiset.map_map] at hrel
    rw [show Algebra.intNorm (Polynomial (AlgebraicClosure (ZMod q)))
        Wb.toAffine.CoordinateRing f = Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) f from
      congrFun (congrArg DFunLike.coe (Algebra.intNorm_eq_norm
        (Polynomial (AlgebraicClosure (ZMod q))) Wb.toAffine.CoordinateRing)) f] at hrel
    rw [hrel]
    congr 1
    refine Multiset.map_congr rfl fun P hP => ?_
    exact hnormpt P.1 P.2
      ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp (hDeq P hP))
  -- abstract norm-evaluation: for any coordinate-ring element, the value of
  -- its norm at an abscissa is the product of its values on the fiber
  have hnormeval' : ∀ (f : Wb.toAffine.CoordinateRing) (c y : (AlgebraicClosure (ZMod q)))
      (hE : Wb.toAffine.Equation c y),
      AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE f *
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          ((WeierstrassCurve.Affine.equation_neg (W' := Wb.toAffine) c
            y).mpr hE) f =
      (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) f).eval c := by
    intro f c y hE
    obtain ⟨a, b, rfl⟩ :=
      WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
        (W' := Wb.toAffine) f
    rw [hnormeval a b c y hE]
    have hev : ∀ (y' : (AlgebraicClosure (ZMod q))) (hE' : Wb.toAffine.Equation c y'),
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE'
          (a • (1 : Wb.toAffine.CoordinateRing) +
            b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
              Polynomial.X) = a.eval c + b.eval c * y' := by
      intro y' hE'
      rw [show a • (1 : Wb.toAffine.CoordinateRing) +
          b • WeierstrassCurve.Affine.CoordinateRing.mk Wb.toAffine
            Polynomial.X =
        AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.C a + Polynomial.C b * Polynomial.X) from by
        rw [map_add, map_mul, Algebra.smul_def, Algebra.smul_def,
          AdjoinRoot.algebraMap_eq, mul_one]
        rfl]
      rw [AdjoinRoot.evalEval_mk]
      simp [Polynomial.evalEval]
    rw [hev y hE, hev _ ((WeierstrassCurve.Affine.equation_neg
      (W' := Wb.toAffine) c y).mpr hE)]
  -- products of vertical spans collapse to the span of the product
  have hspanprod : ∀ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
      (D.map (fun P => Ideal.span ({Polynomial.X - Polynomial.C P.1} :
        Set (Polynomial (AlgebraicClosure (ZMod q)))))).prod =
      Ideal.span {(D.map (fun P =>
        Polynomial.X - Polynomial.C P.1)).prod} := by
    intro D
    induction D using Multiset.induction_on with
    | empty => simp [Ideal.one_eq_top, Ideal.span_singleton_one]
    | cons P D ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.map_cons,
        Multiset.prod_cons, Ideal.span_singleton_mul_span_singleton]
  -- the norm IS a nonzero constant times the vertical product of the divisor
  have hNconst : ∀ (f : Wb.toAffine.CoordinateRing)
      (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {f} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      ∃ u : (AlgebraicClosure (ZMod q)), u ≠ 0 ∧
        Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) f =
          Polynomial.C u * (D.map (fun P =>
            Polynomial.X - Polynomial.C P.1)).prod := by
    intro f D hDeq hDfac
    have h1 := hNfac f D hDeq hDfac
    rw [hspanprod D] at h1
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp h1
    obtain ⟨u, huu, hCu⟩ := Polynomial.isUnit_iff.mp (v⁻¹ : _ˣ).isUnit
    refine ⟨u, huu.ne_zero, ?_⟩
    rw [mul_comm, hCu]
    rw [← hv, mul_assoc, Units.mul_inv, mul_one]
  -- VERTICAL WEIL RECIPROCITY (fiber-quotient form): for any function and
  -- any two abscissas, the fiber products of the function against the
  -- cross-evaluated vertical products agree -- both sides are the constant
  -- of `hNconst` times the symmetric double product
  have hrecfib : ∀ (f : Wb.toAffine.CoordinateRing)
      (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {f} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      ∀ (c₁ y₁ c₂ y₂ : (AlgebraicClosure (ZMod q))) (hE₁ : Wb.toAffine.Equation c₁ y₁)
        (hE₂ : Wb.toAffine.Equation c₂ y₂),
      (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE₁ f *
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          ((WeierstrassCurve.Affine.equation_neg (W' := Wb.toAffine) c₁
            y₁).mpr hE₁) f) *
        (D.map (fun P => c₂ - P.1)).prod =
      (AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE₂ f *
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial)
          ((WeierstrassCurve.Affine.equation_neg (W' := Wb.toAffine) c₂
            y₂).mpr hE₂) f) *
        (D.map (fun P => c₁ - P.1)).prod := by
    intro f D hDeq hDfac c₁ y₁ c₂ y₂ hE₁ hE₂
    obtain ⟨u, -, hNf⟩ := hNconst f D hDeq hDfac
    have hev : ∀ c : (AlgebraicClosure (ZMod q)), (Algebra.norm (Polynomial (AlgebraicClosure (ZMod q))) f).eval c =
        u * (D.map (fun P => c - P.1)).prod := by
      intro c
      rw [hNf, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_multiset_prod, Multiset.map_map]
      congr 2
      exact Multiset.map_congr rfl fun P _ => by simp
    rw [hnormeval' f c₁ y₁ hE₁, hnormeval' f c₂ y₂ hE₂, hev c₁, hev c₂]
    ring
  -- the norm of a line element is minus the fiber cubic of `hlinerec`
  have hNline : ∀ l n : (AlgebraicClosure (ZMod q)),
      Algebra.norm (Polynomial (AlgebraicClosure (ZMod q)))
        (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
          Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))) =
      -(Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n)) := by
    intro l n
    rw [show (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))) =
      (-(Polynomial.C l * Polynomial.X + Polynomial.C n)) •
        (1 : Wb.toAffine.CoordinateRing) +
        (1 : Polynomial (AlgebraicClosure (ZMod q))) • WeierstrassCurve.Affine.CoordinateRing.mk
          Wb.toAffine Polynomial.X from by
      rw [map_sub, Algebra.smul_def, Algebra.smul_def, map_one, one_mul,
        map_neg, AdjoinRoot.algebraMap_eq]
      rw [show ((AdjoinRoot.of Wb.toAffine.polynomial)
          (Polynomial.C l * Polynomial.X + Polynomial.C n)) =
        (AdjoinRoot.mk Wb.toAffine.polynomial)
          (Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))
        from rfl]
      ring]
    rw [WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
    simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_sub,
      map_ofNat]
    ring
  -- evaluations of the generator elements at curve points
  have hevline : ∀ (l n x y : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x y),
      AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE
        (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
          Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))) =
      y - (l * x + n) := by
    intro l n x y hE
    rw [AdjoinRoot.evalEval_mk]
    simp [Polynomial.evalEval]
  have hevvert : ∀ (c x y : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x y),
      AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine c) =
      x - c := by
    intro c x y hE
    rw [show WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine c =
      AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.C (Polynomial.X - Polynomial.C c)) from rfl,
      AdjoinRoot.evalEval_mk]
    simp [Polynomial.evalEval]
  -- a function vanishes at every point of its divisor
  have hondiv : ∀ (f : Wb.toAffine.CoordinateRing)
      (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      Ideal.span {f} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      ∀ P ∈ D, ∀ (hE : Wb.toAffine.Equation P.1 P.2),
      AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE f = 0 := by
    intro f D hDfac P hPD hE
    have hdvd : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        P.1 (Polynomial.C P.2) ∣ Ideal.span {f} := by
      rw [hDfac]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hPD)
    have hfmem : f ∈ WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        Wb.toAffine P.1 (Polynomial.C P.2) :=
      Ideal.le_of_dvd hdvd (Ideal.subset_span rfl)
    rw [← hker P.1 P.2 hE] at hfmem
    exact hfmem
  -- the abscissa multiset of a line's divisor is the root multiset of its
  -- fiber cubic
  have habs : ∀ (l n : (AlgebraicClosure (ZMod q))) (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {(AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n)))} =
        (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      D.map Prod.fst = (Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n)).roots
      := by
    intro l n D hDeq hDfac
    obtain ⟨u, hu0, hNf⟩ := hNconst _ D hDeq hDfac
    rw [hNline l n] at hNf
    -- compare leading coefficients: the cubic is monic, the product is monic
    have hmonprod : ((D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Polynomial.X -
        Polynomial.C P.1)).prod).Monic :=
      Polynomial.monic_multiset_prod_of_monic D
        (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Polynomial.X - Polynomial.C P.1)
        (fun P _ => Polynomial.monic_X_sub_C P.1)
    have hmoncub : (Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n)).Monic
      := by monicity!
    have hlc := congrArg Polynomial.leadingCoeff hNf
    rw [Polynomial.leadingCoeff_neg, hmoncub.leadingCoeff,
      Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hmonprod.leadingCoeff, mul_one] at hlc
    -- so u = -1 and the cubic IS the vertical product
    rw [← hlc] at hNf
    rw [show (Polynomial.C (-1 : (AlgebraicClosure (ZMod q)))) = -1 from by
      simp, neg_one_mul] at hNf
    have hprodeq := (neg_inj.mp hNf).symm
    rw [show (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        Polynomial.X - Polynomial.C P.1)) =
      (D.map Prod.fst).map (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        Prod.fst D).symm] at hprodeq
    rw [← hprodeq, Polynomial.roots_multiset_prod_X_sub_C]
  -- LINE-LINE WEIL RECIPROCITY in divisor form: the value product of line 1
  -- over the divisor of line 2 is MINUS that of line 2 over line 1
  have hrecline : ∀ (l₁ n₁ l₂ n₂ : (AlgebraicClosure (ZMod q))), l₁ ≠ l₂ →
      ∀ (D₁ D₂ : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D₁, Wb.toAffine.Equation P.1 P.2) →
      (∀ P ∈ D₂, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {(AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l₁ * Polynomial.X + Polynomial.C n₁)))} =
        (D₁.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      Ideal.span {(AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l₂ * Polynomial.X + Polynomial.C n₂)))} =
        (D₂.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      (D₂.map (fun P => P.2 - (l₁ * P.1 + n₁))).prod =
        - (D₁.map (fun P => P.2 - (l₂ * P.1 + n₂))).prod := by
    intro l₁ n₁ l₂ n₂ hl D₁ D₂ hDeq₁ hDeq₂ hfac₁ hfac₂
    -- points of each divisor satisfy their line's equation
    have hy : ∀ (l n : (AlgebraicClosure (ZMod q))) (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
        (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
        Ideal.span {(AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n)))} =
          (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2))).prod →
        ∀ P ∈ D, P.2 = l * P.1 + n := by
      intro l n D hDeq hfac P hP
      have h0 := hondiv _ D hfac P hP (hDeq P hP)
      rw [hevline l n P.1 P.2 (hDeq P hP)] at h0
      exact sub_eq_zero.mp h0
    -- rewrite both value products through the lines and the abscissas
    have hside : ∀ (la na lb nb : (AlgebraicClosure (ZMod q))) (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (hDeq : ∀ P ∈ D, Wb.toAffine.Equation P.1 P.2)
        (hyD : ∀ P ∈ D, P.2 = lb * P.1 + nb),
        (D.map (fun P => P.2 - (la * P.1 + na))).prod =
        ((D.map Prod.fst).map (fun x => (lb - la) * x + (nb - na))).prod := by
      intro la na lb nb D hDeq hyD
      rw [Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun P hP => ?_)
      rw [hyD P hP]
      show lb * P.1 + nb - (la * P.1 + na) = (lb - la) * P.1 + (nb - na)
      ring
    rw [hside l₁ n₁ l₂ n₂ D₂ hDeq₂ (hy l₂ n₂ D₂ hDeq₂ hfac₂),
      hside l₂ n₂ l₁ n₁ D₁ hDeq₁ (hy l₁ n₁ D₁ hDeq₁ hfac₁),
      habs l₁ n₁ D₁ hDeq₁ hfac₁, habs l₂ n₂ D₂ hDeq₂ hfac₂]
    exact hlinerec l₁ n₁ l₂ n₂ hl _ _ rfl rfl
  -- exact division along a span factorization: if span f = span a * J then
  -- f = a * g with span g = J
  have hdvdspan : ∀ (a f : Wb.toAffine.CoordinateRing)
      (J : Ideal Wb.toAffine.CoordinateRing), a ≠ 0 →
      Ideal.span {f} = Ideal.span {a} * J →
      ∃ g, f = a * g ∧ Ideal.span {g} = J := by
    intro a f J ha hfac
    have hmem : f ∈ Ideal.span ({a} : Set Wb.toAffine.CoordinateRing) := by
      have hle : Ideal.span {f} ≤ Ideal.span {a} := by
        rw [hfac]
        exact Ideal.mul_le_right
      exact hle (Ideal.subset_span rfl)
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
    refine ⟨g, hg, ?_⟩
    have hspanmul : Ideal.span ({a} : Set Wb.toAffine.CoordinateRing) *
        Ideal.span {g} = Ideal.span {a} * J := by
      rw [Ideal.span_singleton_mul_span_singleton, ← hg, hfac]
    exact mul_left_cancel₀ (by
      simpa [Ideal.span_singleton_eq_bot] using ha) hspanmul
  -- THE CLASS-GROUP DESCENT: every function whose span factors through point
  -- ideals equals a constant times a quotient of products of line elements
  -- and vertical elements (Miller reduction, by induction on divisor size)
  have hgenfac : ∀ (n : ℕ) (f : Wb.toAffine.CoordinateRing)
      (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))), D.card ≤ n →
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      Ideal.span {f} = (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      ∃ (Ln Ld : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) (Vn Vd : Multiset (AlgebraicClosure (ZMod q)))
        (u : (AlgebraicClosure (ZMod q))), u ≠ 0 ∧
        f * (Ld.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
          Polynomial.C P.2)))).prod * (Vd.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod =
        AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C u) *
          (Ln.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
        (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
          Polynomial.C P.2)))).prod * (Vn.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod := by
    intro n
    induction n with
    | zero =>
      intro f D hcard hDeq hDfac
      rw [Nat.le_zero, Multiset.card_eq_zero] at hcard
      subst hcard
      rw [Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top,
        Ideal.span_singleton_eq_top] at hDfac
      obtain ⟨c, hc0, hcu⟩ := hCunits f hDfac
      exact ⟨0, 0, 0, 0, c, hc0, by simp [hcu]⟩
    | succ n IH =>
      intro f D hcard hDeq hDfac
      by_cases hle : D.card ≤ n
      · exact IH f D hle hDeq hDfac
      · have hcards : D.card = n + 1 := le_antisymm hcard (not_le.mp hle)
        by_cases hone : D.card = 1
        · -- a single point ideal cannot be principal: its class is the
          -- nonzero class of an affine point
          exfalso
          obtain ⟨P, hDP⟩ := Multiset.card_eq_one.mp hone
          subst hDP
          have hEP : Wb.toAffine.Equation P.1 P.2 :=
            hDeq P (Multiset.mem_singleton_self P)
          have hnsP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
            hEP
          rw [Multiset.map_singleton, Multiset.prod_singleton] at hDfac
          have h1 : ClassGroup.mk Wb.toAffine.FunctionField
              (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hnsP) = 1 := by
            rw [ClassGroup.mk_eq_one_iff]
            rw [show ((WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hnsP :
              FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
                Wb.toAffine.FunctionField) :
              Submodule Wb.toAffine.CoordinateRing
                Wb.toAffine.FunctionField) =
              ((WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
                P.1 (Polynomial.C P.2) : Ideal Wb.toAffine.CoordinateRing) :
                FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
                  Wb.toAffine.FunctionField) from by
              rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq]]
            rw [← hDfac, FractionalIdeal.coeIdeal_span_singleton]
            exact ⟨⟨algebraMap _ _ f,
              FractionalIdeal.coe_spanSingleton _ _⟩⟩
          have h0 : WeierstrassCurve.Affine.Point.toClass
              (WeierstrassCurve.Affine.Point.some P.1 P.2 hnsP :
                Wb.toAffine.Point) = 0 := by
            rw [WeierstrassCurve.Affine.Point.toClass_some, h1]
            rfl
          have := (WeierstrassCurve.Affine.Point.toClass_eq_zero _).mp h0
          simp at this
        · -- at least two points: peel a pair by a vertical or a line
          have hne : D ≠ 0 := by
            intro h0
            rw [h0] at hcards
            simp at hcards
          obtain ⟨P, hP⟩ := Multiset.exists_mem_of_ne_zero hne
          have hD1 : P ::ₘ D.erase P = D := Multiset.cons_erase hP
          have hne1 : D.erase P ≠ 0 := by
            intro h0
            rw [← hD1, h0] at hone
            simp at hone
          obtain ⟨Q, hQ⟩ := Multiset.exists_mem_of_ne_zero hne1
          have hD2 : Q ::ₘ (D.erase P).erase Q = D.erase P :=
            Multiset.cons_erase hQ
          have hEP : Wb.toAffine.Equation P.1 P.2 := hDeq P hP
          have hEQ : Wb.toAffine.Equation Q.1 Q.2 :=
            hDeq Q (Multiset.mem_of_mem_erase hQ)
          have hDeq'' : ∀ T ∈ (D.erase P).erase Q,
              Wb.toAffine.Equation T.1 T.2 := fun T hT =>
            hDeq T (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hT))
          have hcard'' : ((D.erase P).erase Q).card = n - 1 := by
            have h1 := Multiset.card_erase_of_mem hQ
            have h2 := Multiset.card_erase_of_mem hP
            simp only [Nat.pred_eq_sub_one] at h1 h2
            omega
          have hprodD : (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod =
              WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
                P.1 (Polynomial.C P.2) *
              (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
                Q.1 (Polynomial.C Q.2) *
              (((D.erase P).erase Q).map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod) := by
            conv_lhs => rw [← hD1, ← hD2, Multiset.map_cons,
              Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
          by_cases hcase : P.1 = Q.1 ∧ P.2 = Wb.toAffine.negY Q.1 Q.2
          · -- vertical Miller move: P and Q are a conjugate fiber pair
            obtain ⟨hx, hy⟩ := hcase
            have hnsQ := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
              hEQ
            have hneg := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
              (W := Wb.toAffine) hnsQ
            have hfacv : Ideal.span {f} =
                Ideal.span {WeierstrassCurve.Affine.CoordinateRing.XClass
                  Wb.toAffine Q.1} *
                ((((D.erase P).erase Q)).map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              WeierstrassCurve.Affine.CoordinateRing.XYIdeal
                Wb.toAffine P.1 (Polynomial.C P.2))).prod := by
              rw [hDfac, hprodD, hx, hy, ← mul_assoc, hneg]
              rfl
            obtain ⟨g, hfg, hspang⟩ := hdvdspan _ f _
              (WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
                (W' := Wb.toAffine) Q.1) hfacv
            obtain ⟨Ln, Ld, Vn, Vd, u, hu0, heq⟩ := IH g _
              (by omega) hDeq'' hspang
            refine ⟨Ln, Ld, Q.1 ::ₘ Vn, Vd, u, hu0, ?_⟩
            rw [hfg, Multiset.map_cons, Multiset.prod_cons]
            linear_combination (WeierstrassCurve.Affine.CoordinateRing.XClass
              Wb.toAffine Q.1) * heq
          · -- line Miller move: peel P, Q through the line and push the sum
            have hnsP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
              hEP
            have hnsQ := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp
              hEQ
            have hnsS := WeierstrassCurve.Affine.nonsingular_add hnsP hnsQ
              hcase
            have hlineId := hline P.1 P.2 Q.1 Q.2 hnsP hnsQ hcase
            have hnegS := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
              (W := Wb.toAffine) hnsS
            have hn1 : n ≥ 1 := by omega
            have hfacl : Ideal.span {f *
                WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
                  (Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))} =
                Ideal.span {WeierstrassCurve.Affine.CoordinateRing.YClass
                  Wb.toAffine (WeierstrassCurve.Affine.linePolynomial P.1 P.2
                    (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))} *
                ((((Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)), (Wb.toAffine.addY P.1 Q.1 P.2 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))) ::ₘ ((D.erase P).erase Q)).map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              WeierstrassCurve.Affine.CoordinateRing.XYIdeal
                Wb.toAffine P.1 (Polynomial.C P.2))).prod
                := by
              rw [← Ideal.span_singleton_mul_span_singleton, hDfac, hprodD]
              rw [show (Ideal.span {WeierstrassCurve.Affine.CoordinateRing.XClass
                Wb.toAffine (Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))} : Ideal Wb.toAffine.CoordinateRing) =
                WeierstrassCurve.Affine.CoordinateRing.XIdeal Wb.toAffine
                  (Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)) from rfl, ← hnegS]
              rw [Multiset.map_cons, Multiset.prod_cons]
              rw [show (Ideal.span
                {WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
                  (WeierstrassCurve.Affine.linePolynomial P.1 P.2
                    (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))} :
                Ideal Wb.toAffine.CoordinateRing) =
                WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
                  (WeierstrassCurve.Affine.linePolynomial P.1 P.2
                    (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)) from rfl, hlineId]
              ring
            obtain ⟨h, hfg, hspanh⟩ := hdvdspan _ _ _
              (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
                (W' := Wb.toAffine) _) hfacl
            have hDeqS : ∀ T ∈ ((Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)), (Wb.toAffine.addY P.1 Q.1 P.2 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2))) ::ₘ ((D.erase P).erase Q),
                Wb.toAffine.Equation T.1 T.2 := by
              intro T hT
              rcases Multiset.mem_cons.mp hT with hTS | hTD
              · rw [hTS]
                exact hnsS.left
              · exact hDeq'' T hTD
            obtain ⟨Ln, Ld, Vn, Vd, u, hu0, heq⟩ := IH h _
              (by rw [Multiset.card_cons]; omega) hDeqS hspanh
            have hlelt : WeierstrassCurve.Affine.CoordinateRing.YClass
                Wb.toAffine (WeierstrassCurve.Affine.linePolynomial P.1 P.2
                  (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)) =
                AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
                  Polynomial.C (Polynomial.C (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * Polynomial.X +
                    Polynomial.C (P.2 - (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * P.1))) := by
              rw [show WeierstrassCurve.Affine.linePolynomial P.1 P.2 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) =
                Polynomial.C (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * Polynomial.X +
                  Polynomial.C (P.2 - (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * P.1) from by
                rw [WeierstrassCurve.Affine.linePolynomial]
                simp only [Polynomial.C_sub, Polynomial.C_mul]
                ring]
              rfl
            refine ⟨((Wb.toAffine.slope P.1 Q.1 P.2 Q.2), P.2 - (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * P.1) ::ₘ Ln, Ld, Vn,
              (Wb.toAffine.addX P.1 Q.1 (Wb.toAffine.slope P.1 Q.1 P.2 Q.2)) ::ₘ Vd, u, hu0, ?_⟩
            rw [hlelt] at hfg
            rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
              Multiset.prod_cons]
            linear_combination ((Ld.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                AdjoinRoot.mk Wb.toAffine.polynomial
                  (Polynomial.X - Polynomial.C (Polynomial.C P.1 *
                    Polynomial.X + Polynomial.C P.2)))).prod *
              (Vd.map (WeierstrassCurve.Affine.CoordinateRing.XClass
                Wb.toAffine)).prod) * hfg +
              (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
                Polynomial.C (Polynomial.C (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * Polynomial.X +
                  Polynomial.C (P.2 - (Wb.toAffine.slope P.1 Q.1 P.2 Q.2) * P.1)))) * heq
  -- every abscissa carries a fiber point (the fiber quadratic has a root)
  have hfiber : ∀ c : (AlgebraicClosure (ZMod q)), ∃ y : (AlgebraicClosure (ZMod q)), Wb.toAffine.Equation c y := by
    intro c
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
      (Wb.toAffine.polynomial.map (Polynomial.evalRingHom c)) (by
        rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero]
        · rw [WeierstrassCurve.Affine.degree_polynomial]
          norm_num
        · rw [show Wb.toAffine.polynomial.leadingCoeff =
            (1 : Polynomial (AlgebraicClosure (ZMod q))) from
            WeierstrassCurve.Affine.monic_polynomial]
          simp)
    refine ⟨y₀, ?_⟩
    rw [WeierstrassCurve.Affine.Equation]
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hy₀
    rw [show Wb.toAffine.polynomial.evalEval c y₀ =
      Wb.toAffine.polynomial.eval₂ (Polynomial.evalRingHom c) y₀ from
      (Polynomial.eval₂_evalRingHom c ▸ rfl)]
    exact hy₀
  -- the divisor witness of a vertical element
  have hvertdiv : ∀ c : (AlgebraicClosure (ZMod q)), ∃ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) ∧ D.card = 2 ∧
      (∀ P ∈ D, P.1 = c) ∧
      Ideal.span {WeierstrassCurve.Affine.CoordinateRing.XClass
        Wb.toAffine c} =
      (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine P.1
          (Polynomial.C P.2))).prod := by
    intro c
    obtain ⟨y, hy⟩ := hfiber c
    have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hy
    refine ⟨{(c, Wb.toAffine.negY c y), (c, y)}, ?_, rfl, ?_, ?_⟩
    · intro P hP
      rcases Multiset.mem_cons.mp hP with h | h
      · rw [h]
        exact (WeierstrassCurve.Affine.equation_neg c y).mpr hy
      · rw [Multiset.mem_singleton.mp h]
        exact hy
    · intro P hP
      rcases Multiset.mem_cons.mp hP with h | h
      · rw [h]
      · rw [Multiset.mem_singleton.mp h]
    · rw [show ({(c, Wb.toAffine.negY c y), (c, y)} :
        Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
        (c, Wb.toAffine.negY c y) ::ₘ {(c, y)} from rfl,
        Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton]
      exact (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
        (W := Wb.toAffine) hns).symm
  -- the divisor witness of a line element: points on the line, abscissas
  -- the roots of the fiber cubic
  have hlinediv : ∀ l n : (AlgebraicClosure (ZMod q)), ∃ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) ∧
      (∀ P ∈ D, P.2 = l * P.1 + n) ∧
      D.map Prod.fst = (Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n)).roots ∧
      Ideal.span {AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))} =
      (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine P.1
          (Polynomial.C P.2))).prod := by
    intro l n
    obtain ⟨D, hDeq, hDfac⟩ := hfactor
      (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n)))
      (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
        (W' := Wb.toAffine) (Polynomial.C l * Polynomial.X +
          Polynomial.C n))
    refine ⟨D, hDeq, ?_, habs l n D hDeq hDfac, hDfac⟩
    intro P hP
    have h0 := hondiv _ D hDfac P hP (hDeq P hP)
    rw [hevline l n P.1 P.2 (hDeq P hP)] at h0
    exact sub_eq_zero.mp h0
  -- explicit form of the line divisor: the roots of the fiber cubic paired
  -- with their ordinates on the line
  have hlinediv' : ∀ l n : (AlgebraicClosure (ZMod q)),
      Ideal.span {AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n))} =
      (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n)).roots.map (fun x => (x, l * x + n))).map
        (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine P.1
            (Polynomial.C P.2))).prod := by
    intro l n
    obtain ⟨D, hDeq, honline, hDfst, hDfac⟩ := hlinediv l n
    have hDrec : D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => (P.1, l * P.1 + n)) = D := by
      have hpt : ∀ P ∈ D, (fun P : (AlgebraicClosure (ZMod q)) ×
          (AlgebraicClosure (ZMod q)) => (P.1, l * P.1 + n)) P = id P := by
        intro P hP
        exact Prod.ext rfl (honline P hP).symm
      have h1 : D.map (fun P : (AlgebraicClosure (ZMod q)) ×
          (AlgebraicClosure (ZMod q)) => (P.1, l * P.1 + n)) =
          D.map id :=
        Multiset.map_congr rfl hpt
      exact h1.trans (Multiset.map_id D)
    have hkey : (Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 -
          Wb.toAffine.a₃ * n)).roots.map
        (fun x : (AlgebraicClosure (ZMod q)) => (x, l * x + n)) = D := by
      rw [← hDfst, Multiset.map_map]
      exact hDrec
    rw [hkey]
    exact hDfac
  -- generic facts about the fiber cubic: monic of degree three
  have hcubmon : ∀ l n : (AlgebraicClosure (ZMod q)), ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).Monic := by
    intro l n
    monicity!
  have hcubdeg : ∀ l n : (AlgebraicClosure (ZMod q)), ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).natDegree = 3 := by
    intro l n
    compute_degree!
  -- signed generator-pair reciprocity, line-line, UNCONDITIONAL: covers the
  -- generic-slope case (hlinerec), parallel lines, and identical lines
  have hggll : ∀ l₁ n₁ l₂ n₂ : (AlgebraicClosure (ZMod q)),
      (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₂ ^ 2 - Wb.toAffine.a₁ * l₂)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₂ * n₂ - Wb.toAffine.a₁ * n₂
            - Wb.toAffine.a₃ * l₂) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₂ ^ 2 - Wb.toAffine.a₃ * n₂))).roots.map
        (fun x => (l₂ * x + n₂) - (l₁ * x + n₁))).prod =
      - (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₁ ^ 2 - Wb.toAffine.a₁ * l₁)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₁ * n₁ - Wb.toAffine.a₁ * n₁
            - Wb.toAffine.a₃ * l₁) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₁ ^ 2 - Wb.toAffine.a₃ * n₁))).roots.map
        (fun x => (l₁ * x + n₁) - (l₂ * x + n₂))).prod := by
    intro l₁ n₁ l₂ n₂
    by_cases hl : l₁ = l₂
    · subst hl
      have hc1 : ∀ x : (AlgebraicClosure (ZMod q)), (l₁ * x + n₂) - (l₁ * x + n₁) = n₂ - n₁ := by
        intro x
        ring
      have hc2 : ∀ x : (AlgebraicClosure (ZMod q)), (l₁ * x + n₁) - (l₁ * x + n₂) = n₁ - n₂ := by
        intro x
        ring
      rw [Multiset.map_congr rfl (fun x _ => hc1 x),
        Multiset.map_congr rfl (fun x _ => hc2 x),
        Multiset.map_const', Multiset.prod_replicate,
        Multiset.map_const', Multiset.prod_replicate,
        hcard _, hcubdeg l₁ n₂, hcard _, hcubdeg l₁ n₁]
      ring
    · have h1 : ∀ x : (AlgebraicClosure (ZMod q)), (l₂ * x + n₂) - (l₁ * x + n₁) =
          (l₂ - l₁) * x + (n₂ - n₁) := by
        intro x
        ring
      have h2 : ∀ x : (AlgebraicClosure (ZMod q)), (l₁ * x + n₁) - (l₂ * x + n₂) =
          (l₁ - l₂) * x + (n₁ - n₂) := by
        intro x
        ring
      rw [Multiset.map_congr rfl (fun x _ => h1 x),
        Multiset.map_congr rfl (fun x _ => h2 x)]
      exact hlinerec l₁ n₁ l₂ n₂ hl _ _ rfl rfl
  -- signed generator-pair reciprocity, line-vertical (sign +1): the fiber
  -- product of the line equals the vertical product over the line divisor
  have hgglv : ∀ (l n c y : (AlgebraicClosure (ZMod q))), Wb.toAffine.Equation c y →
      (Wb.toAffine.negY c y - (l * c + n)) * (y - (l * c + n)) =
      (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots.map (fun x => x - c)).prod := by
    intro l n c y hE
    have hEneg := (WeierstrassCurve.Affine.equation_neg (W' := Wb.toAffine)
      c y).mpr hE
    have hL := hnormeval'
      (AdjoinRoot.mk Wb.toAffine.polynomial (Polynomial.X -
        Polynomial.C (Polynomial.C l * Polynomial.X + Polynomial.C n)))
      c y hE
    rw [hevline l n c y hE, hevline l n c _ hEneg, hNline l n] at hL
    rw [mul_comm, hL]
    have hroots : (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots.map (fun x => x - c)).prod =
        (-1) ^ 3 * (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots.map (fun x => c - x)).prod := by
      have hneg : ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots.map (fun x : (AlgebraicClosure (ZMod q)) => x - c) =
          (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
            - Wb.toAffine.a₃ * l) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots.map (fun x => c - x)).map Neg.neg := by
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl fun x _ => by simp
      rw [hneg, Multiset.prod_map_neg, Multiset.card_map, hcard _,
        hcubdeg l n]
    rw [hroots, ← hevalprod _ (hcubmon l n) c]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg]
    ring
  -- signed generator-pair reciprocity, vertical-vertical (sign +1): both
  -- sides are the constant square of the abscissa difference
  have hggvv : ∀ (c₁ c₂ : (AlgebraicClosure (ZMod q)))
      (D₁ D₂ : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      D₁.card = 2 → (∀ P ∈ D₁, P.1 = c₁) →
      D₂.card = 2 → (∀ P ∈ D₂, P.1 = c₂) →
      (D₂.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => P.1 - c₁)).prod =
      (D₁.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => P.1 - c₂)).prod := by
    intro c₁ c₂ D₁ D₂ h1card h1abs h2card h2abs
    have e2 : D₂.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => P.1 - c₁) =
        D₂.map (fun _ => c₂ - c₁) :=
      Multiset.map_congr rfl (fun P hP => by rw [h2abs P hP])
    have e1 : D₁.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => P.1 - c₂) =
        D₁.map (fun _ => c₁ - c₂) :=
      Multiset.map_congr rfl (fun P hP => by rw [h1abs P hP])
    rw [e1, e2, Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_const', Multiset.prod_replicate, h1card, h2card]
    ring
  -- canonical fiber ordinates
  obtain ⟨yfib, hyfib⟩ := Classical.axiomOfChoice hfiber
  -- vertical-vs-word reciprocity (sign +1): the vertical value product over
  -- a word's divisor equals the word's value product over the vertical fiber
  have hvw : ∀ (c : (AlgebraicClosure (ZMod q))) (L : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
      (V : Multiset (AlgebraicClosure (ZMod q))),
      (((L.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - c)).prod =
      ((({(c, Wb.toAffine.negY c (yfib c)), (c, yfib c)} :
          Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map (fun P =>
        (L.map (fun ln => P.2 - (ln.1 * P.1 + ln.2))).prod *
        (V.map (fun c' => P.1 - c')).prod))).prod := by
    intro c L V
    rw [Multiset.map_add, Multiset.prod_add]
    rw [show (({(c, Wb.toAffine.negY c (yfib c)), (c, yfib c)} :
        Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map (fun P =>
        (L.map (fun ln => P.2 - (ln.1 * P.1 + ln.2))).prod *
        (V.map (fun c' => P.1 - c')).prod)).prod =
      ((L.map (fun ln => Wb.toAffine.negY c (yfib c) -
          (ln.1 * c + ln.2))).prod *
        (V.map (fun c' => c - c')).prod) *
      ((L.map (fun ln => yfib c - (ln.1 * c + ln.2))).prod *
        (V.map (fun c' => c - c')).prod) from by
      rw [show ({(c, Wb.toAffine.negY c (yfib c)), (c, yfib c)} :
        Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
        (c, Wb.toAffine.negY c (yfib c)) ::ₘ {(c, yfib c)} from rfl,
        Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton]]
    have hLpart : ((L.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
        (fun x => (x, ln.1 * x + ln.2)))).map
          (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - c)).prod =
        (L.map (fun ln => (Wb.toAffine.negY c (yfib c) -
          (ln.1 * c + ln.2)) * (yfib c - (ln.1 * c + ln.2)))).prod := by
      rw [Multiset.map_bind, Multiset.prod_bind]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun ln _ => ?_)
      rw [Multiset.map_map]
      rw [show (((fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - c) ∘
          fun x => (x, ln.1 * x + ln.2))) = fun x => x - c from rfl]
      exact (hgglv ln.1 ln.2 c (yfib c) (hyfib c)).symm
    have hVpart : ((V.bind (fun c' => ({(c', Wb.toAffine.negY c'
        (yfib c')), (c', yfib c')} : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))))).map
          (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - c)).prod =
        (V.map (fun c' => (c - c') * (c - c'))).prod := by
      rw [Multiset.map_bind, Multiset.prod_bind]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun c' _ => ?_)
      rw [show ({(c', Wb.toAffine.negY c' (yfib c')), (c', yfib c')} :
        Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
        (c', Wb.toAffine.negY c' (yfib c')) ::ₘ {(c', yfib c')} from rfl,
        Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton]
      ring
    rw [hLpart, hVpart]
    rw [show (V.map (fun c' => (c - c') * (c - c'))).prod =
      (V.map (fun c' => c - c')).prod * (V.map (fun c' => c - c')).prod
      from by rw [← Multiset.prod_map_mul]]
    rw [show (L.map (fun ln => (Wb.toAffine.negY c (yfib c) -
        (ln.1 * c + ln.2)) * (yfib c - (ln.1 * c + ln.2)))).prod =
      (L.map (fun ln => Wb.toAffine.negY c (yfib c) -
        (ln.1 * c + ln.2))).prod *
      (L.map (fun ln => yfib c - (ln.1 * c + ln.2))).prod
      from by rw [← Multiset.prod_map_mul]]
    ring
  -- line-vs-word reciprocity (sign `(-1)^lines`): the line value product
  -- over a word's divisor against the word's value product over the line's
  -- divisor
  have hlw : ∀ (l₀ n₀ : (AlgebraicClosure (ZMod q))) (L : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
      (V : Multiset (AlgebraicClosure (ZMod q))),
      (((L.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀))).prod =
      (-1) ^ Multiset.card L *
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
          (L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod *
          (V.map (fun c' => x - c')).prod)).prod := by
    intro l₀ n₀ L V
    rw [Multiset.map_add, Multiset.prod_add]
    have hLpart : ((L.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
        (fun x => (x, ln.1 * x + ln.2)))).map
          (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀))).prod =
        (-1) ^ Multiset.card L * (L.map (fun ln =>
          (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
            (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod)).prod := by
      rw [Multiset.map_bind, Multiset.prod_bind]
      have h1 : ∀ ln ∈ L, ((((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀))).prod =
          (-1) * (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
            (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod := by
        intro ln _
        rw [Multiset.map_map]
        rw [show ((fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀)) ∘
          fun x => (x, ln.1 * x + ln.2)) =
          fun x => (ln.1 * x + ln.2) - (l₀ * x + n₀) from rfl]
        rw [hggll l₀ n₀ ln.1 ln.2]
        ring
      have h2 : L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          ((((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀))).prod) =
        L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          (-1) * (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
          (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod) :=
        Multiset.map_congr rfl h1
      rw [h2]
      rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    have hVpart : ((V.bind (fun c' => ({(c', Wb.toAffine.negY c'
        (yfib c')), (c', yfib c')} : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))))).map
          (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.2 - (l₀ * T.1 + n₀))).prod =
        (V.map (fun c' => (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map
          (fun x => x - c')).prod)).prod := by
      rw [Multiset.map_bind, Multiset.prod_bind]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun c' _ => ?_)
      rw [show ({(c', Wb.toAffine.negY c' (yfib c')), (c', yfib c')} :
        Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
        (c', Wb.toAffine.negY c' (yfib c')) ::ₘ {(c', yfib c')} from rfl,
        Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton]
      exact hgglv l₀ n₀ c' (yfib c') (hyfib c')
    rw [hLpart, hVpart]
    have hsplit : (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
        (L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod *
        (V.map (fun c' => x - c')).prod)).prod =
      (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
        (L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod)).prod *
      (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
        (V.map (fun c' => x - c')).prod)).prod := by
      rw [← Multiset.prod_map_mul]
    rw [hsplit]
    have hswapL : (L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
          (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod)).prod =
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
          (L.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => (l₀ * x + n₀) - (ln.1 * x + ln.2))).prod)).prod :=
      Multiset.prod_map_prod_map L ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots
    have hswapV : (V.map (fun c' =>
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x => x - c')).prod)).prod =
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots.map (fun x =>
          (V.map (fun c' => x - c')).prod)).prod :=
      Multiset.prod_map_prod_map V ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - l₀ ^ 2 - Wb.toAffine.a₁ * l₀)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * l₀ * n₀ - Wb.toAffine.a₁ * n₀
            - Wb.toAffine.a₃ * l₀) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - n₀ ^ 2 - Wb.toAffine.a₃ * n₀))).roots
    rw [hswapL, hswapV]
    ring
  -- word-vs-word reciprocity (sign `(-1)^(lines * lines)`): the value
  -- product of one line/vertical word over the other word's divisor,
  -- against the reverse product, assembled from `hlw` per line of the
  -- first word and `hvw` per vertical of the first word
  have hww : ∀ (L₁ L₂ : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
      (V₁ V₂ : Multiset (AlgebraicClosure (ZMod q))),
      (((L₂.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V₂.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                T.2 - (ab.1 * T.1 + ab.2))).prod *
              (V₁.map (fun cv => T.1 - cv)).prod)).prod =
      (-1) ^ (Multiset.card L₁ * Multiset.card L₂) *
        (((L₁.bind (fun ab => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ab.1 ^ 2 - Wb.toAffine.a₁ * ab.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ab.1 * ab.2 - Wb.toAffine.a₁ * ab.2
            - Wb.toAffine.a₃ * ab.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ab.2 ^ 2 - Wb.toAffine.a₃ * ab.2))).roots.map
          (fun x => (x, ab.1 * x + ab.2)))) +
        (V₁.bind (fun cv => {(cv, Wb.toAffine.negY cv (yfib cv)),
          (cv, yfib cv)}))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (L₂.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                T.2 - (ln.1 * T.1 + ln.2))).prod *
              (V₂.map (fun c' => T.1 - c')).prod)).prod := by
    intro L₁ L₂ V₁ V₂
    rw [Multiset.prod_map_mul]
    -- the `L₁`-line part over the second word's divisor, by `hlw` per line
    have hLpart : (((L₂.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V₂.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                T.2 - (ab.1 * T.1 + ab.2))).prod)).prod =
        (L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          (-1) ^ Multiset.card L₂ *
          (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ab.1 ^ 2 - Wb.toAffine.a₁ * ab.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ab.1 * ab.2 - Wb.toAffine.a₁ * ab.2
            - Wb.toAffine.a₃ * ab.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ab.2 ^ 2 - Wb.toAffine.a₃ * ab.2))).roots.map (fun x =>
            (L₂.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (ab.1 * x + ab.2) - (ln.1 * x + ln.2))).prod *
            (V₂.map (fun c' => x - c')).prod)).prod)).prod :=
      (Multiset.prod_map_prod_map _ L₁).trans (congrArg Multiset.prod
        (Multiset.map_congr rfl fun ab _ => hlw ab.1 ab.2 L₂ V₂))
    -- the `V₁`-vertical part over the second word's divisor, by `hvw`
    have hVpart : (((L₂.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V₂.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (V₁.map (fun cv => T.1 - cv)).prod)).prod =
        (V₁.map (fun cv => ((({(cv, Wb.toAffine.negY cv (yfib cv)), (cv, yfib cv)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map (fun P =>
          (L₂.map (fun ln => P.2 - (ln.1 * P.1 + ln.2))).prod *
          (V₂.map (fun c' => P.1 - c')).prod))).prod)).prod :=
      (Multiset.prod_map_prod_map _ V₁).trans (congrArg Multiset.prod
        (Multiset.map_congr rfl fun cv _ => hvw cv L₂ V₂))
    rw [hLpart, hVpart]
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    -- expand the first word's divisor on the right-hand side
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_bind, Multiset.prod_bind,
      Multiset.map_bind, Multiset.prod_bind]
    -- beta-reduce the per-line composite on the right-hand side
    have hRL : L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        ((((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ab.1 ^ 2 - Wb.toAffine.a₁ * ab.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ab.1 * ab.2 - Wb.toAffine.a₁ * ab.2
            - Wb.toAffine.a₃ * ab.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ab.2 ^ 2 - Wb.toAffine.a₃ * ab.2))).roots.map
          (fun x => (x, ab.1 * x + ab.2))).map
            (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (L₂.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                T.2 - (ln.1 * T.1 + ln.2))).prod *
              (V₂.map (fun c' => T.1 - c')).prod)).prod) =
      L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
        (((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ab.1 ^ 2 - Wb.toAffine.a₁ * ab.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ab.1 * ab.2 - Wb.toAffine.a₁ * ab.2
            - Wb.toAffine.a₃ * ab.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ab.2 ^ 2 - Wb.toAffine.a₃ * ab.2))).roots.map (fun x =>
            (L₂.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              (ab.1 * x + ab.2) - (ln.1 * x + ln.2))).prod *
            (V₂.map (fun c' => x - c')).prod)).prod) :=
      Multiset.map_congr rfl fun ab _ => by
        rw [Multiset.map_map]
        rfl
    rw [hRL]
    rw [mul_comm (Multiset.card L₁) (Multiset.card L₂), pow_mul]
    ring
  -- UNIQUENESS of the point divisor: equal products of point ideals force
  -- equal point multisets (prime picking + maximality + `hXYinj` +
  -- Dedekind cancellation)
  have hdivuniq : ∀ (D E : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
      (∀ P ∈ E, Wb.toAffine.Equation P.1 P.2) →
      (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod =
        (E.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod →
      D = E := by
    intro D
    induction D using Multiset.induction with
    | empty =>
      intro E _ hEeq h
      rw [Multiset.map_zero, Multiset.prod_zero] at h
      by_contra hne
      obtain ⟨Q, hQ⟩ := Multiset.exists_mem_of_ne_zero (fun h0 => hne h0.symm)
      obtain ⟨E', hE'⟩ := Multiset.exists_cons_of_mem (Multiset.mem_map_of_mem
        (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2)) hQ)
      have hle : (E.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod ≤
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine Q.1 (Polynomial.C Q.2) := by
        rw [hE', Multiset.prod_cons]
        exact Ideal.mul_le_right
      rw [← h] at hle
      exact (hXYmax Q.1 Q.2 (hEeq Q hQ)).ne_top (top_le_iff.mp (by
        rwa [Ideal.one_eq_top] at hle))
    | cons P D' IH =>
      intro E hDeq hEeq h
      have hEP : Wb.toAffine.Equation P.1 P.2 := hDeq P (Multiset.mem_cons_self P D')
      have hmaxP := hXYmax P.1 P.2 hEP
      have hle : (E.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod ≤
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine P.1 (Polynomial.C P.2) := by
        rw [← h, Multiset.map_cons, Multiset.prod_cons]
        exact Ideal.mul_le_right
      obtain ⟨Q, hQE, hQle⟩ := (hmaxP.isPrime.multiset_prod_map_le _).mp hle
      have hQeq := hEeq Q hQE
      have hQP : Q = P := by
        obtain ⟨h1, h2⟩ := hXYinj Q.1 Q.2 P.1 P.2 hQeq
          ((hXYmax Q.1 Q.2 hQeq).eq_of_le hmaxP.ne_top hQle)
        exact Prod.ext h1 h2
      obtain ⟨E', hE'⟩ := Multiset.exists_cons_of_mem hQE
      rw [hQP] at hE'
      have hne0 : WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          P.1 (Polynomial.C P.2) ≠ ⊥ := by
        intro hbot
        exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero
          (W' := Wb.toAffine) P.1 (Ideal.mem_bot.mp (hbot ▸ Ideal.subset_span
            (Set.mem_insert _ _)))
      have hcancel : ((D'.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod : Ideal Wb.toAffine.CoordinateRing) =
          (E'.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine P.1 (Polynomial.C P.2))).prod := by
        refine mul_left_cancel₀ hne0 ?_
        have h' := h
        rw [Multiset.map_cons, Multiset.prod_cons, hE', Multiset.map_cons,
          Multiset.prod_cons] at h'
        exact h'
      rw [hE', IH E' (fun T hT => hDeq T (Multiset.mem_cons_of_mem hT))
        (fun T hT => hEeq T (by rw [hE']; exact Multiset.mem_cons_of_mem hT))
        hcancel]
  -- explicit vertical divisor at the canonical fiber: the span of a
  -- vertical is the product of the two conjugate fiber point ideals
  have hvertdiv' : ∀ c : (AlgebraicClosure (ZMod q)),
      Ideal.span {WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine c} =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine c
          (Polynomial.C (Wb.toAffine.negY c (yfib c))) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine c
          (Polynomial.C (yfib c)) := by
    intro c
    have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (hyfib c)
    exact (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
      (W := Wb.toAffine) hns).symm
  -- the divisor of a WORD: the span of a product of line and vertical
  -- elements is the product of the point ideals over its explicit divisor
  have hworddiv : ∀ (L : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
      (V : Multiset (AlgebraicClosure (ZMod q))),
      Ideal.span {(L.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X + Polynomial.C P.2)))).prod *
        (V.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod} =
      (((L.bind (fun ln => ((Polynomial.X ^ 3
        + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
          * Polynomial.X ^ 2
        + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
            - Wb.toAffine.a₃ * ln.1) * Polynomial.X
        + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
          (fun x => (x, ln.1 * x + ln.2)))) +
        (V.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
          (c', yfib c')}))).map
            (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
              Wb.toAffine P.1 (Polynomial.C P.2))).prod := by
    intro L V
    rw [Multiset.map_add, Multiset.prod_add,
      ← Ideal.span_singleton_mul_span_singleton]
    congr 1
    · -- the line part, by induction through `hlinediv'`
      induction L using Multiset.induction with
      | empty => simp
      | cons ln L' IHL =>
        rw [Multiset.map_cons, Multiset.prod_cons,
          ← Ideal.span_singleton_mul_span_singleton, Multiset.cons_bind,
          Multiset.map_add, Multiset.prod_add, IHL, hlinediv' ln.1 ln.2]
    · -- the vertical part, by induction through `hvertdiv'`
      induction V using Multiset.induction with
      | empty => simp
      | cons c V' IHV =>
        rw [Multiset.map_cons, Multiset.prod_cons,
          ← Ideal.span_singleton_mul_span_singleton, Multiset.cons_bind,
          Multiset.map_add, Multiset.prod_add, IHV, hvertdiv' c,
          show ({(c, Wb.toAffine.negY c (yfib c)), (c, yfib c)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
            (c, Wb.toAffine.negY c (yfib c)) ::ₘ {(c, yfib c)} from rfl,
          Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
          Multiset.prod_singleton]
  sorry

set_option warn.sorry false in
/-- **The Weil pairing over a finite field, Frobenius-twisted form**
(DERIVED from `exists_weilPairing_mu` by discrete logarithm): on the
`p`-torsion of an elliptic curve over `𝔽_q` (`p ≠ q`) there is an
alternating, nondegenerate, `ZMod p`-bilinear pairing which the
`q`-power Frobenius scales by `q` — pick a primitive `p`-th root of
unity `ζ`; the `μ_p`-valued pairing reads through the discrete
logarithm base `ζ` as a `ZMod p`-valued pairing, and Frobenius
naturality `e(Fx,Fy) = e(x,y)^q` becomes multiplication by `q`. -/
theorem exists_weilPairing_frobenius (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hqp : q ≠ p) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p]
        (((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p] ZMod p),
      (∀ v, e v v = 0) ∧ (∃ x y, e x y ≠ 0) ∧
      ∀ x y, e (frobeniusTorsionEnd q Wbar p x)
          (frobeniusTorsionEnd q Wbar p y) = (q : ZMod p) * e x y := by
  classical
  obtain ⟨e₀, hbl, hbr, halt, hnd, hord, hfrob⟩ :=
    exists_weilPairing_mu q Wbar p hqp
  -- a primitive `p`-th root of unity in `𝔽̄_q`, at the unit level
  haveI : NeZero ((p : ℕ) : (AlgebraicClosure (ZMod q))) := by
    haveI : CharP (AlgebraicClosure (ZMod q)) q :=
      charP_of_injective_algebraMap
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
    exact ⟨CharP.cast_ne_zero_of_ne_of_prime (R := (AlgebraicClosure (ZMod q)))
      (Fact.out : p.Prime) hqp⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod q)) p
  have hζu : IsPrimitiveRoot (hζ.isUnit (Fact.out : p.Prime).ne_zero).unit p :=
    hζ.isUnit_unit (Fact.out : p.Prime).ne_zero
  -- the discrete logarithm on the `p`-th roots of unity
  set ζu : (AlgebraicClosure (ZMod q))ˣ := (hζ.isUnit (Fact.out : p.Prime).ne_zero).unit with hζudef
  have hmem : ∀ x y, e₀ x y ∈ Subgroup.zpowers ζu := by
    intro x y
    rw [hζu.zpowers_eq]
    exact (mem_rootsOfUnity p _).mpr (hord x y)
  set dlog : ∀ (x y : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p)), ZMod p :=
    fun x y => hζu.zmodEquivZPowers.symm
      (Additive.ofMul (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu))
    with hdlogdef
  -- the discrete logarithm is injective at the identity
  have hdlog0 : ∀ x y, dlog x y = 0 → e₀ x y = 1 := by
    intro x y h0
    have h1 : Additive.ofMul (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) =
        hζu.zmodEquivZPowers 0 := by
      rw [← h0]
      simp only [hdlogdef]
      exact (hζu.zmodEquivZPowers.apply_symm_apply _).symm
    rw [map_zero] at h1
    have h2 := congrArg (Subtype.val ∘ Additive.toMul) h1
    simpa using h2
  -- transfer of the pairing laws through the logarithm
  have hdadd_l : ∀ x y z, dlog (x + y) z = dlog x z + dlog y z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ (x + y) z, hmem (x + y) z⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x z, hmem x z⟩ : Subgroup.zpowers ζu) * ⟨e₀ y z, hmem y z⟩ :=
      Subtype.ext (hbl x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdadd_r : ∀ x y z, dlog x (y + z) = dlog x y + dlog x z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ x (y + z), hmem x (y + z)⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) * ⟨e₀ x z, hmem x z⟩ :=
      Subtype.ext (hbr x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdalt : ∀ x, dlog x x = 0 := by
    intro x
    simp only [hdlogdef]
    have hsub : (⟨e₀ x x, hmem x x⟩ : Subgroup.zpowers ζu) = 1 :=
      Subtype.ext (halt x)
    rw [hsub]
    rw [show Additive.ofMul (1 : Subgroup.zpowers ζu) = 0 from rfl, map_zero]
  have hdfrob : ∀ x y, dlog (frobeniusTorsionEnd q Wbar p x)
      (frobeniusTorsionEnd q Wbar p y) = (q : ZMod p) * dlog x y := by
    intro x y
    simp only [hdlogdef]
    have hval : e₀ (frobeniusTorsionEnd q Wbar p x)
        (frobeniusTorsionEnd q Wbar p y) = (e₀ x y) ^ q := by
      rw [hfrob]
      refine Units.ext ?_
      show frobAlgHom q ((e₀ x y : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q))) = (((e₀ x y) ^ q :
        (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q)))
      rw [Units.val_pow_eq_pow_val]
      rfl
    have hsub : (⟨e₀ (frobeniusTorsionEnd q Wbar p x)
        (frobeniusTorsionEnd q Wbar p y), hmem _ _⟩ :
        Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :=
      Subtype.ext (by
        show e₀ (frobeniusTorsionEnd q Wbar p x)
          (frobeniusTorsionEnd q Wbar p y) =
          ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :
            Subgroup.zpowers ζu).1
        rw [hval]
        rfl)
    refine Eq.trans (congrArg (fun g : Subgroup.zpowers ζu =>
      hζu.zmodEquivZPowers.symm (Additive.ofMul g)) hsub) ?_
    show hζu.zmodEquivZPowers.symm
      (Additive.ofMul ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q)) = _
    rw [ofMul_pow, map_nsmul, nsmul_eq_mul]
  -- right-zero law
  have hdzero_r : ∀ x, dlog x 0 = 0 := by
    intro x
    have h2 := hdadd_r x 0 0
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  have hdzero_l : ∀ y, dlog 0 y = 0 := by
    intro y
    have h2 := hdadd_l 0 0 y
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  -- the inner linear maps
  have heinner : ∀ x : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p), ∃ f : (((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p] ZMod p),
      ∀ y, f y = dlog x y := by
    intro x
    refine ⟨AddMonoidHom.toZModLinearMap p
      ⟨⟨dlog x, hdzero_r x⟩, hdadd_r x⟩, fun y => rfl⟩
  choose einner heinnerval using heinner
  -- the outer linear map
  have houter : ∃ e : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p] (((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p] ZMod p),
      ∀ x y, e x y = dlog x y := by
    refine ⟨AddMonoidHom.toZModLinearMap p
      ⟨⟨einner, ?_⟩, ?_⟩, fun x y => heinnerval x y⟩
    · refine LinearMap.ext fun y => ?_
      rw [heinnerval]
      exact hdzero_l y
    · intro x₁ x₂
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.add_apply, heinnerval, heinnerval, heinnerval]
      exact hdadd_l x₁ x₂ y
  obtain ⟨e, he⟩ := houter
  refine ⟨e, ?_, ?_, ?_⟩
  · intro v
    rw [he]
    exact hdalt v
  · -- nondegeneracy: some torsion point is nonzero, and pairs nontrivially
    have hcard : Nat.card ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p) = p ^ 2 := by
      haveI : CharP (AlgebraicClosure (ZMod q)) q :=
        charP_of_injective_algebraMap
          (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
      refine TorsionCard.card_torsionBy _ p ?_
      exact CharP.cast_ne_zero_of_ne_of_prime
        (R := (AlgebraicClosure (ZMod q))) (Fact.out : p.Prime) hqp
    haveI : Finite ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) :=
      Nat.finite_of_card_ne_zero (by
        rw [hcard]
        exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
    haveI : Nontrivial ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p) := by
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      rw [hcard]
      have := (Fact.out : p.Prime).two_le
      nlinarith
    obtain ⟨x, hx0⟩ := exists_ne (0 : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion p))
    obtain ⟨y, hy⟩ := hnd x hx0
    refine ⟨x, y, ?_⟩
    rw [he]
    intro h0
    exact hy (hdlog0 x y h0)
  · intro x y
    rw [he, he]
    exact hdfrob x y

/-- **The Frobenius determinant over a finite field** (DERIVED
2026-07-20 from the Weil pairing): the `q`-power Frobenius on the
`p`-torsion of an elliptic curve over `𝔽_q` (`p ≠ q`) has determinant
`q` — the Frobenius scales the Weil pairing by `q`, and on a
2-dimensional space an endomorphism scaling a nonzero alternating form
by `c` has determinant `c` (`det_eq_of_conj`). -/
theorem det_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hqp : q ≠ p) :
    LinearMap.det (frobeniusTorsionEnd q Wbar p) = (q : ZMod p) := by
  obtain ⟨e, halt, hnd, hconj⟩ := exists_weilPairing_frobenius q Wbar p hqp
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hpk : ((p : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro hz
    have h1 : q ∣ p :=
      (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q p).mp hz
    rcases (Nat.Prime.eq_one_or_self_of_dvd Fact.out q h1) with h2 | h2
    · exact Nat.Prime.one_lt (Fact.out : q.Prime) |>.ne' h2
    · exact hqp h2
  have hrank := WeierstrassCurve.p_torsion_rank
    (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) hpk
  exact det_eq_of_conj hrank e halt hnd hconj

set_option warn.sorry false in
/-- **Frobenius determinant at good primes** (sorry node): away from a
finite set `S` of places, the determinant of the mod-`p` representation
evaluates at the global arithmetic Frobenius of the prime `q` to
`q mod p`. Content: outside the (finitely many) places of bad reduction
and the residue characteristic, the `p`-torsion reduces injectively
(the Néron–Ogg–Shafarevich machinery of `GoodReduction.lean`), the
geometric Frobenius acts on the reduced torsion, and its determinant is
the degree `q` of the Frobenius isogeny — the classical
`det ρ̄(Frob_q) = q` of point counting/Weil. The mod-`p` cyclotomic
character takes the same value `q` at `Frob_q`
(`cyclotomicCharacterModL_globalFrob`, PROVEN), so by Chebotarev
density the two characters agree everywhere — which is how
`det_galoisRep_eq_cyclotomic` below consumes this node. -/
theorem det_galoisRep_globalFrob (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p) (hodd : Odd p) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        LinearMap.det
          (E.galoisRep p hppos
            (GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) : Module.End (ZMod p)
            ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)) =
        (q : ZMod p) := by
  obtain ⟨S, hS⟩ := exists_frobenius_reduction_model E p hppos hodd
  refine ⟨S, ?_⟩
  intro q hq hqS
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hqp, Wbar, hell, ψ, hψ⟩ := hS q hq hqS
  haveI := hell
  have hρ : (E.galoisRep p hppos
      (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) : Module.End (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)) =
      ψ.symm.conj (frobeniusTorsionEnd q Wbar p) := by
    apply LinearMap.ext
    intro x
    show _ = ψ.symm (frobeniusTorsionEnd q Wbar p (ψ.symm.symm x))
    rw [LinearEquiv.symm_symm, ← hψ x, LinearEquiv.symm_apply_apply]
  rw [hρ, LinearEquiv.conj_apply, LinearMap.comp_assoc]
  exact (LinearMap.det_conj (frobeniusTorsionEnd q Wbar p) ψ.symm).trans
    (det_frobeniusTorsionEnd q Wbar (p := p) hqp)

set_option backward.isDefEq.respectTransparency false in
/-- The mod-`p` cyclotomic character is the residue of the `p`-adic
cyclotomic character: `χ̄(σ) = toZMod (χ(σ))`. Both sides act on a
`p`-th root of unity by the same exponent (`cyclotomicCharacter.spec`
at level `1`, with the `toZMod = ringEquivCongr ∘ toZModPow 1` kernel
comparison), so `modularCyclotomicCharacter.unique` pins the modular
character to the residue value. -/
lemma cyclotomicCharacterModL_eq_toZMod (p : ℕ) [Fact p.Prime]
    (σ : Field.absoluteGaloisGroup ℚ) :
    ((GaloisRepresentation.cyclotomicCharacterModL p σ : (ZMod p)ˣ) :
        ZMod p) =
      PadicInt.toZMod
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv :
          ℤ_[p]ˣ) : ℤ_[p]) := by
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) p)
    _ (c := PadicInt.toZMod
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv :
        ℤ_[p]ˣ) : ℤ_[p])) ?_).symm
  intro t ht
  have ht1 : (t : AlgebraicClosure ℚ) ^ p ^ 1 = 1 := by
    rw [pow_one, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p t).mp ht,
      Units.val_one]
  have hspec := cyclotomicCharacter.spec p σ.toRingEquiv
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ht1
  have hval : (((cyclotomicCharacter (AlgebraicClosure ℚ) p
        σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).toZModPow 1).val =
      (PadicInt.toZMod ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val := by
    rw [GaloisRepresentation.toZMod_eq_ringEquivCongr_comp_toZModPow,
      RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, ZMod.ringEquivCongr_val]
  rw [hval] at hspec
  exact hspec

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The determinant of the mod-`p` Galois representation is the
cyclotomic character** (DERIVED 2026-07-17 from the Frobenius-det node
and Chebotarev density): `det ρ̄` and `χ̄` are continuous
conjugation-invariant `ZMod p`-valued functions on `Γ ℚ` that agree at
the global Frobenii of almost all primes (`det_galoisRep_globalFrob`
resp. `cyclotomicCharacterModL_globalFrob`), and the union of the
Frobenius conjugacy classes away from any finite set is dense
(`dense_conjClasses_globalFrob`), so the closed agreement set is
everything. Conversely `det ρ = χ` CONSTRUCTS the abstract Weil
pairing (the coordinate determinant form), which is how the tree
consumes it. -/
theorem det_galoisRep_eq_cyclotomic (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p) (hodd : Odd p)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det
      (E.galoisRep p hppos g : Module.End (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)) =
      algebraMap ℤ_[p] (ZMod p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) := by
  classical
  obtain ⟨S, hS⟩ := det_galoisRep_globalFrob E p hppos hodd
  set T := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p with hT
  set ρ := E.galoisRep p hppos with hρ
  set f₁ : Field.absoluteGaloisGroup ℚ → ZMod p :=
    fun σ => LinearMap.det (ρ σ : Module.End (ZMod p) T) with hf₁
  set f₂ : Field.absoluteGaloisGroup ℚ → ZMod p :=
    fun σ => ((GaloisRepresentation.cyclotomicCharacterModL p σ :
      (ZMod p)ˣ) : ZMod p) with hf₂
  -- `f₁` is multiplicative (determinant of a monoid hom into `End`)
  have hf₁mul : ∀ a b : Field.absoluteGaloisGroup ℚ,
      f₁ (a * b) = f₁ a * f₁ b := by
    intro a b
    show LinearMap.det (ρ (a * b) : Module.End (ZMod p) T) = _
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.det_comp]
  have hf₁one : f₁ 1 = 1 := by
    show LinearMap.det (ρ (1 : Field.absoluteGaloisGroup ℚ) :
      Module.End (ZMod p) T) = 1
    rw [map_one]
    exact LinearMap.det_id
  -- `f₁` is conjugation-invariant
  have hf₁conj : ∀ h x : Field.absoluteGaloisGroup ℚ,
      f₁ (h * x * h⁻¹) = f₁ x := by
    intro h x
    have h1 : f₁ (h * x * h⁻¹) * f₁ h = f₁ h * f₁ x := by
      rw [← hf₁mul, ← hf₁mul]
      congr 1
      group
    have h2 : f₁ (h * x * h⁻¹) * f₁ h = f₁ x * f₁ h := by
      rw [h1, mul_comm]
    have hunit : IsUnit (f₁ h) := by
      have hhh : f₁ h * f₁ h⁻¹ = 1 := by
        rw [← hf₁mul, mul_inv_cancel, hf₁one]
      exact ⟨⟨f₁ h, f₁ h⁻¹, hhh, by rw [mul_comm]; exact hhh⟩, rfl⟩
    exact hunit.mul_right_cancel h2
  -- `f₂` is conjugation-invariant (character into an abelian group)
  have hf₂conj : ∀ h x : Field.absoluteGaloisGroup ℚ,
      f₂ (h * x * h⁻¹) = f₂ x := by
    intro h x
    show ((GaloisRepresentation.cyclotomicCharacterModL p (h * x * h⁻¹) :
      (ZMod p)ˣ) : ZMod p) = _
    rw [map_mul, map_mul, map_inv, mul_comm, inv_mul_cancel_left]
  -- continuity of `f₁`: the endomorphism space is discrete
  have hcont1 : Continuous f₁ := by
    letI := moduleTopology (ZMod p) (Module.End (ZMod p) T)
    haveI : Finite T := WeierstrassCurve.n_torsion_finite _ hppos
    haveI : Finite (Module.End (ZMod p) T) :=
      Finite.of_injective (fun f => (f : T → T)) DFunLike.coe_injective
    haveI : Module.Finite (ZMod p) (Module.End (ZMod p) T) :=
      Module.Finite.of_finite
    haveI : DiscreteTopology (Module.End (ZMod p) T) :=
      GaloisRepresentation.discreteTopology_moduleTopology (ZMod p)
        (Module.End (ZMod p) T)
    have hcontρ : Continuous fun σ : Field.absoluteGaloisGroup ℚ =>
        (ρ σ : Module.End (ZMod p) T) :=
      ρ.continuous_toFun
    exact continuous_of_discreteTopology.comp hcontρ
  have hcont2 : Continuous f₂ :=
    GaloisRepresentation.continuous_cyclotomicCharacterModL p
  -- the agreement set is closed and contains the dense Frobenius classes
  have hclosed : IsClosed {x : Field.absoluteGaloisGroup ℚ | f₁ x = f₂ x} :=
    isClosed_eq hcont1 hcont2
  set S' : Finset (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ)) :=
    insert (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat S
    with hS'
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ), v ∉ S' ∧
        ∃ h : Field.absoluteGaloisGroup ℚ,
          x = h * GaloisRepresentation.globalFrob v * h⁻¹} ⊆
      {x : Field.absoluteGaloisGroup ℚ | f₁ x = f₂ x} := by
    rintro x ⟨v, hvS, h, rfl⟩
    obtain ⟨q, hq, rfl⟩ :=
      GaloisRepresentation.exists_prime_toHeightOneSpectrum v
    have hqp : q ≠ p := by
      rintro rfl
      exact hvS (Finset.mem_insert_self _ _)
    have hvS0 : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S :=
      fun hmem => hvS (Finset.mem_insert_of_mem hmem)
    show f₁ _ = f₂ _
    rw [hf₁conj, hf₂conj]
    have h1 : f₁ (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) = (q : ZMod p) :=
      hS q hq hvS0
    have h2 : f₂ (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) = (q : ZMod p) :=
      GaloisRepresentation.cyclotomicCharacterModL_globalFrob hq hqp
    rw [h1, h2]
  -- density closes the argument
  have hdense := GaloisRepresentation.dense_conjClasses_globalFrob
    (K := ℚ) S'
  have huniv : {x : Field.absoluteGaloisGroup ℚ | f₁ x = f₂ x} =
      Set.univ := by
    apply Set.eq_univ_of_univ_subset
    calc (Set.univ : Set (Field.absoluteGaloisGroup ℚ))
        = closure {x : Field.absoluteGaloisGroup ℚ |
            ∃ v : IsDedekindDomain.HeightOneSpectrum
              (NumberField.RingOfIntegers ℚ), v ∉ S' ∧
              ∃ h : Field.absoluteGaloisGroup ℚ,
                x = h * GaloisRepresentation.globalFrob v * h⁻¹} :=
          hdense.closure_eq.symm
      _ ⊆ closure {x : Field.absoluteGaloisGroup ℚ | f₁ x = f₂ x} :=
          closure_mono hsub
      _ = {x : Field.absoluteGaloisGroup ℚ | f₁ x = f₂ x} :=
          hclosed.closure_eq
  have hg : f₁ g = f₂ g := by
    have := Set.mem_univ g
    rw [← huniv] at this
    exact this
  show LinearMap.det (ρ g : Module.End (ZMod p) T) =
    algebraMap ℤ_[p] (ZMod p)
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv :
        ℤ_[p]ˣ) : ℤ_[p])
  rw [show (algebraMap ℤ_[p] (ZMod p) : ℤ_[p] →+* ZMod p) =
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p) from rfl]
  rw [← cyclotomicCharacterModL_eq_toZMod p g]
  exact hg

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The Weil pairing** (DERIVED 2026-07-17 from the determinant
node): on the `p`-torsion of an elliptic curve over `ℚ` there is an
alternating, nondegenerate, `ZMod p`-bilinear pairing which the
absolute Galois group scales by (the mod-`p` reduction of) the
cyclotomic character. Constructed as the coordinate determinant form
in a basis, which exists since `#E[p] = p²` (the torsion count) makes
the torsion a rank-`2` space; the Galois twist is the determinant of
the representation (`pairing_map_eq_det_smul`), which is the
cyclotomic character by the determinant node. -/
theorem exists_weilPairing (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hppos : 0 < p) (hodd : Odd p) :
    ∃ e : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p
        →ₗ[ZMod p] ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p
        →ₗ[ZMod p] ZMod p),
      (∀ v, e v v = 0) ∧ (∃ x y, e x y ≠ 0) ∧
      ∀ g x y, e (E.galoisRep p hppos g x) (E.galoisRep p hppos g y) =
        algebraMap ℤ_[p] (ZMod p)
          (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) * e x y := by
  classical
  have hp := (Fact.out : p.Prime)
  -- the torsion count gives rank 2
  have hcard : Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = p ^ 2 :=
    TorsionCard.card_torsionBy
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) p
      (Nat.cast_ne_zero.mpr hp.ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have := hp.pos
    positivity)
  haveI : Fintype ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    rw [ZMod.card] at h
    have h2 : p ^ 2 = p ^ Module.finrank (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h
    exact (Nat.pow_right_injective hp.two_le h2.symm)
  have hrank : Module.rank (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = 2 := by
    have := Module.finrank_eq_rank (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)
    rw [hfr] at this
    exact_mod_cast this.symm
  -- the coordinate determinant pairing
  let b : Module.Basis (Fin 2) (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Module.finBasisOfFinrankEq (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) hfr
  let e : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) →ₗ[ZMod p] ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) →ₗ[ZMod p] ZMod p :=
    LinearMap.mk₂ (ZMod p)
      (fun x y => b.coord 0 x * b.coord 1 y - b.coord 1 x * b.coord 0 y)
      (by intro m₁ m₂ n; simp only [map_add]; ring)
      (by intro c m n; simp only [map_smul, smul_eq_mul]; ring)
      (by intro m n₁ n₂; simp only [map_add]; ring)
      (by intro c m n; simp only [map_smul, smul_eq_mul]; ring)
  have halt : ∀ v, e v v = 0 := by
    intro v
    show b.coord 0 v * b.coord 1 v - b.coord 1 v * b.coord 0 v = 0
    ring
  refine ⟨e, halt, ⟨b 0, b 1, ?_⟩, ?_⟩
  · show b.coord 0 (b 0) * b.coord 1 (b 1) -
      b.coord 1 (b 0) * b.coord 0 (b 1) ≠ 0
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num [Finsupp.single_apply]
  · intro g x y
    rw [← det_galoisRep_eq_cyclotomic E p hppos hodd g]
    exact pairing_map_eq_det_smul hrank e halt
      (E.galoisRep p hppos g) x y

end WeilPairing
