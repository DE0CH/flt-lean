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
  -- Step 3c-v-e: assembly — reduce to a value-level equation and
  -- compute both sides on the point
  intro x
  refine Subtype.ext ?_
  -- the Galois action is the coordinatewise automorphism
  have hgalval : (E.galoisRep p hppos (GaloisRepresentation.globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat) x).1 =
      WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
        (AlgEquiv.toAlgHom (R := ℚ) (A₁ := AlgebraicClosure ℚ)
          (A₂ := AlgebraicClosure ℚ) (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))
        x.1 := rfl
  -- the left side unfolds to the composite of the layer values
  have hLv : ((((ψ₀.trans τ).trans redL).trans identL)
      (E.galoisRep p hppos (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) x)).1 =
      (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
        ((E.galoisRep p hppos (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) x)).1))))))) := rfl
  -- the right side is the coordinatewise `q`-power Frobenius of the
  -- composite value
  have hRv : ((frobeniusTorsionEnd q Wbar p)
      ((((ψ₀.trans τ).trans redL).trans identL) x)).1 =
      WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
        (frobAlgHom q)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt x.1)))))))) := rfl
  rw [hLv, hRv, hgalval]
  -- the point-level key equation, by cases on the point
  have hkey : ∀ (P : ((E.map (algebraMap ℚ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point),
      ((p : ℕ) : ℤ) • P = 0 →
      (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt
        (WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
          (AlgEquiv.toAlgHom (R := ℚ) (A₁ := AlgebraicClosure ℚ)
            (A₂ := AlgebraicClosure ℚ) (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) P)))))))) =
      WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
        (frobAlgHom q)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm) (imap
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq1)
        (edn.symm (redFun (eup (Pmap (hmodelPt P)))))))) := by
    intro P hP
    cases P with
    | zero =>
      have h1 : WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
          (AlgEquiv.toAlgHom (R := ℚ) (A₁ := AlgebraicClosure ℚ)
            (A₂ := AlgebraicClosure ℚ) (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat))
          (0 : ((E.map (algebraMap ℚ
            (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point) =
          (0 : ((E.map (algebraMap ℚ
            (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point) :=
        map_zero _
      have h2 : WeierstrassCurve.Affine.Point.map (W' := Wbar)
          (S := ZMod q) (frobAlgHom q)
          (0 : ((Wbar.map (algebraMap (ZMod q)
            (AlgebraicClosure (ZMod q))))⁄(AlgebraicClosure
            (ZMod q))).toAffine.Point) = 0 := map_zero _
      rw [show (WeierstrassCurve.Affine.Point.zero : ((E.map (algebraMap ℚ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).toAffine.Point) = 0
        from rfl, h1]
      rw [map_zero hmodelPt]
      rw [map_zero Pmap]
      rw [map_zero eup]
      rw [hred0]
      rw [map_zero edn.symm]
      rw [map_zero (WeierstrassCurve.Affine.Point.equivOfEq hEq1)]
      rw [map_zero imap]
      rw [map_zero (WeierstrassCurve.Affine.Point.equivOfEq hEq2.symm)]
      rw [h2]
      rfl
    | some a b hab =>
      sorry
  exact hkey x.1 ((Submodule.mem_torsionBy_iff _ _).mp x.2)

set_option warn.sorry false in
/-- **The Weil pairing over a finite field, Frobenius-twisted form**
(sorry node — the canonical arithmetic input): on the `p`-torsion of an
elliptic curve over `𝔽_q` (`p ≠ q`) there is an alternating,
nondegenerate, `ZMod p`-bilinear pairing which the `q`-power Frobenius
scales by `q`. This is the Weil pairing valued in `μ_p ⊂ 𝔽̄_q` — on
which the Frobenius acts by `ζ ↦ ζ^q` — read through any
identification `μ_p ≃ ZMod p`; Galois-equivariance of the pairing
becomes the `q`-scaling. -/
theorem exists_weilPairing_frobenius (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hqp : q ≠ p) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p]
        (((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion p) →ₗ[ZMod p] ZMod p),
      (∀ v, e v v = 0) ∧ (∃ x y, e x y ≠ 0) ∧
      ∀ x y, e (frobeniusTorsionEnd q Wbar p x)
          (frobeniusTorsionEnd q Wbar p y) = (q : ZMod p) * e x y :=
  sorry

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

