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
public import Mathlib.LinearAlgebra.Determinant
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
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p) :
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
  sorry

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
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p) :
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
  obtain ⟨S, hS⟩ := exists_frobenius_reduction_model E p hppos
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
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det
      (E.galoisRep p hppos g : Module.End (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)) =
      algebraMap ℤ_[p] (ZMod p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) := by
  classical
  obtain ⟨S, hS⟩ := det_galoisRep_globalFrob E p hppos
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
    (p : ℕ) [Fact p.Prime] (hppos : 0 < p) :
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
    rw [← det_galoisRep_eq_cyclotomic E p hppos g]
    exact pairing_map_eq_det_smul hrank e halt
      (E.galoisRep p hppos g) x y

end WeilPairing

