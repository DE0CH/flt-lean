/-
Lift.lean — own work for the Fermat project (not vendored from the FLT
project).

The decomposition of **B5** ("hardly ramified mod-ℓ with ℓ ≥ 5 is not
irreducible") following the FLT project's plan (Buzzard, 2026 EPSRC course,
Lecture 4):

* **B6a** (`exists_hardlyRamifiedLift`): an irreducible hardly ramified
  mod-`ℓ` representation lifts to a hardly ramified `ℓ`-adic representation
  over the integers `O` of a finite extension of `ℚ_ℓ`, compatibly with
  characteristic polynomials of Frobenius. The lift data is bundled in the
  structure `HardlyRamifiedLift`. DECOMPOSED (2026-07-22) into the
  Khare–Wintenberger-style core `exists_finite_lift` (sorry node: a lift
  over a module-finite local topological `ℤ_ℓ`-algebra `R` of
  characteristic zero, not necessarily a domain — mathematically the
  universal hardly-ramified deformation ring, finite over `ℤ_ℓ` by
  potential modularity and of dimension `≥ 1` by Galois-cohomological
  presentation counting) plus PROVEN commutative-algebra glue: quotient
  `R` by a prime lying over `(0) ⊆ ℤ_ℓ` and specialize (the
  specialization stability of `IsHardlyRamified` along the quotient and
  the framing is fully proven: `isFlatAt_baseChange_quotient`,
  `isTameAtTwo_baseChange`, `isHardlyRamified_baseChange_quotient`,
  `isHardlyRamified_conj`).

* **B6bc** (`residual_charFrob_eq`, sorry node): the residual
  characteristic polynomials of Frobenius of a liftable representation are
  those of `1 ⊕ χ̄` (i.e. `X² − (q+1)X + q` at `Frob_q`). Mathematically
  this is the composite of two further statements which a later layer must
  separate: the `ℓ`-adic lift spreads out into a weakly compatible family
  of hardly ramified `p`-adic representations over the completions of a
  number field (B6b, "spreading out" — provable *without* a residual
  modularity hypothesis, the 21st-century input), and any hardly ramified
  `3`-adic representation is an extension of the trivial character by the
  cyclotomic character (B6c), which pins the traces of the whole family.

* **Chebotarev–Brauer–Nesbitt** (`not_isIrreducible_of_charFrob_eq`, sorry
  node): a continuous mod-`ℓ` representation whose Frobenius characteristic
  polynomials away from `{2, 3, ℓ}` are those of `1 ⊕ χ̄` is not
  irreducible: the Frobenii are dense (Chebotarev), so all characteristic
  polynomials agree with those of `1 ⊕ χ̄`, and Brauer–Nesbitt forces the
  semisimplification to be `1 ⊕ χ̄`, which is reducible.

Given these, B5 is proven in `Reducible.lean`.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Family
public import Mathlib.Topology.Instances.ZMod
-- Chebotarev density, the mod-ℓ cyclotomic character, Brauer–Nesbitt and
-- the bridge lemmas, used in the proof of `not_isIrreducible_of_charFrob_eq`.
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange

@[expose] public section

open GaloisRepresentation Polynomial

namespace GaloisRepresentation

/-- The natural `ℤ_ℓ`-algebra structure on `ℤ/ℓℤ`. -/
noncomputable local instance (ℓ : ℕ) [Fact ℓ.Prime] : Algebra ℤ_[ℓ] (ZMod ℓ) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- The standard rank-2 free module `Fin 2 → O` has rank 2. -/
lemma rank_finTwoFun (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

variable {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
  {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
  [Module.Finite (ZMod ℓ) V] [Module.Free (ZMod ℓ) V]
  (hdim : Module.rank (ZMod ℓ) V = 2)

/-- The data of a hardly ramified `ℓ`-adic lift of a mod-`ℓ` representation
`ρbar`: a coefficient ring `O` (abstractly: the integers of a finite
extension of `ℚ_ℓ` — a compact topological local domain, finite over
`ℤ_ℓ`), a hardly ramified representation `ρ : Gal(ℚ̄/ℚ) → GL₂(O)`, and a
reduction map `π : O →+* ℤ/ℓℤ` matching the characteristic polynomials of
Frobenius of `ρ` with those of `ρbar` at all good primes. -/
structure HardlyRamifiedLift (ρbar : GaloisRep ℚ (ZMod ℓ) V) where
  /-- The coefficient ring of the lift. -/
  O : Type
  [commRing : CommRing O]
  [isDomain : IsDomain O]
  [topologicalSpace : TopologicalSpace O]
  [isTopologicalRing : IsTopologicalRing O]
  [isLocalRing : IsLocalRing O]
  [algebra : Algebra ℤ_[ℓ] O]
  [moduleFinite : Module.Finite ℤ_[ℓ] O]
  -- The topology is the `ℤ_ℓ`-module topology (true for the integers of a
  -- finite extension of `ℚ_ℓ`; added so the lift can be fed to the
  -- compatible-family layer `Family.lean`, whose statements require it).
  [isModuleTopology : IsModuleTopology ℤ_[ℓ] O]
  /-- The lifted representation, framed by the standard basis. -/
  ρ : FramedGaloisRep ℚ O (Fin 2)
  /-- The lift is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hℓOdd
    (rank_finTwoFun O) ρ
  /-- The reduction map to the residue characteristic-`ℓ` world. -/
  π : O →+* ZMod ℓ
  /-- The coefficient ring has characteristic zero: `ℤ_ℓ` embeds. (AUDIT
  STRENGTHENING 2026-07-22: true for the intended `O` — the integers of a
  finite extension of `ℚ_ℓ` — and recorded so that the downstream
  compatible-family layer, whose coefficient rings must embed into `ℚ̄_ℓ`,
  can consume it; without it the structure would be satisfiable by
  `O = ℤ/ℓℤ` itself, trivializing the lift.) -/
  algebraMap_injective : Function.Injective (algebraMap ℤ_[ℓ] O)
  /-- The lift reduces to `ρbar`: the characteristic polynomials of
  Frobenius match at every prime `q ∉ {2, ℓ}`. -/
  charFrob_compat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

set_option backward.isDefEq.respectTransparency false in
/-- Any number field embeds into the algebraic closure of `ℚ_p` — the
coefficient field of a compatible family can be evaluated at every prime
(an ingredient of the proof of `residual_charFrob_eq_of_family`, where
the `3`-adic member of the family is extracted). The target is an
algebraically closed field of characteristic zero, so `IsAlgClosed.lift`
applies to the algebraic extension `E/ℚ`. -/
lemma nonempty_ringHom_to_padicAlgClosure
    (E : Type*) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] :
    Nonempty (E →+* AlgebraicClosure ℚ_[p]) := by
  haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := E)
    (M := AlgebraicClosure ℚ_[p])).toRingHom⟩

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- Characteristic-polynomial transport through base change and framing:
the family-membership equation `(τ.baseChange B).conj e = σ_φ` identifies
the characteristic polynomials of the family member with the images of
those of `τ` under the coefficient map. (Ingredient of the proof of
`residual_charFrob_eq_of_family`.) -/
lemma charpoly_baseChange_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep ℚ A W) (e : (B ⊗[A] W) ≃ₗ[B] N)
    (g : Field.absoluteGaloisGroup ℚ) :
    (((τ.baseChange B).conj e) g).charpoly =
      ((τ g).charpoly).map (algebraMap A B) := by
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom A B W) (τ g)).charpoly = _
  rw [show (Module.End.baseChangeHom A B W) (τ g) =
    LinearMap.baseChange B (τ g) from rfl, LinearMap.charpoly_baseChange]

/-- **B6a-core** (sorry node): the Khare–Wintenberger-style lifting core.
An irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5` lifts to
a hardly ramified representation over *some* coefficient ring `R` — a local
topological `ℤ_ℓ`-algebra, finite as a `ℤ_ℓ`-module, carrying the
`ℤ_ℓ`-module topology, of characteristic zero (`ℤ_ℓ` embeds) — with a
reduction map matching the characteristic polynomials of Frobenius of
`ρbar` at all good primes. `R` is *not* required to be a domain.

Mathematically `R` is the universal deformation ring of `ρbar` for the
hardly ramified deformation problem (representable since `ρbar` is
irreducible: Schur's lemma plus Mazur's criterion), and the two deep
inputs pinning it down are:

* a presentation `R ≅ ℤ_ℓ[[x₁,…,x_g]]/(f₁,…,f_r)` with `g − r ≥ 1`, from
  the global Euler characteristic formula and Poitou–Tate duality with
  balanced local conditions (Mazur; Böckle) — since a complete local
  Noetherian `ℤ_ℓ`-algebra presented with more generators than relations
  has Krull dimension `≥ 1`, this forces a characteristic-zero fiber,
  i.e. the injectivity clause below once `R` is known to be `ℤ_ℓ`-finite;
* finiteness of `R` as a `ℤ_ℓ`-module — the potential-modularity /
  Taylor–Wiles–Kisin input (the residual-modularity hypothesis is bypassed
  via Moret-Bailly, following Taylor and Khare–Wintenberger).

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4; Böckle's appendix to Khare's *Serre's conjecture* notes;
Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem exists_finite_lift (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (R : Type) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLocalRing R) (_ : Algebra ℤ_[ℓ] R)
      (_ : Module.Finite ℤ_[ℓ] R) (_ : IsModuleTopology ℤ_[ℓ] R),
      Function.Injective (algebraMap ℤ_[ℓ] R) ∧
      ∃ ρ : FramedGaloisRep ℚ R (Fin 2),
        IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ ∧
        ∃ π : R →+* ZMod ℓ, ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
          (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
            ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness transfers along quotient specialization** (PROVEN
2026-07-22, mirroring the residue-field transfer
`IsHardlyRamified.isFlatAt_baseChange_residue` of `Threeadic.lean`): if
`ρ` is flat at `ℓ`, so is its base change to a quotient `R ⧸ P` of the
coefficient ring. The open ideals of `R ⧸ P` correspond to the open
ideals `J ⊇ P` of `R` (preimages along the continuous quotient map are
open), the double base change `((R ⧸ P) ⧸ I) ⊗ ((R ⧸ P) ⊗ M)` collapses
equivariantly to `(R ⧸ J) ⊗ M` (tensor cancellation
`AlgebraTensorModule.cancelBaseChange` plus the double-quotient
isomorphism `DoubleQuot.quotQuotEquivQuotOfLE` along
`I = J.map (Ideal.Quotient.mk P)`), and
`HasFlatProlongationAt.of_equiv` transports the Hopf-algebra witness. -/
theorem isFlatAt_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    {ρ : GaloisRep ℚ R M}
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))) :
    (ρ.baseChange (R ⧸ P)).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) := by
  constructor
  intro I hI
  -- the corresponding open ideal of `R`, lying over `P`
  let J : Ideal R := I.comap (Ideal.Quotient.mk P)
  have hPJ : P ≤ J := fun x hx => by
    show Ideal.Quotient.mk P x ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact I.zero_mem
  have hImap : I = J.map (Ideal.Quotient.mk P) :=
    (Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective I).symm
  have hJopen : IsOpen (J : Set R) := by
    have hpre : (J : Set R) =
        (Ideal.Quotient.mk P) ⁻¹' (I : Set (R ⧸ P)) := rfl
    rw [hpre]
    exact hI.preimage (QuotientRing.isOpenQuotientMap_mk P).continuous
  -- the coefficient identification `((R ⧸ P) ⧸ I) ≃+* R ⧸ J`
  let φ : ((R ⧸ P) ⧸ I) ≃+* (R ⧸ J) :=
    (Ideal.quotEquivOfEq hImap).trans (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
  have hφalg : ∀ r : R,
      φ (algebraMap R ((R ⧸ P) ⧸ I) r) = algebraMap R (R ⧸ J) r := by
    intro r
    show (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
        ((Ideal.quotEquivOfEq hImap)
          (Ideal.Quotient.mk I (Ideal.Quotient.mk P r))) =
      Ideal.Quotient.mk J r
    rw [Ideal.quotEquivOfEq_mk]
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hPJ
  -- its `R`-linear form
  let φlin : ((R ⧸ P) ⧸ I) ≃ₗ[R] (R ⧸ J) :=
    { φ.toAddEquiv with
      map_smul' := fun r x => by
        show φ (r • x) = r • φ x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφalg] }
  -- assemble: cancel the middle base change, then transport coefficients
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ P)
    ((R ⧸ P) ⧸ I) ((R ⧸ P) ⧸ I) M
  let e₂ := TensorProduct.congr φlin (LinearEquiv.refl R M)
  let eSp : ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space ≃+
      ((ρ.baseChange (R ⧸ J)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space) :=
    e₁.toAddEquiv.trans e₂.toAddEquiv
  have he : ∀ (g : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))))
      (x : (((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space),
      eSp (g • x) = g • eSp x := by
    intro g x
    show (e₁.toAddEquiv.trans e₂.toAddEquiv)
        ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      ((ρ.baseChange (R ⧸ J)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((e₁.toAddEquiv.trans e₂.toAddEquiv) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero =>
        rw [show (c ⊗ₜ[R ⧸ P] (0 : (R ⧸ P) ⊗[R] M)) =
          (0 : ((R ⧸ P) ⧸ I) ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] M)) from
          TensorProduct.tmul_zero _ _]
        simp
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        simp only [map_add, ha, hb]
      | tmul d m => rfl
  refine (hflat.cond J hJopen).of_equiv _ eSp.symm ?_
  intro g x
  apply eSp.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Tameness at `2` transfers along base change** (generalization of the
proven residue-field transfer `IsHardlyRamified.isTameAtTwo_baseChange_residue`
in `Threeadic.lean` from finite residue fields to arbitrary topological
coefficient algebras `B`, same proof): the rank-1 tame quadratic quotient
`(π, δ)` of `ρ` at `2` base-changes to `(rid ∘ (π ⊗ 1), (δ ⊗ 1)ᵉ)` for
`ρ ⊗ B`. -/
lemma isTameAtTwo_baseChange {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B]
    {ρ : GaloisRep ℚ R M}
    (htame : ∃ (π : M →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : M,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (B ⊗[R] M) →ₗ[B] B) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] B B),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : B ⊗[R] M,
        π ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  obtain ⟨π, hπsurj, δ, h⟩ := htame
  -- the canonical identification `B ⊗[R] R ≃ₗ[B] B`
  let e : (B ⊗[R] R) ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid R B B
  -- the base-changed projection and character
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange B π, ?_,
    (δ.baseChange B).conj e, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · intro g w
    refine ⟨?_, ?_, ?_⟩
    · -- equivariance, by linearity on simple tensors
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have h1 := (h g v).1
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [show ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2])) g (c ⊗ₜ v) =
          c ⊗ₜ ((ρ.map (algebraMap ℚ ℚ_[2])) g v) from rfl,
          LinearMap.baseChange_tmul, h1,
          GaloisRep.conj_apply, LinearMap.baseChange_tmul]
        rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.rid_symm_apply,
          show ((δ.baseChange B) g : Module.End B (B ⊗[R] R)) =
            LinearMap.baseChange B (δ g) from rfl,
          LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [show (δ g) (π v) = π v • (δ g) 1 from by
          conv_lhs => rw [show (π v : R) = π v • (1 : R) from by
            rw [smul_eq_mul, mul_one]]
          rw [map_smul]]
        simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
          mul_comm]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    · -- unramifiedness: the kernel only grows under base change + conj
      intro σ hσ
      have hδσ : δ σ = 1 := (h 1 0).2.1 hσ
      have : (δ.baseChange B).conj e σ = 1 := by
        rw [GaloisRep.conj_apply]
        rw [show (δ.baseChange B) σ =
          LinearMap.baseChange B (δ σ) from rfl, hδσ]
        refine LinearMap.ext fun c => ?_
        simp
      exact this
    · -- the quadratic condition transfers through the monoid hom
      intro g'
      have hsq : δ g' * δ g' = 1 := (h 1 0).2.2 g'
      calc (δ.baseChange B).conj e g' * (δ.baseChange B).conj e g'
          = (δ.baseChange B).conj e (g' * g') := (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply]
            rw [show (δ.baseChange B) (g' * g') =
              LinearMap.baseChange B (δ (g' * g')) from rfl,
              map_mul δ, hsq]
            refine LinearMap.ext fun c => ?_
            simp

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along quotient specialization of the
coefficients** (DERIVED 2026-07-22, mirroring the proven residue-field
transfer `exists_residual_isHardlyRamified` of `Threeadic.lean`): the
determinant condition maps along `R → R ⧸ P` (`LinearMap.det_baseChange`),
unramifiedness passes to any base change (existing instance), tameness at
`2` and flatness at `ℓ` by the proven transfers above. -/
lemma isHardlyRamified_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] {hdimM : Module.rank R M = 2}
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    (hdimQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ) :
    IsHardlyRamified hℓOdd hdimQ (ρ.baseChange (R ⧸ P)) := by
  constructor
  · -- the determinant condition maps along the quotient map
    intro g
    have hdet : (ρ.baseChange (R ⧸ P)).det g =
        algebraMap R (R ⧸ P) (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange (R ⧸ P)) g) = _
      rw [show ((ρ.baseChange (R ⧸ P)) g :
          Module.End (R ⧸ P) ((R ⧸ P) ⊗[R] M)) =
        LinearMap.baseChange (R ⧸ P) (ρ g) from rfl,
        LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro p hp hpp
    letI : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      h.isUnramified p hp hpp
    infer_instance
  · -- flatness at ℓ (sorried transfer leaf)
    exact isFlatAt_baseChange_quotient P h.isFlat
  · -- tameness at 2 (proven transfer)
    exact isTameAtTwo_baseChange (R ⧸ P) h.isTameAtTwo

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along conjugation** by a linear
isomorphism of the representation space (PROVEN 2026-07-22): the
determinant is conjugation-invariant, the kernels of the local
representations only grow, flatness transports through
`HasFlatProlongationAt.of_equiv` along the base-changed isomorphism, and
the tame quadratic quotient is composed with the inverse isomorphism. -/
lemma isHardlyRamified_conj {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsHardlyRamified hℓOdd hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness: the kernel of the local representation only grows
    intro p hp hpp
    have hun := h.isUnramified p hp hpp
    refine ⟨le_trans hun.localInertiaGroup_le ?_⟩
    intro σ hσ
    have h1 : ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 := hσ
    show (ρ.conj e).toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1
    rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
      ← GaloisRep.toLocal_apply, h1]
    refine LinearMap.ext fun w => ?_
    simp
  · -- flatness: transport along the base-changed equivariant isomorphism
    constructor
    intro I hI
    refine (h.isFlat.cond I hI).of_equiv _
      (LinearEquiv.baseChange R (R ⧸ I) M N e).toAddEquiv ?_
    intro g x
    show (LinearEquiv.baseChange R (R ⧸ I) M N e)
        (((ρ.baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      (((ρ.conj e).baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((LinearEquiv.baseChange R (R ⧸ I) M N e) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
        LinearEquiv.baseChange_tmul, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · -- tameness at 2: compose the quotient with the inverse isomorphism
    obtain ⟨π, hπsurj, δ, hδ⟩ := h.isTameAtTwo
    refine ⟨π.comp (e.symm : N →ₗ[R] M), ?_, δ, ?_⟩
    · intro r
      obtain ⟨m, hm⟩ := hπsurj r
      exact ⟨e m, by simp [hm]⟩
    · intro g w
      refine ⟨?_, (hδ 1 0).2.1, (hδ 1 0).2.2⟩
      have h1 := (hδ g (e.symm w)).1
      show π (e.symm ((ρ.conj e).map (algebraMap ℚ ℚ_[2]) g w)) =
        δ g (π (e.symm w))
      rw [GaloisRep.map_apply, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        ← GaloisRep.map_apply, h1]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **B6a**: an irreducible hardly ramified mod-`ℓ` representation with
`ℓ ≥ 5` admits a hardly ramified `ℓ`-adic lift over a characteristic-zero
local topological domain finite over `ℤ_ℓ`.

DERIVED (2026-07-22) from the Khare–Wintenberger core `exists_finite_lift`
by commutative algebra: `ℓ` is not nilpotent in `R` (characteristic-zero
injectivity), so some prime `P` of `R` avoids it, and — every nonzero
element of `ℤ_ℓ` being a unit times a power of `ℓ` — `P` lies over
`(0) ⊆ ℤ_ℓ`. The quotient `O := R ⧸ P` is then a characteristic-zero
local topological domain, finite over `ℤ_ℓ` with the `ℤ_ℓ`-module
topology; the reduction map factors through it (`P ⊆ 𝔪 = ker π`, the
kernel being maximal because `R/ker π` is a finite domain), and the
characteristic polynomials of Frobenius transport through the
specialization by `charpoly_baseChange_conj`. The specialization
stability of `IsHardlyRamified` along `R → R ⧸ P` is PROVEN by
`isHardlyRamified_baseChange_quotient` + `isHardlyRamified_conj` above,
so this derivation is sorry-free modulo `exists_finite_lift`. -/
theorem exists_hardlyRamifiedLift (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    Nonempty (HardlyRamifiedLift hℓOdd ρbar) := by
  classical
  obtain ⟨R, iR1, iR2, iR3, iR4, iR5, iR6, iR7, hinj, ρR, hρR, πR, hπR⟩ :=
    exists_finite_lift hℓOdd hdim hℓ5 h hirr
  letI := iR1; letI := iR2; letI := iR3; letI := iR4; letI := iR5
  letI := iR6; letI := iR7
  -- Step 1: a prime of `R` lying over `(0) ⊆ ℤ_ℓ`.
  obtain ⟨P, hPp, hP0⟩ : ∃ P : Ideal R, P.IsPrime ∧
      ∀ x : ℤ_[ℓ], algebraMap ℤ_[ℓ] R x ∈ P → x = 0 := by
    have hℓR : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ nilradical R := by
      rw [mem_nilradical]
      rintro ⟨n, hn⟩
      rw [← map_pow] at hn
      exact pow_ne_zero n
        (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
        (hinj (hn.trans (map_zero (algebraMap ℤ_[ℓ] R)).symm))
    obtain ⟨P, hPp, hℓP⟩ : ∃ P : Ideal R, Ideal.IsPrime P ∧
        algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ P := by
      by_contra hcon
      push Not at hcon
      refine hℓR ?_
      rw [nilradical_eq_sInf]
      exact Submodule.mem_sInf.mpr fun J hJ => hcon J hJ
    refine ⟨P, hPp, fun x hx => by_contra fun hx0 => ?_⟩
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow] at hx
    rcases hPp.mem_or_mem hx with hu | hpow
    · exact hPp.ne_top (Ideal.eq_top_of_isUnit_mem P hu
        (IsUnit.map (algebraMap ℤ_[ℓ] R) (PadicInt.unitCoeff hx0).isUnit))
    · exact hℓP (hPp.mem_of_pow_mem _ hpow)
  haveI := hPp
  -- Step 2: `O := R ⧸ P` is a local topological domain of characteristic
  -- zero, finite over `ℤ_ℓ` with the `ℤ_ℓ`-module topology.
  have hloc : IsLocalRing (R ⧸ P) :=
    .of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := hloc
  have hfin : Module.Finite ℤ_[ℓ] (R ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
  letI := hfin
  have hmt : IsModuleTopology ℤ_[ℓ] (R ⧸ P) := by
    constructor
    have hquot :=
      (QuotientRing.isOpenQuotientMap_mk P).isQuotientMap.eq_coinduced
    have hmod := ModuleTopology.eq_coinduced_of_surjective
      (φ := (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap)
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
    rw [hquot, hmod]
    rfl
  letI := hmt
  have hinjO : Function.Injective (algebraMap ℤ_[ℓ] (R ⧸ P)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx => hP0 x ?_
    rwa [IsScalarTower.algebraMap_apply ℤ_[ℓ] R (R ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hx
  -- Step 3: specialize the framed representation along `R → R ⧸ P`.
  let e : (R ⧸ P) ⊗[R] (Fin 2 → R) ≃ₗ[R ⧸ P] (Fin 2 → R ⧸ P) :=
    TensorProduct.piScalarRight R (R ⧸ P) (R ⧸ P) (Fin 2)
  let ρO : FramedGaloisRep ℚ (R ⧸ P) (Fin 2) := (ρR.baseChange (R ⧸ P)).conj e
  -- Specialization stability of hardly-ramifiedness: established for the
  -- base change by `isHardlyRamified_baseChange_quotient` (determinant,
  -- unramifiedness and tameness proven; flatness the sorried transfer
  -- leaf `isFlatAt_baseChange_quotient`), then transported through the
  -- standard-basis framing `e` by `isHardlyRamified_conj`.
  have hrankQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] (Fin 2 → R)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  have hHRO : IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ P)) ρO :=
    isHardlyRamified_conj hℓOdd (rank_finTwoFun (R ⧸ P))
      (isHardlyRamified_baseChange_quotient hℓOdd P hrankQ hρR) e
  -- Step 4: the reduction map factors through the quotient: `ker πR` is
  -- maximal (its quotient is a finite domain, hence a field), so it is the
  -- maximal ideal of the local ring `R`, which contains the prime `P`.
  have hPle : P ≤ RingHom.ker πR := by
    haveI : (RingHom.ker πR).IsPrime := RingHom.ker_isPrime πR
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI : Finite (R ⧸ RingHom.ker πR) :=
      Finite.of_equiv _ (RingHom.quotientKerEquivRange πR).symm.toEquiv
    calc P ≤ IsLocalRing.maximalIdeal R :=
          IsLocalRing.le_maximalIdeal hPp.ne_top
      _ = RingHom.ker πR := (IsLocalRing.eq_maximalIdeal
          (Ideal.Quotient.maximal_of_isField _
            (Finite.isField_of_domain (R ⧸ RingHom.ker πR)))).symm
  let πO : R ⧸ P →+* ZMod ℓ :=
    Ideal.Quotient.lift P πR fun a ha => by
      rw [← RingHom.mem_ker]
      exact hPle ha
  -- Step 5: assemble; the characteristic polynomials of Frobenius
  -- transport through the specialization.
  have hcompat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map πO =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hq2 hqℓ
    have hcf : ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (ρR.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (algebraMap R (R ⧸ P)) :=
      charpoly_baseChange_conj ρR e
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    have hπcomp : πO.comp (algebraMap R (R ⧸ P)) = πR := by
      ext a
      rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.lift_mk P πR _
    rw [hcf, Polynomial.map_map, hπcomp]
    exact hπR q hq hq2 hqℓ
  exact ⟨{ O := R ⧸ P
           ρ := ρO
           isHardlyRamified := hHRO
           π := πO
           algebraMap_injective := hinjO
           charFrob_compat := hcompat }⟩

/-- **Compatibility bookkeeping** (sorry node): if the hardly ramified
`ℓ`-adic lift of `ρbar` lives in a compatible family of hardly ramified
representations, then the residual characteristic polynomials of Frobenius
of `ρbar` at `q ∉ {2, 3, ℓ}` are those of `1 ⊕ χ̄`, i.e.
`X² − (q+1)X + q` at `Frob_q`.

The eventual proof is bookkeeping around **B6c**
(`IsHardlyRamified.three_adic`, `Threeadic.lean`): the family's `3`-adic
member is hardly ramified, so by B6c its Frobenius traces at primes
`q ≥ 5` are `1 + q`; its Frobenius determinants are `q` (cyclotomic
determinant, part of `IsHardlyRamified`); compatibility transports the
resulting characteristic polynomial `X² − (q+1)X + q` from the `3`-adic
member to the `ℓ`-adic member, and the lift's `charFrob_compat` reduces it
to `ρbar`. No arithmetic-geometric content remains in this node — only
linear-algebra and base-change bookkeeping.

AUDIT RESTATEMENT (2026-07-16): the conclusion allows a finite
exceptional set `S` of places — the compatibility of the family
(`GaloisRepFamily.isCompatible`) only pins the characteristic
polynomials outside an unspecified finite set of places, so the former
`∀ q ∉ {2,3,ℓ}` form was unprovable from the stated hypotheses. The
downstream Chebotarev–Brauer–Nesbitt argument is insensitive to any
finite exceptional set. -/
theorem residual_charFrob_eq_of_family (_hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (L : HardlyRamifiedLift hℓOdd ρbar)
    (hfam :
      letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
      letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
      letI := L.moduleFinite; letI := L.isModuleTopology
      IsHardlyRamified.IsInHardlyRamifiedFamily (p := ℓ) L.ρ) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ q (hq : q.Prime),
        Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ) := by
  classical
  letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
  letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
  letI := L.moduleFinite; letI := L.isModuleTopology
  obtain ⟨E, iF, iNF, σ, ⟨S₀, Pv, hPv⟩, hodd, iAlgR, iCSR, hinjR, ψ, r', hψ⟩ :=
    hfam
  letI := iF; letI := iNF; letI := iAlgR; letI := iCSR
  haveI h3fact : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨φ₃⟩ := nonempty_ringHom_to_padicAlgClosure E 3
  obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
      hinjA, W, iW1, iW2, iW3, iW4, hW, τ, r, hτHR, hτeq⟩ :=
    hodd h3fact (by decide) φ₃
  letI := iA1; letI := iA2; letI := iA3; letI := iA4; letI := iA5
  letI := iA6; letI := iA7; letI := iA8; letI := iA9; letI := iA10
  letI := iA11; letI := iA12
  letI := iW1; letI := iW2; letI := iW3; letI := iW4
  refine ⟨insert Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
    (insert Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat S₀), ?_⟩
  intro q hq hqS hqℓ
  -- unpack the exceptional-set membership
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inl rfl))
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inl rfl))))
  have hqS₀ : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S₀ :=
    fun hmem => hqS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  have hq5 : 5 ≤ q := by
    have h2 := hq.two_le
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · interval_cases q
      · omega
      · omega
      · exact absurd hq (by decide)
    · exact h5
  -- side conditions: the place has residue characteristic ≠ 3 and ≠ ℓ
  have hside3 : ((3 : ℕ) : NumberField.RingOfIntegers ℚ) ∉
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal := by
    rw [natCast_mem_toHeightOneSpectrum_iff (by decide) hq]
    omega
  have hsideℓ : ((ℓ : ℕ) : NumberField.RingOfIntegers ℚ) ∉
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal := by
    rw [natCast_mem_toHeightOneSpectrum_iff (Fact.out : ℓ.Prime) hq]
    exact fun h => hqℓ h.symm
  obtain ⟨-, hcomp3⟩ := hPv (p := 3) h3fact φ₃
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) hqS₀ hside3
  obtain ⟨-, hcompℓ⟩ := hPv (p := ℓ) ‹Fact ℓ.Prime› ψ
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) hqS₀ hsideℓ
  -- the 3-adic member's characteristic polynomial at Frobenius
  haveI : Nontrivial A := inferInstance
  have hτcp : (τ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      X ^ 2 - C ((q : A) + 1) * X + C (q : A) := by
    have hfin : Module.finrank A W = 2 := by
      unfold Module.finrank
      rw [hW]
      simp
    have hrec := charpoly_eq_quadratic_of_finrank_two (F := A) (V := W) hfin
      (τ (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)))
    have htrace := IsHardlyRamified.three_adic W hW hτHR q hq hq5
    have hdet0 := hτHR.det (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
    rw [cyclotomicCharacter_globalFrob (ℓ := 3) hq hq3, map_natCast] at hdet0
    have hdet1 : LinearMap.det (τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) = (q : A) :=
      hdet0
    have htrace1 : LinearMap.trace A W (τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) = 1 + (q : A) :=
      htrace
    rw [hrec, hdet1, htrace1, add_comm (1 : A) (q : A)]
  -- transport to the family member over `ℚ̄₃` and descend to `E`
  have h3top : ((σ h3fact φ₃) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      ((τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly).map
        (algebraMap A (AlgebraicClosure ℚ_[3])) := by
    rw [← hτeq]
    exact charpoly_baseChange_conj τ r _
  have hPvq : Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) =
      X ^ 2 - C ((q : E) + 1) * X + C (q : E) := by
    apply Polynomial.map_injective φ₃ φ₃.injective
    rw [← hcomp3]
    show ((σ h3fact φ₃) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly = _
    rw [h3top, hτcp]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast,
      map_add, map_one]
  -- transport the `ℓ`-adic member and descend to the lift's coefficients
  have hℓtop : ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      ((L.ρ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly).map
        (algebraMap L.O (AlgebraicClosure ℚ_[ℓ])) := by
    rw [← hψ]
    exact charpoly_baseChange_conj L.ρ r' _
  have hOcp : (L.ρ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      X ^ 2 - C ((q : L.O) + 1) * X + C (q : L.O) := by
    apply Polynomial.map_injective (algebraMap L.O (AlgebraicClosure ℚ_[ℓ]))
      hinjR
    rw [← hℓtop]
    show ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly = _
    rw [show ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
        ((σ ‹Fact ℓ.Prime› ψ).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)
          (Field.AbsoluteGaloisGroup.adicArithFrob
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly
        from rfl, hcompℓ, hPvq]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast,
      map_add, map_one]
  -- reduce through the lift's compatibility
  have hred := L.charFrob_compat q hq hq2 hqℓ
  rw [show L.ρ.charFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) =
    (L.ρ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly
    from rfl, hOcp] at hred
  rw [← hred]
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, map_natCast,
    map_add, map_one]

/-- **B6b + B6c**: the residual characteristic polynomials of Frobenius of
a liftable hardly ramified representation are those of `1 ⊕ χ̄`, i.e.
`X² − (q+1)X + q` at `Frob_q`. Derived from **B6b**
(`IsHardlyRamified.mem_isCompatible`, `Family.lean`: the lift spreads out
into a compatible family of hardly ramified representations) and the
compatibility bookkeeping node above (which consumes **B6c**,
`IsHardlyRamified.three_adic`). -/
theorem residual_charFrob_eq (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (L : HardlyRamifiedLift hℓOdd ρbar) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ q (hq : q.Prime),
        Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ) :=
  residual_charFrob_eq_of_family hℓOdd hℓ5 L
    (letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
     letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
     letI := L.moduleFinite; letI := L.isModuleTopology
     -- the characteristic-zero hypothesis of the restated B6b node is
     -- exactly the `algebraMap_injective` field of the lift package
     IsHardlyRamified.mem_isCompatible hℓOdd (rank_finTwoFun L.O)
       L.algebraMap_injective L.isHardlyRamified)

set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev + Brauer–Nesbitt**: a continuous mod-`ℓ` representation
of `Gal(ℚ̄/ℚ)` whose characteristic polynomials of Frobenius away from
`{2, 3, ℓ}` are those of `1 ⊕ χ̄` is not irreducible.

DERIVED from the Chebotarev density node
(`dense_conjClasses_globalFrob`), the Brauer–Nesbitt node
(`not_isIrreducible_of_charpoly_eq`), the Frobenius value of the mod-`ℓ`
cyclotomic character (`cyclotomicCharacterModL_globalFrob`), and the
proven continuity/bridge lemmas of `Chebotarev.lean`: the set of `g` where
the characteristic polynomial of `ρbar g` agrees with that of `1 ⊕ χ̄` is
closed (both coefficient functions are continuous into the discrete
`ZMod ℓ` — the module topology on `End` is discrete) and contains the
dense set of Frobenius conjugates, hence is everything. -/
theorem not_isIrreducible_of_charFrob_eq
    {ρbar : GaloisRep ℚ (ZMod ℓ) V}
    (S : Finset (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ)))
    (h : ∀ q (hq : q.Prime),
      Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ)) :
    ¬ ρbar.IsIrreducible := by
  classical
  -- an auxiliary prime avoiding the exceptional places pins the rank at 2:
  -- distinct primes give distinct places, so a finite set of places
  -- excludes only finitely many primes
  obtain ⟨q₀, hq₀p, hq₀S, hq₀ℓ⟩ :
      ∃ q₀ : ℕ, ∃ hq₀ : q₀.Prime,
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀ ∉ S) ∧ q₀ ≠ ℓ := by
    set T : Finset ℕ := (insert
        ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
        S).attach.image
      (fun v => (exists_prime_toHeightOneSpectrum v.1).choose) with hT
    obtain ⟨q₀, hq₀ge, hq₀p⟩ := Nat.exists_infinite_primes (T.sup id + 1)
    have hq₀T : q₀ ∉ T := by
      intro hmem
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    have hq₀S' : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p ∉
        insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
          S := by
      intro hmem
      apply hq₀T
      obtain ⟨hcp, hceq⟩ := (exists_prime_toHeightOneSpectrum
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose_spec
      have hch : (exists_prime_toHeightOneSpectrum
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose = q₀ :=
        toHeightOneSpectrumRingOfIntegersRat_injective hcp hq₀p hceq.symm
      rw [hT]
      exact Finset.mem_image.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, hch⟩
    refine ⟨q₀, hq₀p, fun hmem => hq₀S' (Finset.mem_insert_of_mem hmem), ?_⟩
    rintro rfl
    exact hq₀S' (Finset.mem_insert.mpr (Or.inl rfl))
  have hfr : Module.finrank (ZMod ℓ) V = 2 := by
    have h0 := congrArg Polynomial.natDegree (h q₀ hq₀p hq₀S hq₀ℓ)
    rwa [GaloisRep.charFrob_eq_charpoly_globalFrob,
      LinearMap.charpoly_natDegree, natDegree_comparisonQuadratic] at h0
  have hrank : Module.rank (ZMod ℓ) V = 2 := by
    rw [← Module.finrank_eq_rank (ZMod ℓ) V, hfr]
    norm_num
  -- the endomorphism space is discrete in its module topology
  letI : TopologicalSpace (Module.End (ZMod ℓ) V) :=
    moduleTopology (ZMod ℓ) (Module.End (ZMod ℓ) V)
  haveI : DiscreteTopology (Module.End (ZMod ℓ) V) :=
    discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  -- the agreement set is closed …
  have hχcont := continuous_cyclotomicCharacterModL ℓ
  have hc1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 1 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End (ZMod ℓ) V => φ.charpoly.coeff 1)) hρcont
  have hc0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 0 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End (ZMod ℓ) V => φ.charpoly.coeff 0)) hρcont
  have hb1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => -(x + 1))
      continuous_of_discreteTopology hχcont
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      (ρbar g).charpoly.coeff 1 =
        -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rw [Set.setOf_and]
    exact (isClosed_eq hc1 hb1).inter (isClosed_eq hc0 hχcont)
  -- … and contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ insert
          ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        (ρbar g).charpoly.coeff 1 =
          -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
        (ρbar g).charpoly.coeff 0 =
          ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hqS : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S :=
      fun hmem => hvS (Finset.mem_insert_of_mem hmem)
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inl rfl))
    -- conjugation invariance of the characteristic polynomial
    have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
      have : ρbar g * ρbar g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact this
    have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
      have : ρbar g⁻¹ * ρbar g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact this
    have hconj : (ρbar (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹)).charpoly =
        (ρbar (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly := by
      have heq : ρbar (g * globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
          (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj
            (ρbar (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
        ext x
        simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
      rw [heq, LinearEquiv.charpoly_conj]
    -- conjugation invariance of the cyclotomic character
    have hχconj : cyclotomicCharacterModL ℓ (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
        cyclotomicCharacterModL ℓ (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have hval := h q hq hqS hqℓ
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    have hfrob := cyclotomicCharacterModL_globalFrob (ℓ := ℓ) hq hqℓ
    constructor
    · show (ρbar _).charpoly.coeff 1 = _
      rw [hconj, hval, coeff_one_comparisonQuadratic, hχconj, hfrob]
    · show (ρbar _).charpoly.coeff 0 = _
      rw [hconj, hval, coeff_zero_comparisonQuadratic, hχconj, hfrob]
  -- density: the agreement set is everything
  have hDall : ∀ g : Field.absoluteGaloisGroup ℚ,
      (ρbar g).charpoly.coeff 1 =
        -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ)
      (insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S)
    have : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact this (Set.mem_univ g)
  -- reconstruct the polynomial identity and conclude by Brauer–Nesbitt
  apply not_isIrreducible_of_charpoly_eq hrank ρbar
  intro g
  obtain ⟨h1, h0⟩ := hDall g
  refine monic_quadratic_ext (LinearMap.charpoly_monic _)
    (monic_comparisonQuadratic _) ?_ (natDegree_comparisonQuadratic _) ?_ ?_
  · rw [LinearMap.charpoly_natDegree, hfr]
  · rw [h1, coeff_one_comparisonQuadratic]
  · rw [h0, coeff_zero_comparisonQuadratic]

end GaloisRepresentation
