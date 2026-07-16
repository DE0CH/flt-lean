/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Topology.Instances.ZMod
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- VENDORING ADDITION: the counting lemma backing `group_theory_lemma`.
public import Fermat.FLT.EllipticCurve.TorsionCounting
-- VENDORING ADDITION: the torsion count via divisibility + the
-- prime-level count, backing `n_torsion_card`.
public import Fermat.FLT.EllipticCurve.TorsionCard

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
-- VENDORING CHANGE (2026-07-16): finiteness is now DERIVED from the
-- torsion count (`TorsionCard.card_torsionBy`): the count is `n² > 0`,
-- and a type of positive `Nat.card` is finite. The hypotheses are
-- specialized to separably closed fields of characteristic zero — the
-- only fields at which the tree uses finiteness (the division-polynomial
-- route of the former `TorsionFinite.lean`, which covered arbitrary
-- characteristic, is superseded and removed).
theorem WeierstrassCurve.n_torsion_finite [IsSepClosed k] [CharZero k]
    {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := by
  have hcard := TorsionCard.card_torsionBy E n (Nat.cast_ne_zero.mpr hn.ne')
  have hpos : 0 < Nat.card (E.nTorsion n) := by
    rw [hcard]
    positivity
  exact (Nat.card_pos_iff.mp hpos).2

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
-- This theorem was well-known in the early part of the 20th century.
-- VENDORING CHANGE: the `sorry` is replaced by the derivation in
-- `TorsionCard.lean`: strong induction peeling off the minimal prime
-- factor, from the divisibility node (`TorsionCard.smul_surjective`) and
-- the prime-level count (`TorsionCard.prime_torsion_card`).
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 :=
  TorsionCard.card_torsionBy E n hn

-- This theorem was well-known in the early part of the 20th century.
-- VENDORING CHANGE: the `sorry` is replaced by the counting argument in
-- `Fermat/FLT/EllipticCurve/TorsionCounting.lean` (structure theorem for
-- finite abelian groups + torsion counting + CRT).
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) :=
  TorsionCounting.nonempty_torsionBy_addEquiv_pi_zmod hn r h

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- VENDORING ADDITION: the `p`-torsion is 2-dimensional as a `ZMod p`-module.
-- This discharges the rank hypothesis of `IsHardlyRamified` for the Frey
-- curve (previously a `sorry` in statement position in
-- `GaloisRepresentation/HardlyRamified/Frey.lean`).
theorem WeierstrassCurve.p_torsion_rank [IsSepClosed k] {p : ℕ} [Fact p.Prime]
    (hp : (p : k) ≠ 0) : Module.rank (ZMod p) (E.nTorsion p) = 2 := by
  obtain ⟨φ⟩ := E.n_torsion_dimension hp
  let ψ : E.nTorsion p ≃ₗ[ZMod p] (ZMod p × ZMod p) :=
    { φ with map_smul' := ZMod.map_smul φ.toAddMonoidHom }
  have h := ψ.lift_rank_eq
  rw [rank_prod', Module.rank_self] at h
  simpa [one_add_one_eq_two] using h

-- follows easily from the above
-- VENDORING CHANGE: the unrestricted statement is FALSE for `n = 0` (the
-- `0`-torsion is the whole group of points, which is typically infinite), so
-- the instance now requires `[NeZero n]`; it is then immediate from
-- `n_torsion_finite`, consolidating the sorry into that single node.
noncomputable instance [IsSepClosed k] [CharZero k] (n : ℕ) [NeZero n] :
    Module.Finite (ZMod n) (E.nTorsion n) :=
  haveI : Finite (E.nTorsion n) := E.n_torsion_finite (Nat.pos_of_ne_zero (NeZero.ne n))
  Module.Finite.of_finite

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      -- VENDORING CHANGE: the four `sorry`s here are filled in.
      one_smul P := by cases P <;> rfl
      mul_smul g h P := by cases P <;> rfl
      smul_zero g := rfl
      smul_add g P Q :=
        map_add (WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)) P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
-- VENDORING CHANGE: the `sorry`-d data is replaced by the genuine construction.
-- The representation is the natural Galois action on the `n`-torsion (via
-- `WeierstrassCurve.Affine.Point.map`, packaged through the `DistribMulAction`
-- instance above), made `ZMod n`-linear by `ZMod.toZModLinearMap`. Continuity:
-- the `n`-torsion is finite (`n_torsion_finite`, still sorry-rooted), so the
-- coordinates of all torsion points generate a finite extension `F/K`; the
-- representation kills the open subgroup `Gal(Kᵃˡᵍ/F)`, hence every fiber is a
-- union of left cosets of an open subgroup, hence open — so the map is
-- continuous for ANY topology on the target.
noncomputable def WeierstrassCurve.galoisRep {K : Type u} [Field K] [CharZero K]
    (E : WeierstrassCurve K)
    [E.IsElliptic] [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
    GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :=
  letI := moduleTopology (ZMod n) (Module.End (ZMod n)
    ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n))
  -- the ambient Galois action on points, as a monoid hom into additive
  -- endomorphisms; the ascription typechecks because the double base change
  -- `(E.map (algebraMap K Kᵃˡᵍ))⁄Kᵃˡᵍ` is definitionally `E⁄Kᵃˡᵍ`
  let ρamb : Field.absoluteGaloisGroup K →*
      AddMonoid.End (((E.map (algebraMap K (AlgebraicClosure K)))⁄(AlgebraicClosure K)).Point) :=
    DistribMulAction.toAddMonoidEnd (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((E⁄(AlgebraicClosure K)).Point)
  -- the induced `ZMod n`-linear action on the `n`-torsion
  let ρm : Field.absoluteGaloisGroup K →*
      Module.End (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :=
    { toFun := fun σ =>
        AddMonoidHom.toZModLinearMap n (TorsionCounting.endRestrict (ρamb σ) n)
      map_one' := by
        ext P
        rw [map_one ρamb]
        rfl
      map_mul' := fun σ τ => by
        ext P
        rw [map_mul ρamb]
        rfl }
  { toMonoidHom := ρm
    continuous_toFun := by
      haveI : NeZero n := ⟨hn.ne'⟩
      haveI hMfin : Finite ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :=
        WeierstrassCurve.n_torsion_finite _ hn
      -- the coordinates of a point
      let coords : ((E.map (algebraMap K (AlgebraicClosure K)))⁄(AlgebraicClosure K)).Point →
          Set (AlgebraicClosure K) := fun P =>
        match P with
        | .zero => ∅
        | .some x y _ => {x, y}
      have hcoordsFin : ∀ P, (coords P).Finite := by
        intro P
        cases P with
        | zero => exact Set.finite_empty
        | some x y h => exact (Set.finite_singleton y).insert x
      -- the (finite) set of coordinates of all `n`-torsion points
      set S : Set (AlgebraicClosure K) :=
        ⋃ P : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n, coords P.1 with hSdef
      have hSFin : S.Finite := Set.finite_iUnion fun P => hcoordsFin P.1
      haveI := hSFin.to_subtype
      haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
        IntermediateField.finiteDimensional_adjoin fun x _ =>
          (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
      have hHopen : IsOpen ((IntermediateField.adjoin K S).fixingSubgroup :
          Set (Field.absoluteGaloisGroup K)) :=
        (IntermediateField.adjoin K S).fixingSubgroup_isOpen
      -- the representation kills the fixing subgroup
      have hker : ∀ τ ∈ (IntermediateField.adjoin K S).fixingSubgroup, ρm τ = 1 := by
        intro τ hτ
        have hfixmem : ∀ x ∈ S,
            (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) x = x := fun x hx =>
          ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ) x
            (IntermediateField.subset_adjoin K S hx)
        ext P
        show (ρamb τ) P.1 = (P.1 :
          ((E.map (algebraMap K (AlgebraicClosure K)))⁄(AlgebraicClosure K)).Point)
        obtain ⟨P0, hP0⟩ := P
        show (ρamb τ) P0 = P0
        cases P0 with
        | zero => rfl
        | some x y hxy =>
          have hx : (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) x = x :=
            hfixmem x (Set.mem_iUnion.mpr
              ⟨⟨WeierstrassCurve.Affine.Point.some x y hxy, hP0⟩,
              show x ∈ ({x, y} : Set (AlgebraicClosure K)) from Set.mem_insert x {y}⟩)
          have hy : (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) y = y :=
            hfixmem y (Set.mem_iUnion.mpr
              ⟨⟨WeierstrassCurve.Affine.Point.some x y hxy, hP0⟩,
              show y ∈ ({x, y} : Set (AlgebraicClosure K)) from
                Set.mem_insert_of_mem x rfl⟩)
          show WeierstrassCurve.Affine.Point.map (W' := E)
            (τ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) (.some x y hxy) = .some x y hxy
          rw [WeierstrassCurve.Affine.Point.map_some]
          simp only [hx, hy]
      -- continuity: every fiber is a union of left cosets of the open subgroup
      refine continuous_def.mpr fun U _ => isOpen_iff_forall_mem_open.mpr fun σ hσ => ?_
      open Pointwise in
      refine ⟨σ • ((IntermediateField.adjoin K S).fixingSubgroup :
        Set (Field.absoluteGaloisGroup K)), ?_, hHopen.leftCoset σ, ?_⟩
      · rintro τ' ⟨u, hu, rfl⟩
        show ρm (σ * u) ∈ U
        rw [map_mul, hker u hu, mul_one]
        exact hσ
      · exact ⟨1, Subgroup.one_mem _, mul_one σ⟩ }
