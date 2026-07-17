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

set_option warn.sorry false in
/-- **The determinant of the mod-`p` Galois representation is the
cyclotomic character** (sorry node): the arithmetic content of the
Weil pairing. Classically: the pairing `E[p] × E[p] → μ_p` is
Galois-equivariant with `Gal` acting on `μ_p` by the cyclotomic
character, and on a rank-`2` space any equivariant alternating
nondegenerate pairing forces `det ρ = χ`. Conversely `det ρ = χ`
suffices to CONSTRUCT the abstract pairing (the coordinate
determinant form), which is how the tree consumes it. -/
theorem det_galoisRep_eq_cyclotomic (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (p : ℕ) [Fact p.Prime] (hppos : 0 < p)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det
      (E.galoisRep p hppos g : Module.End (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p)) =
      algebraMap ℤ_[p] (ZMod p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) :=
  sorry

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

