/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# The relative ideal norm on class groups

Mathlib has `Ideal.relNorm R : Ideal S →*₀ Ideal R` for an extension `R ⊆ S` of Dedekind
domains, and it has the class group `ClassGroup R`; it does **not** have the induced map
`ClassGroup S →* ClassGroup R`.  It has only the map in the OTHER direction,
`ClassGroup.extendedHom : ClassGroup A →* ClassGroup B`, which pushes fractional ideals
forward along `A → B` (`Mathlib/RingTheory/ClassGroup/ExtendedHom.lean`).

This file supplies the norm direction, `ClassGroup.relNormHom`, together with the two facts
that make it usable: its value on the class of an integral ideal, and its transitivity in a
tower.

## Main definitions

* `ClassGroup.relNormNZD R S : (Ideal S)⁰ → (Ideal R)⁰` — the relative norm of a nonzero
  ideal, packaged as a nonzerodivisor.  `Ideal.relNorm_eq_bot_iff` is what makes this
  well defined.
* `ClassGroup.relNormHom R S : ClassGroup S →* ClassGroup R` — the induced map on class
  groups.

## Main results

* `ClassGroup.relNormHom_mk0` — `relNormHom` sends the class of `I` to the class of
  `N_{S/R} I`.  This, together with `ClassGroup.mk0_surjective`, characterises it.
* `ClassGroup.relNormHom_comp` — transitivity in a tower `R ⊆ T ⊆ S`, from
  `Ideal.relNorm_relNorm`.

## Construction

There is no relative norm on FRACTIONAL ideals at this pin, so `relNormHom` cannot be
obtained by transporting a map along `ClassGroup R = (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸
(principal ideals)`.  It is built instead out of `ClassGroup.mk0_surjective`: the composite
`(Ideal S)⁰ →* ClassGroup R`, `I ↦ [N_{S/R} I]`, is constant on the fibres of
`ClassGroup.mk0` — if `(x) I = (y) J` then `(N x) N I = (N y) N J` by multiplicativity of the
norm and `Ideal.relNorm_singleton` — so it factors through `ClassGroup S` set-theoretically
(`Function.surjInv`), and multiplicativity of the factorisation is read off from
multiplicativity upstairs.  `Algebra.intNorm_eq_zero` is what keeps the two auxiliary
elements nonzero.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace ClassGroup

variable (R S : Type*) [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- The relative norm of a nonzero ideal, as a nonzerodivisor of `Ideal R`.  The
nonzerodivisor clause is `Ideal.relNorm_eq_bot_iff`. -/
noncomputable def relNormNZD (I : (Ideal S)⁰) : (Ideal R)⁰ :=
  ⟨Ideal.relNorm R (I : Ideal S), mem_nonZeroDivisors_of_ne_zero (by
    simpa using (Ideal.relNorm_eq_bot_iff (R := R) (I := (I : Ideal S))).not.mpr
      (by simpa using mem_nonZeroDivisors_iff_ne_zero.mp I.2))⟩

@[simp] theorem relNormNZD_coe (I : (Ideal S)⁰) :
    (relNormNZD R S I : Ideal R) = Ideal.relNorm R (I : Ideal S) := rfl

theorem relNormNZD_mul (I J : (Ideal S)⁰) :
    relNormNZD R S (I * J) = relNormNZD R S I * relNormNZD R S J :=
  Subtype.ext (by simp [relNormNZD])

/-- **The norm class of a nonzero ideal depends only on its ideal class.**  This is the
well-definedness that makes `ClassGroup.relNormHom` exist: `ClassGroup.mk0_eq_mk0_iff` turns
the hypothesis into `(x) I = (y) J`, and applying `Ideal.relNorm` to that equation gives
`(N x) N I = (N y) N J` by `Ideal.relNorm_singleton` and multiplicativity. -/
theorem mk0_relNormNZD_congr {I J : (Ideal S)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (relNormNZD R S I) = ClassGroup.mk0 (relNormNZD R S J) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  refine ClassGroup.mk0_eq_mk0_iff.mpr
    ⟨Algebra.intNorm R S x, Algebra.intNorm R S y, ?_, ?_, ?_⟩
  · simpa [Algebra.intNorm_eq_zero] using hx
  · simpa [Algebra.intNorm_eq_zero] using hy
  · have := congrArg (Ideal.relNorm R) hxy
    simpa [Ideal.relNorm_singleton] using this

/-- The underlying function of `ClassGroup.relNormHom`, obtained from
`ClassGroup.mk0_surjective` by choice.  Its only interface is `relNormHom_mk0`; nothing
should unfold this. -/
noncomputable def relNormFun (c : ClassGroup S) : ClassGroup R :=
  ClassGroup.mk0 (relNormNZD R S (Function.surjInv ClassGroup.mk0_surjective c))

theorem relNormFun_mk0 (I : (Ideal S)⁰) :
    relNormFun R S (ClassGroup.mk0 I) = ClassGroup.mk0 (relNormNZD R S I) :=
  mk0_relNormNZD_congr R S (Function.surjInv_eq ClassGroup.mk0_surjective _)

/-- **THE RELATIVE IDEAL NORM ON CLASS GROUPS**, `[I] ↦ [N_{S/R} I]`.

Absent from mathlib at this pin, which has only the extension map in the opposite
direction (`ClassGroup.extendedHom`).  It is characterised by `relNormHom_mk0` together with
surjectivity of `ClassGroup.mk0`. -/
noncomputable def relNormHom : ClassGroup S →* ClassGroup R :=
  MonoidHom.mk' (relNormFun R S) (by
    intro a b
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, relNormFun_mk0, relNormFun_mk0, relNormFun_mk0, relNormNZD_mul, map_mul])

@[simp] theorem relNormHom_mk0 (I : (Ideal S)⁰) :
    relNormHom R S (ClassGroup.mk0 I) = ClassGroup.mk0 (relNormNZD R S I) :=
  relNormFun_mk0 R S I

variable (T : Type*) [CommRing T] [IsDedekindDomain T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
    [Module.IsTorsionFree R T] [Module.IsTorsionFree T S]

theorem relNormNZD_relNormNZD (I : (Ideal S)⁰) :
    relNormNZD R T (relNormNZD T S I) = relNormNZD R S I :=
  Subtype.ext (Ideal.relNorm_relNorm R T (I : Ideal S))

/-- **TRANSITIVITY OF THE NORM MAP IN A TOWER `R ⊆ T ⊆ S`**, from
`Ideal.relNorm_relNorm`.  This is what makes the norm CLASS GROUP of a tower factor, and
hence what makes the norm index submultiplicative. -/
theorem relNormHom_comp :
    (relNormHom R T).comp (relNormHom T S) = relNormHom R S := by
  refine MonoidHom.ext fun c => ?_
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [MonoidHom.comp_apply, relNormHom_mk0, relNormHom_mk0, relNormHom_mk0,
    relNormNZD_relNormNZD]

end ClassGroup
