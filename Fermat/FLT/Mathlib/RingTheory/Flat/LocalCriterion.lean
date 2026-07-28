/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The local criterion of flatness for a nilpotent ideal

Let `A` be a commutative ring, `J ⊆ A` an ideal with `J ^ N = ⊥`, and `B` an `A`-algebra.
Then `B` is flat over `A` as soon as

* `B ⧸ J B` is flat over `A ⧸ J`, and
* `Tor₁^A(A ⧸ J, B) = 0`, written without derived functors as injectivity of `J ⊗[A] B → B`.

This is [Stacks 00MK] / [Stacks 051C] in the nilpotent case, Matsumura *Commutative Ring
Theory* 22.1/22.3, Bourbaki *Algèbre commutative* III §5.  **No separatedness and no
Artin–Rees are involved** — that is the whole point of the nilpotent case, and it is why
this statement, rather than the full local criterion, is what the consumer needs.

**PROVEN 2026-07-28, and the route is NOT the one this file previously advertised.**
Everything below is a record of how it was actually done, because the two routes this
file recommended for two days were both more expensive than the one that worked.

## The verdict this file used to carry, and why it was wrong

The old module docstring said: mathlib has no `Tor` long exact sequence — true, and
re-verified at this pin (`CategoryTheory/Monoidal/Tor.lean` is 60 lines with two lemmas
about projectives; `CategoryTheory/Abelian/LeftDerived.lean` has no connecting map; there
is no module-level `Tor₁` anywhere, nor in `~/cs/FLT`, nor elsewhere in this project) —
and therefore a prover must either **assemble `Tor₁` with its six-term sequence** or run a
**successive-approximation argument over `Module.Flat.iff_forall_isTrivialRelation`**.

Both of those are real, and **both are unnecessary**.  The equational-criterion route in
particular does not work in the naive form the old text proposed: the induction it
suggested filters the coefficients `c_j = ∑_i f_i a_{ij}` by `J ^ r`, and at `r ≥ 1` every
`c_j` is already `0` in `A ⧸ J`, so reducing the relation mod `J` says nothing and the
inductive step is vacuous.  That dead end is recorded here so nobody walks into it again.

## What the proof actually is: Stacks 00MK with the derived functors deleted

The classical argument proves `Tor₁^A(N, B) = 0` for every `N` killed by a power of `J`,
in two steps, each of which uses the long exact sequence.  The observation that removes
the homological algebra entirely is that **both steps can be phrased as statements about a
submodule of a FLAT module**, where the only input needed is right-exactness of `- ⊗ B`
(root-level `rTensor_exact` — note it is NOT in the `LinearMap` namespace, and inside
`namespace Module.Flat` the bare name resolves to a different lemma, so it must be written
`_root_.rTensor_exact`).  Concretely, the whole development
is a proof of

    `F` flat, `K ≤ F` a submodule, `J ^ n • ⊤ ≤ K`  ⟹  `↥K ⊗[A] B → F ⊗[A] B` injective

(`rTensor_subtype_injective_of_pow_smul_top_le`), by induction on `n`.  Taking `F = A` and
`K` an arbitrary ideal, with `J ^ N = ⊥` so that the hypothesis is vacuous, and feeding the
result to `Module.Flat.iff_rTensor_injective'`, gives the theorem.  The four ingredients:

1. `rTensor_smul_top_subtype_injective_of_flat` — the case `K = J • ⊤`.  `J ⊗[A] F ≅ J • ⊤`
   because `F` is flat, so after the rearrangement `(X ⊗ F) ⊗ B ≅ (X ⊗ B) ⊗ F`
   (`swapEquiv`, natural in `X`) the map in question is `(J ⊗ B → A ⊗ B) ⊗ F`, injective by
   `htor` and flatness of `F`.  This is the ONLY place `htor` is used.

2. `rTensor_injective_of_isTorsionBySet` — change of rings.  For `A`-modules killed by `J`
   an injection stays injective after `- ⊗[A] B`, because
   `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` identifies `(A ⧸ J) ⊗[A] B` with
   `B ⧸ JB` as `A ⧸ J`-algebras, so `hflat` transports to flatness of `(A ⧸ J) ⊗[A] B`,
   and `AlgebraTensorModule.cancelBaseChange` rewrites `P ⊗[A] B` as
   `P ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] B)`.  This is the ONLY place `hflat` is used.

3. `rTensor_subtype_injective_of_smul_top_le` — STEP 1 of Stacks 00MK, i.e. the case
   `n = 1`.  A three-term chase on `J • ⊤ ≤ K ≤ F`: the image of `ξ` in
   `↥(K/J•⊤) ⊗ B → (F/J•⊤) ⊗ B` dies by (2), so `ξ` comes from `(J • ⊤) ⊗ B` by
   right-exactness, and that injects by (1).  **Note it holds for an ARBITRARY flat `F`,
   not just a free one** — which is what makes the induction below close.

4. `rTensor_subtype_injective_of_flat_presentation` — the device replacing the long exact
   sequence.  Given a surjection `π : G ↠ N` with `G` flat and `J • G ≤ π⁻¹(KL)`, STEP 1
   applied to `π⁻¹(KL) ≤ G` transfers to `↥KL ⊗ B → N ⊗ B`.  The chase: lift `ξ` to
   `ξ̃ ∈ π⁻¹(KL) ⊗ B`, observe its image in `G ⊗ B` is killed in `N ⊗ B`, hence equals the
   image of some `ρ ∈ ker π ⊗ B`; STEP 1 forces `ξ̃ = ρ`, and `ker π` maps to `0` in `KL`.

   The induction step is then: for `J ^ (n+1) • ⊤ ≤ K`, put `L = K ⊔ J ^ n • ⊤`, so
   `↥L ⊗ B → F ⊗ B` is injective by the inductive hypothesis, and `J • L ≤ K`, so the
   presentation `(↥L →₀ A) ↠ ↥L` and (4) give `↥K ⊗ B → ↥L ⊗ B`.  Compose.

## Faithfulness note on the shape of the statement

It is stated for an `A`-ALGEBRA `B` rather than for a bare `A`-module `M` for one reason
only: `Algebra (A ⧸ J) (B ⧸ J.map (algebraMap A B))` is an instance
(`Ideal.Quotient.algebraQuotientMapQuotient`), whereas `Module (A ⧸ J) (M ⧸ J • ⊤)` is not,
so the module form cannot even be *stated* without carrying a scalar action by hand.  That
observation is still correct and was re-confirmed while proving this: an attempt to state
the helpers for a bare module failed exactly there.  The module form is the one that
belongs in mathlib, and a prover who produces it should restate this as a corollary rather
than duplicating the argument.  Note that only ingredient (2) above actually needs the
algebra structure; (1), (3), (4) are already module-level.

`htor` is written in the shape of `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, i.e.
as injectivity of `TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype) : J ⊗[A] B → B`,
which is precisely `Tor₁^A(A ⧸ J, B) = 0` spelled without derived functors.

## What this does NOT give

`rTensor_subtype_injective_of_pow_smul_top_le` carries no nilpotence hypothesis — the
nilpotence is spent only at the very end, to make `J ^ N • ⊤ ≤ K` hold for every `K`.  So
the induction is directly reusable for the non-nilpotent statements in
`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` (`lTensor_pow_subtype_injective` and
`lTensor_subtype_injective_of_pow_le`), where `J ^ n • ⊤ ≤ 𝔠` is a hypothesis rather than a
triviality.  It does **not** give flatness of `A ⧸ I ^ n` quotients directly; that needs a
change-of-rings step on top.

[Stacks 00MK]: https://stacks.math.columbia.edu/tag/00MK
[Stacks 051C]: https://stacks.math.columbia.edu/tag/051C
[Stacks 00HK]: https://stacks.math.columbia.edu/tag/00HK
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.Flat

namespace NilpotentLocalCriterion

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- The rearrangement `(X ⊗ F) ⊗ B ≃ (X ⊗ B) ⊗ F`. -/
noncomputable def swapEquiv (X : Type u) [AddCommGroup X] [Module A X]
    (F : Type u) [AddCommGroup F] [Module A F] :
    (X ⊗[A] F) ⊗[A] B ≃ₗ[A] (X ⊗[A] B) ⊗[A] F :=
  (TensorProduct.assoc A X F B) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl A X) (TensorProduct.comm A F B)) ≪≫ₗ
    (TensorProduct.assoc A X B F).symm

theorem swapEquiv_naturality {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] {F : Type u} [AddCommGroup F] [Module A F]
    (g : X →ₗ[A] Y) :
    ((swapEquiv (A := A) (B := B) Y F : _ →ₗ[A] _).comp
        (LinearMap.rTensor B (LinearMap.rTensor F g)))
      = (LinearMap.rTensor F (LinearMap.rTensor B g)).comp
        (swapEquiv (A := A) (B := B) X F : _ →ₗ[A] _) := by
  ext x f b
  simp [swapEquiv]

/-- SUB-LEAF 1. -/
theorem rTensor_smul_top_subtype_injective_of_flat
    {J : Ideal A} (htor : Function.Injective (LinearMap.rTensor B J.subtype))
    {F : Type u} [AddCommGroup F] [Module A F] [Module.Flat A F] :
    Function.Injective (LinearMap.rTensor B (J • (⊤ : Submodule A F)).subtype) := by
  classical
  set mu : ↥J ⊗[A] F →ₗ[A] F :=
    (TensorProduct.lid A F).toLinearMap.comp (LinearMap.rTensor F J.subtype) with hmudef
  have hmuinj : Function.Injective mu :=
    (TensorProduct.lid A F).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap J.subtype Subtype.val_injective)
  have hle : LinearMap.range mu ≤ J • (⊤ : Submodule A F) := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x f =>
      have : mu (x ⊗ₜ[A] f) = (x : A) • f := by simp [hmudef]
      rw [this]
      exact Submodule.smul_mem_smul x.2 Submodule.mem_top
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  have hge : J • (⊤ : Submodule A F) ≤ LinearMap.range mu :=
    Submodule.smul_le.mpr fun r hr x _ => ⟨(⟨r, hr⟩ : ↥J) ⊗ₜ[A] x, by simp [hmudef]⟩
  have hrange : LinearMap.range mu = J • (⊤ : Submodule A F) := le_antisymm hle hge
  set ee : (↥J ⊗[A] F) ≃ₗ[A] ↥(J • (⊤ : Submodule A F)) :=
    (LinearEquiv.ofInjective mu hmuinj).trans (LinearEquiv.ofEq _ _ hrange) with heedef
  have hcomp : (J • (⊤ : Submodule A F)).subtype.comp (ee : (↥J ⊗[A] F) →ₗ[A] _) = mu := by
    ext x; rfl
  -- `rTensor B mu` is injective.
  have hswap := swapEquiv_naturality (B := B) (F := F) J.subtype
  have hbase : Function.Injective
      (LinearMap.rTensor F (LinearMap.rTensor B J.subtype)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ htor
  have hmid : Function.Injective (LinearMap.rTensor B (LinearMap.rTensor F J.subtype)) := by
    have hcompinj : Function.Injective
        (((swapEquiv (A := A) (B := B) A F).toLinearMap.comp
          (LinearMap.rTensor B (LinearMap.rTensor F J.subtype)))) := by
      rw [hswap]
      exact hbase.comp (swapEquiv (A := A) (B := B) (↥J) F).injective
    rw [LinearMap.coe_comp] at hcompinj
    exact Function.Injective.of_comp hcompinj
  have hkey : Function.Injective (LinearMap.rTensor B mu) := by
    rw [hmudef, LinearMap.rTensor_comp]
    exact (LinearEquiv.rTensor B (TensorProduct.lid A F)).injective.comp hmid
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨w, rfl⟩ := (LinearEquiv.rTensor B ee).surjective z
  have hw : LinearMap.rTensor B mu w = 0 := by
    rw [← hcomp, LinearMap.rTensor_comp_apply]
    exact hz
  rw [(injective_iff_map_eq_zero _).mp hkey w hw, map_zero]

/-- SUB-LEAF 2 (change of rings). -/
theorem rTensor_injective_of_isTorsionBySet
    {J : Ideal A} (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (hP : Module.IsTorsionBySet A P J) (hQ : Module.IsTorsionBySet A Q J)
    (f : P →ₗ[A] Q) (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor B f) := by
  classical
  letI : Module (A ⧸ J) P := hP.module
  letI : Module (A ⧸ J) Q := hQ.module
  haveI : IsScalarTower A (A ⧸ J) P := hP.isScalarTower
  haveI : IsScalarTower A (A ⧸ J) Q := hQ.isScalarTower
  have hsurj : Function.Surjective (algebraMap A (A ⧸ J)) := Ideal.Quotient.mk_surjective
  haveI hflat' : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B J).symm.toLinearEquiv
  set f' : P →ₗ[A ⧸ J] Q := f.extendScalarsOfSurjective hsurj with hf'def
  have hf' : Function.Injective f' := hf
  have hinj2 : Function.Injective (LinearMap.rTensor ((A ⧸ J) ⊗[A] B) f') :=
    Module.Flat.rTensor_preserves_injective_linearMap f' hf'
  have hnat : ∀ y : P ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] B),
      LinearMap.rTensor B f
          (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) P B y)
        = TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) Q B
            (LinearMap.rTensor ((A ⧸ J) ⊗[A] B) f' y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        have hsm : f (a • p) = a • f p := f'.map_smul a p
        have hfp : f' p = f p := rfl
        simp [hsm, hfp]
      | add u v hu hv => simp [TensorProduct.tmul_add, hu, hv]
    | add u v hu hv => simp [hu, hv]
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) P B).surjective x
  rw [hnat y] at hx
  have hy := (injective_iff_map_eq_zero _).mp hinj2 y
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) Q B).injective
      (by rw [hx, map_zero]))
  rw [hy, map_zero]

/-- STEP 1 of Stacks 00MK. -/
theorem rTensor_subtype_injective_of_smul_top_le
    {J : Ideal A} (htor : Function.Injective (LinearMap.rTensor B J.subtype))
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    {F : Type u} [AddCommGroup F] [Module A F] [Module.Flat A F]
    {K : Submodule A F} (hK : J • (⊤ : Submodule A F) ≤ K) :
    Function.Injective (LinearMap.rTensor B K.subtype) := by
  classical
  set K' : Submodule A F := J • (⊤ : Submodule A F) with hK'def
  set iota : ↥K' →ₗ[A] ↥K := Submodule.inclusion hK with hiotadef
  set Kb : Submodule A (F ⧸ K') := K.map K'.mkQ with hKbdef
  set p : ↥K →ₗ[A] ↥Kb :=
    K'.mkQ.restrict (p := K) (q := Kb) (fun x hx => Submodule.mem_map_of_mem hx) with hpdef
  have hpsurj : Function.Surjective p := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hexact : Function.Exact iota p := by
    intro y
    constructor
    · intro hy
      have hmem : (y : F) ∈ K' := by
        have h := congrArg Subtype.val hy
        simpa [hpdef, LinearMap.restrict_apply, Submodule.Quotient.mk_eq_zero] using h
      exact ⟨⟨(y : F), hmem⟩, by ext; rfl⟩
    · rintro ⟨z, rfl⟩
      ext
      exact (Submodule.Quotient.mk_eq_zero _).mpr z.2
  -- `↥Kb` and `F ⧸ K'` are killed by `J`.
  have hkill : ∀ j ∈ J, ∀ z : F ⧸ K', j • z = 0 := by
    intro j hj z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K' z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Submodule.smul_mem_smul hj Submodule.mem_top)
  have htorQ : Module.IsTorsionBySet A (F ⧸ K') J := fun z j => hkill j j.2 z
  have htorP : Module.IsTorsionBySet A ↥Kb J :=
    fun x j => Subtype.ext (hkill j j.2 (x : F ⧸ K'))
  refine (injective_iff_map_eq_zero _).mpr fun xi hxi => ?_
  have hbar : LinearMap.rTensor B p xi = 0 := by
    refine rTensor_injective_of_isTorsionBySet hflat htorP htorQ Kb.subtype
      Subtype.val_injective ?_
    have hcomp : (Kb.subtype).comp p = K'.mkQ.comp K.subtype := by ext x; rfl
    rw [← LinearMap.rTensor_comp_apply, hcomp, LinearMap.rTensor_comp_apply, hxi, map_zero,
      map_zero]
  obtain ⟨xi', rfl⟩ := (_root_.rTensor_exact B hexact hpsurj xi).mp hbar
  have hzero : LinearMap.rTensor B K'.subtype xi' = 0 := by
    have hcomp : K.subtype.comp iota = K'.subtype := by ext x; rfl
    rw [← hcomp, LinearMap.rTensor_comp_apply]
    exact hxi
  have hxi'0 : xi' = 0 :=
    (injective_iff_map_eq_zero _).mp
      (rTensor_smul_top_subtype_injective_of_flat (B := B) htor (F := F)) xi' hzero
  rw [hxi'0, map_zero]

/-- THE PRESENTATION TRICK: transfer STEP 1 across a flat presentation `G ↠ N`. -/
theorem rTensor_subtype_injective_of_flat_presentation
    {J : Ideal A} (htor : Function.Injective (LinearMap.rTensor B J.subtype))
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    {N : Type u} [AddCommGroup N] [Module A N] (KL : Submodule A N)
    {G : Type u} [AddCommGroup G] [Module A G] [Module.Flat A G]
    (pi : G →ₗ[A] N) (hpisurj : Function.Surjective pi)
    (hJG : J • (⊤ : Submodule A G) ≤ KL.comap pi) :
    Function.Injective (LinearMap.rTensor B KL.subtype) := by
  classical
  have hRKt : LinearMap.ker pi ≤ KL.comap pi := by
    intro x hx
    simp only [Submodule.mem_comap]
    rw [show pi x = 0 from hx]
    exact zero_mem _
  have hstep1 : Function.Injective (LinearMap.rTensor B (KL.comap pi).subtype) :=
    rTensor_subtype_injective_of_smul_top_le htor hflat hJG
  set q : ↥(KL.comap pi) →ₗ[A] ↥KL :=
    pi.restrict (p := KL.comap pi) (q := KL) (fun x hx => hx) with hqdef
  have hqsurj : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := hpisurj y
    exact ⟨⟨g, hy⟩, rfl⟩
  have hqKt : pi.comp (KL.comap pi).subtype = KL.subtype.comp q := by ext x; rfl
  have hexactT :
      Function.Exact (LinearMap.rTensor B (LinearMap.ker pi).subtype) (LinearMap.rTensor B pi) :=
    _root_.rTensor_exact B (LinearMap.exact_subtype_ker_map pi) hpisurj
  refine (injective_iff_map_eq_zero _).mpr fun xi hxi => ?_
  obtain ⟨xit, hxit⟩ := LinearMap.rTensor_surjective B hqsurj xi
  have hker :
      LinearMap.rTensor B pi (LinearMap.rTensor B (KL.comap pi).subtype xit) = 0 := by
    rw [← LinearMap.rTensor_comp_apply, hqKt, LinearMap.rTensor_comp_apply, hxit, hxi]
  obtain ⟨rho, hrho⟩ := (hexactT _).mp hker
  have hxiteq : LinearMap.rTensor B (Submodule.inclusion hRKt) rho = xit := by
    refine hstep1 ?_
    rw [← LinearMap.rTensor_comp_apply,
      show (KL.comap pi).subtype.comp (Submodule.inclusion hRKt) = (LinearMap.ker pi).subtype from
        by ext; rfl, hrho]
  have hq0 : q.comp (Submodule.inclusion hRKt) = 0 := LinearMap.ext fun x => Subtype.ext x.2
  rw [← hxit, ← hxiteq, ← LinearMap.rTensor_comp_apply, hq0, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

/-- THE INDUCTION (step 2 of Stacks 00MK). -/
theorem rTensor_subtype_injective_of_pow_smul_top_le
    {J : Ideal A} (htor : Function.Injective (LinearMap.rTensor B J.subtype))
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J)) :
    ∀ (n : ℕ) {F : Type u} [AddCommGroup F] [Module A F] [Module.Flat A F]
      {K : Submodule A F}, (J ^ n) • (⊤ : Submodule A F) ≤ K →
      Function.Injective (LinearMap.rTensor B K.subtype) := by
  classical
  intro n
  induction n with
  | zero =>
    intro F _ _ _ K hK
    have hKtop : K = ⊤ := by
      refine top_le_iff.mp ?_
      simpa using hK
    subst hKtop
    have : (⊤ : Submodule A F).subtype = (Submodule.topEquiv : _ ≃ₗ[A] F).toLinearMap := rfl
    rw [this]
    exact (LinearEquiv.rTensor B (Submodule.topEquiv : _ ≃ₗ[A] F)).injective
  | succ n ih =>
    intro F _ _ _ K hK
    set L : Submodule A F := K ⊔ (J ^ n) • (⊤ : Submodule A F) with hLdef
    have hKL : K ≤ L := le_sup_left
    have hLinj : Function.Injective (LinearMap.rTensor B L.subtype) := ih le_sup_right
    -- `J • L ≤ K`, from `J • (J ^ n • ⊤) = J ^ (n+1) • ⊤ ≤ K`.
    have hpow : J • ((J ^ n) • (⊤ : Submodule A F)) = (J ^ (n + 1)) • (⊤ : Submodule A F) := by
      rw [pow_succ', mul_smul]
    have hJL : J • L ≤ K := by
      refine Submodule.smul_le.mpr fun r hr x hx => ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hLdef ▸ hx)
      rw [smul_add]
      exact add_mem (K.smul_mem r hy) (hK (hpow ▸ Submodule.smul_mem_smul hr hz))
    -- Apply the presentation trick inside `↥L`, to `KL = K` viewed in `↥L`.
    set KL : Submodule A ↥L := K.comap L.subtype with hKLdef
    have hJG : J • (⊤ : Submodule A (↥L →₀ A))
        ≤ KL.comap (Finsupp.linearCombination A (id : ↥L → ↥L)) := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      simp only [Submodule.mem_comap, hKLdef, map_smul]
      show ((r • Finsupp.linearCombination A (id : ↥L → ↥L) x : ↥L) : F) ∈ K
      exact hJL (Submodule.smul_mem_smul hr
        (Finsupp.linearCombination A (id : ↥L → ↥L) x).2)
    have hKLinj : Function.Injective (LinearMap.rTensor B KL.subtype) :=
      rTensor_subtype_injective_of_flat_presentation htor hflat KL
        (Finsupp.linearCombination A (id : ↥L → ↥L))
        (fun y => ⟨Finsupp.single y 1, by
          rw [Finsupp.linearCombination_single, one_smul, id]⟩) hJG
    set e : ↥KL ≃ₗ[A] ↥K := Submodule.comapSubtypeEquivOfLe hKL with hedef
    have hcomp : K.subtype
        = L.subtype.comp (KL.subtype.comp (e.symm : ↥K →ₗ[A] ↥KL)) := by ext x; rfl
    rw [hcomp, LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    exact hLinj.comp (hKLinj.comp (LinearEquiv.rTensor B e.symm).injective)


end NilpotentLocalCriterion

open NilpotentLocalCriterion in
/-- **THE LOCAL CRITERION OF FLATNESS FOR A NILPOTENT IDEAL** (**PROVEN 2026-07-28**; pure
commutative algebra; [Stacks 00MK] / [Stacks 051C], Matsumura *Commutative Ring Theory*
22.1/22.3).

`J ^ N = ⊥`, `B ⧸ JB` flat over `A ⧸ J`, and `J ⊗[A] B → B` injective (which is
`Tor₁^A(A ⧸ J, B) = 0` written without derived functors) together force `B` flat over `A`.

The module docstring above records the proof in full, and in particular **corrects** the
two routes this leaf used to advertise: mathlib really has no `Tor` long exact sequence,
but neither building one nor the successive-approximation argument over
`Module.Flat.iff_forall_isTrivialRelation` is needed.  The whole content is
`NilpotentLocalCriterion.rTensor_subtype_injective_of_pow_smul_top_le`, an induction whose
only homological input is right-exactness of `- ⊗ B`.

Consumed by `Fermat.flat_quotientMap_pow_of_flat_quotientMap`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`), which is the nilpotent half of the
one-element local criterion `Fermat.flat_of_flat_quotient_isSMulRegular`. -/
theorem of_flat_quotient_of_pow_eq_bot {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (J : Ideal A) (N : ℕ) (hJnil : J ^ N = ⊥)
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    (htor : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype))) :
    Module.Flat A B := by
  have hc : (TensorProduct.lid A B).toLinearMap.comp (LinearMap.rTensor B J.subtype)
      = TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype) := by
    ext x b; simp
  have htor' : Function.Injective (LinearMap.rTensor B J.subtype) := by
    rw [← hc, LinearMap.coe_comp] at htor
    exact Function.Injective.of_comp htor
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  exact rTensor_subtype_injective_of_pow_smul_top_le htor' hflat N (F := A) (K := I)
    (by rw [hJnil]; simp)

end Module.Flat
