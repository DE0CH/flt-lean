/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!

# Hilbert 90 for the ABSOLUTE Galois group, and `H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`

Proposed new Mathlib material.  The pin has Noether's Hilbert 90 only for a **finite**
extension (`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`, whose file
lists *"develop Galois cohomology to extend Noether's result to infinite Galois
extensions"* as an explicit TODO).  This file supplies exactly the case of that TODO which
the descent arguments in `Fermat/FLT/ModularCurve/X0.lean` need, and proves it by
inflation from a finite level.

## Main statements

* `Field.exists_ne_zero_forall_absoluteGalois_apply_eq_mul` — **Hilbert 90 for `Γ_K`**: a
  multiplicative `1`-cocycle `c : Γ_K → K̄ˣ` inflated from `Gal(L/K)`, with `L/K` finite
  Galois, is a coboundary: `σ γ = c σ * γ` for a single `γ ∈ K̄ˣ`.
* `Field.exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul` — **Kummer theory in
  the form `H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`**: if moreover `c` takes its values in `μₙ`, the `γ`
  produced above has `γⁿ` fixed by `Γ_K`, hence `γⁿ = d` for a genuine `d ∈ K`.  So the
  class of `c` is realised by an element of `Kˣ` and `γ` is an `n`-th root of it.

Both are proved; there is no `sorry` in this file.

## Why "inflated from a finite level" is the right continuity hypothesis

`H¹(Γ_K, K̄ˣ) = 1` is FALSE for arbitrary (non-continuous) cochains; the classical proof
— Artin's linear independence of characters, which is what mathlib's finite-level theorem
runs on — needs the cocycle to factor through a finite quotient.  For a cocycle with
values in the finite group `μₙ` (given the discrete topology) continuity is *equivalent*
to factoring through `Gal(L/K)` for some finite Galois `L/K`, so the hypothesis here is
not a restriction in the intended application, merely a concrete presentation of it.

The hypothesis is stated *pointwise* — "if `σ` and `τ` agree on `L` then `c σ = c τ`" —
rather than as a factorisation through `AlgEquiv.restrictNormalHom`, because pointwise
agreement is what a consumer can actually establish: the level `L` is typically generated
by the coordinates of finitely many algebraic points, and one checks agreement there.

## Why this is Kummer theory WITHOUT `μₙ ⊆ K`

`H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ` comes from the Kummer sequence `1 → μₙ → K̄ˣ → K̄ˣ → 1` together
with `H¹(Γ_K, K̄ˣ) = 1`, i.e. Hilbert 90.  It does **not** need `μₙ ⊆ K`; that hypothesis
is needed only for the *other* reading, `Hom(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`, in which the cocycle is
a homomorphism.  When `μₙ ⊄ K` the Galois action on `μₙ` is nontrivial and `c` is a genuine
cocycle — which is precisely the situation at `j = 0` in `X0.lean`, where `n = 3` and
`Γ_ℚ` acts on `μ₃` through the quadratic character of `ℚ(ζ₃)`.

**A tempting shortcut is FALSE and worth recording**: one may *not* conclude that the
cubic field cut out is a cyclic cubic field.  A cyclic cubic field is never of the form
`ℚ(∛d)` — that would force `ζ₃` into a field of odd degree over `ℚ` — and it is exactly
the cocycle condition, as opposed to the homomorphism condition, that excludes them.

## Implementation notes

`Field.absoluteGaloisGroup K` is a plain `def` for `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`
and is **not** reducible in mathlib, so `σ x` does not even elaborate for
`σ : Field.absoluteGaloisGroup K` unless some downstream file has marked it reducible (this
project's `Fermat/FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` does).  To
keep this file free of that dependency the statements below are phrased directly in terms of
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`; a consumer holding a
`Field.absoluteGaloisGroup K`-indexed cocycle can apply them unchanged wherever that
attribute is in scope.

-/

@[expose] public section

namespace Field

variable {K : Type*} [Field K]

/-- **Hilbert 90 for the absolute Galois group**, for a `1`-cocycle inflated from a finite
Galois subextension `L/K` of `K̄/K`.

`c` is a multiplicative `1`-cocycle for the action of `Γ_K` on `K̄ˣ`
(`hcoc : c (σ * τ) = c σ * σ (c τ)`) taking its values in `L` (`hcmem`) and depending only
on the restriction of `σ` to `L` (`hinfl`).  The conclusion is that `c` is a coboundary:
there is one `γ ∈ K̄ˣ` with `σ γ = c σ * γ` for **every** `σ ∈ Γ_K`.

The proof is inflation from `Gal(L/K)`.  `c` descends to `f : Gal(L/K) → Lˣ` — total
because `AlgEquiv.restrictNormalHom` is surjective, well defined by `hinfl` — and `f` is
again a cocycle, so Noether's theorem
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`, which is where
`FiniteDimensional K L` is used) supplies `β ∈ Lˣ` with `ρ β / β = f ρ`.  Its image in `K̄`
is the required `γ`, by `AlgEquiv.restrictNormalHom_apply`. -/
theorem exists_ne_zero_forall_absoluteGalois_apply_eq_mul
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L]
    (c : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)
    (hcmem : ∀ σ, c σ ∈ L) (hc0 : ∀ σ, c σ ≠ 0)
    (hcoc : ∀ σ τ, c (σ * τ) = c σ * σ (c τ))
    (hinfl : ∀ σ τ, (∀ x ∈ L, σ x = τ x) → c σ = c τ) :
    ∃ γ : AlgebraicClosure K, γ ≠ 0 ∧ ∀ σ, σ γ = c σ * γ := by
  classical
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) L) :=
    AlgEquiv.restrictNormalHom_surjective _
  choose lift hlift using hsurj
  -- `c σ` depends only on `σ|_L`, in the form needed to descend it along `restrictNormalHom`
  have hdep : ∀ σ τ, AlgEquiv.restrictNormalHom L σ = AlgEquiv.restrictNormalHom L τ →
      c σ = c τ := by
    intro σ τ h
    refine hinfl σ τ fun x hx => ?_
    have hσ := AlgEquiv.restrictNormalHom_apply L σ ⟨x, hx⟩
    have hτ := AlgEquiv.restrictNormalHom_apply L τ ⟨x, hx⟩
    rw [← hσ, ← hτ, h]
  -- the descended cocycle at the finite level `L`
  set f : (L ≃ₐ[K] L) → Lˣ := fun ρ =>
    Units.mk0 (⟨c (lift ρ), hcmem _⟩ : L)
      (fun h => hc0 (lift ρ) (by simpa using congrArg Subtype.val h)) with hfdef
  have hval : ∀ ρ, ((f ρ : L) : AlgebraicClosure K) = c (lift ρ) := fun ρ => rfl
  have hcf : ∀ σ, ((f (AlgEquiv.restrictNormalHom L σ) : L) : AlgebraicClosure K) = c σ := by
    intro σ
    rw [hval]
    exact hdep _ _ (hlift _)
  have hfcoc : groupCohomology.IsMulCocycle₁ f := by
    intro ρ π
    refine Units.ext (Subtype.ext ?_)
    have h1 : c (lift (ρ * π)) = c (lift ρ * lift π) := by
      refine hdep _ _ ?_
      rw [hlift, map_mul, hlift, hlift]
    have h2 : ((ρ ((f π : L)) : L) : AlgebraicClosure K) = (lift ρ) (c (lift π)) := by
      conv_lhs => rw [← hlift ρ]
      exact AlgEquiv.restrictNormalHom_apply L (lift ρ) _
    show ((f (ρ * π) : L) : AlgebraicClosure K)
      = ((((ρ • f π * f ρ : Lˣ) : L)) : AlgebraicClosure K)
    rw [hval, h1, hcoc]
    simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    push_cast
    rw [h2, hval]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hfcoc
  refine ⟨((β : L) : AlgebraicClosure K), by exact_mod_cast Units.ne_zero β, fun σ => ?_⟩
  have hb := hβ (AlgEquiv.restrictNormalHom L σ)
  rw [div_eq_iff_eq_mul] at hb
  have hb' := congrArg (fun y : Lˣ => ((y : L) : AlgebraicClosure K)) hb
  simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hb'
  push_cast at hb'
  rw [AlgEquiv.restrictNormalHom_apply L σ (β : L)] at hb'
  rw [hb', hcf]

/-- **Kummer theory for `Γ_K` in the form `H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`.**

If the cocycle `c` of `exists_ne_zero_forall_absoluteGalois_apply_eq_mul` takes its values
in the `n`-th roots of unity, the trivialising element `γ` has `γⁿ` fixed by every
`σ ∈ Γ_K` — because `σ (γⁿ) = (c σ)ⁿ γⁿ = γⁿ` — hence `γⁿ = d` for a genuine `d ∈ K`: the
class of `c` in `H¹(Γ_K, μₙ)` is the class of `d` in `Kˣ/(Kˣ)ⁿ`, and `γ` is an `n`-th root
of `d` in `K̄`.

This is the form consumed by the sextic-twist descent at `j = 0` in
`Fermat/FLT/ModularCurve/X0.lean` (`n = 3`, `K = ℚ`).

`[PerfectField K]` is what turns "fixed by `Γ_K`" into "in `K`"
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`); it holds for every field of
characteristic `0`, in particular for `ℚ`.

`hn : n ≠ 0` is genuinely needed and not decoration: at `n = 0` the hypothesis `hcpow`
degenerates to `1 = 1`, so it no longer forces `c σ ≠ 0` and the cocycle need not take
values in `K̄ˣ` at all. -/
theorem exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul [PerfectField K]
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hn : n ≠ 0)
    (c : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)
    (hcmem : ∀ σ, c σ ∈ L) (hcpow : ∀ σ, c σ ^ n = 1)
    (hcoc : ∀ σ τ, c (σ * τ) = c σ * σ (c τ))
    (hinfl : ∀ σ τ, (∀ x ∈ L, σ x = τ x) → c σ = c τ) :
    ∃ (γ : AlgebraicClosure K) (d : K), γ ≠ 0 ∧
      γ ^ n = algebraMap K (AlgebraicClosure K) d ∧
      ∀ σ, σ γ = c σ * γ := by
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h
    have hσ := hcpow σ
    rw [h, zero_pow hn] at hσ
    exact zero_ne_one hσ
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_ne_zero_forall_absoluteGalois_apply_eq_mul L c hcmem hc0 hcoc hinfl
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ (γ ^ n) = γ ^ n := by
    intro σ
    rw [map_pow, hγ σ, mul_pow, hcpow σ, one_mul]
  obtain ⟨d, hd⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (γ ^ n)).mpr hfix
  exact ⟨γ, d, hγ0, hd.symm, hγ⟩

end Field
