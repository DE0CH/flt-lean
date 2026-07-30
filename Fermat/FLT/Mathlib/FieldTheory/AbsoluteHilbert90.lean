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
public import Mathlib.FieldTheory.Perfect

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
  multiplicative `1`-cocycle `c : Γ_K → Ωˣ` inflated from `Gal(L/K)`, with `L/K` finite
  Galois, is a coboundary: `σ γ = c σ * γ` for a single `γ ∈ Ωˣ`.
* `Field.exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul` — **Kummer theory in
  the form `H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`**: if moreover `c` takes its values in `μₙ`, the `γ`
  produced above has `γⁿ` fixed by `Γ_K`, hence `γⁿ = d` for a genuine `d ∈ K`.  So the
  class of `c` is realised by an element of `Kˣ` and `γ` is an `n`-th root of it.
* `Field.isGalois_of_isAlgClosed` — the instance plumbing that makes an algebraically closed
  algebraic extension of a perfect field satisfy `[IsGalois K Ω]`, supplied as a THEOREM
  rather than an instance because at the literal base field `ℚ` the two `Algebra ℚ ℚ̄`
  instances form a diamond and `Algebra.IsAlgebraic ℚ ℚ̄` does not synthesise (see the
  `Implementation notes` below).

All three are proved; there is no `sorry` in this file.

## The ambient field is an arbitrary `Ω` with `[IsGalois K Ω]`, not `AlgebraicClosure K`

Generalised 2026-07-29 (it was stated for `AlgebraicClosure K` when the file was written).
Nothing in either proof knows what `Ω` is: they use only
`AlgEquiv.restrictNormalHom_surjective` (which needs `Normal K Ω` and `Normal K L`) and
`InfiniteGalois.mem_range_algebraMap_iff_fixed` (which needs `IsGalois K Ω`), both already
stated for a general `Ω`.  Note that `[IsGalois K Ω]` *replaces* the `[PerfectField K]`
hypothesis of the second theorem — separability of `Ω/K` is now part of the hypothesis
rather than deduced from perfectness of `K` — so the generalisation is not merely a
weakening of the ambient field, it also drops an assumption.

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
`Ω ≃ₐ[K] Ω`; a consumer holding a `Field.absoluteGaloisGroup K`-indexed cocycle can apply
them unchanged wherever that attribute is in scope.

**`[IsGalois K Ω]` is an instance argument, but at `Ω = AlgebraicClosure K` it will NOT be
found by instance search at the literal base field `ℚ`** — the two `Algebra ℚ ℚ̄` instances
form a diamond, so `Algebra.IsAlgebraic ℚ ℚ̄` and `IsAlgClosure ℚ ℚ̄` both fail to
synthesise (documented in `X0.lean`'s `mem_range_of_fixed` and worked around by hand in
`Fermat/FLT/Modularity/Patching.lean`).  Consumers must therefore discharge it locally, e.g.
`haveI : IsGalois ℚ (AlgebraicClosure ℚ) := Field.isGalois_of_isAlgClosed (AlgebraicClosure.isAlgebraic ℚ)`.
That is exactly what `isGalois_of_isAlgClosed` is for.

-/

@[expose] public section

namespace Field

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **An algebraically closed algebraic extension of a perfect field is Galois.**

Deliberately a `theorem` and not an `instance`: at the literal base field `ℚ` the two
`Algebra ℚ ℚ̄` instances form a diamond and `Algebra.IsAlgebraic ℚ ℚ̄` does not synthesise,
so `halg` has to be passed by hand (`AlgebraicClosure.isAlgebraic ℚ`) exactly as it already
is in `Fermat/FLT/Modularity/Patching.lean`.  Registering this as an instance would not
help — the failure is upstream of it, in `Algebra.IsAlgebraic`. -/
theorem isGalois_of_isAlgClosed [PerfectField K] [IsAlgClosed Ω]
    (halg : Algebra.IsAlgebraic K Ω) : IsGalois K Ω := by
  haveI : Algebra.IsAlgebraic K Ω := halg
  haveI : Normal K Ω := { toIsAlgebraic := halg, splits' := fun _ => IsAlgClosed.splits _ }
  haveI : Algebra.IsSeparable K Ω := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨⟩

/-- **Hilbert 90 for the absolute Galois group**, for a `1`-cocycle inflated from a finite
Galois subextension `L/K` of a Galois extension `Ω/K`.

`c` is a multiplicative `1`-cocycle for the action of `Gal(Ω/K)` on `Ωˣ`
(`hcoc : c (σ * τ) = c σ * σ (c τ)`) taking its values in `L` (`hcmem`) and depending only
on the restriction of `σ` to `L` (`hinfl`).  The conclusion is that `c` is a coboundary:
there is one `γ ∈ Ωˣ` with `σ γ = c σ * γ` for **every** `σ ∈ Gal(Ω/K)`.

The proof is inflation from `Gal(L/K)`.  `c` descends to `f : Gal(L/K) → Lˣ` — total
because `AlgEquiv.restrictNormalHom` is surjective, well defined by `hinfl` — and `f` is
again a cocycle, so Noether's theorem
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`, which is where
`FiniteDimensional K L` is used) supplies `β ∈ Lˣ` with `ρ β / β = f ρ`.  Its image in `Ω`
is the required `γ`, by `AlgEquiv.restrictNormalHom_apply`.

`[IsGalois K Ω]` enters only through `AlgEquiv.restrictNormalHom_surjective`, which needs
`Normal K Ω`; the intended `Ω` is an algebraic closure of `K`, but nothing here requires
that. -/
theorem exists_ne_zero_forall_absoluteGalois_apply_eq_mul [IsGalois K Ω]
    (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L]
    (c : (Ω ≃ₐ[K] Ω) → Ω)
    (hcmem : ∀ σ, c σ ∈ L) (hc0 : ∀ σ, c σ ≠ 0)
    (hcoc : ∀ σ τ, c (σ * τ) = c σ * σ (c τ))
    (hinfl : ∀ σ τ, (∀ x ∈ L, σ x = τ x) → c σ = c τ) :
    ∃ γ : Ω, γ ≠ 0 ∧ ∀ σ, σ γ = c σ * γ := by
  classical
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) :=
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
  have hval : ∀ ρ, ((f ρ : L) : Ω) = c (lift ρ) := fun ρ => rfl
  have hcf : ∀ σ, ((f (AlgEquiv.restrictNormalHom L σ) : L) : Ω) = c σ := by
    intro σ
    rw [hval]
    exact hdep _ _ (hlift _)
  have hfcoc : groupCohomology.IsMulCocycle₁ f := by
    intro ρ π
    refine Units.ext (Subtype.ext ?_)
    have h1 : c (lift (ρ * π)) = c (lift ρ * lift π) := by
      refine hdep _ _ ?_
      rw [hlift, map_mul, hlift, hlift]
    have h2 : ((ρ ((f π : L)) : L) : Ω) = (lift ρ) (c (lift π)) := by
      conv_lhs => rw [← hlift ρ]
      exact AlgEquiv.restrictNormalHom_apply L (lift ρ) _
    show ((f (ρ * π) : L) : Ω)
      = ((((ρ • f π * f ρ : Lˣ) : L)) : Ω)
    rw [hval, h1, hcoc]
    simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    push_cast
    rw [h2, hval]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hfcoc
  refine ⟨((β : L) : Ω), by exact_mod_cast Units.ne_zero β, fun σ => ?_⟩
  have hb := hβ (AlgEquiv.restrictNormalHom L σ)
  rw [div_eq_iff_eq_mul] at hb
  have hb' := congrArg (fun y : Lˣ => ((y : L) : Ω)) hb
  simp only [AlgEquiv.smul_units_def, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hb'
  push_cast at hb'
  rw [AlgEquiv.restrictNormalHom_apply L σ (β : L)] at hb'
  rw [hb', hcf]

/-- **Kummer theory for `Γ_K` in the form `H¹(Γ_K, μₙ) ≅ Kˣ/(Kˣ)ⁿ`.**

If the cocycle `c` of `exists_ne_zero_forall_absoluteGalois_apply_eq_mul` takes its values
in the `n`-th roots of unity, the trivialising element `γ` has `γⁿ` fixed by every
`σ ∈ Γ_K` — because `σ (γⁿ) = (c σ)ⁿ γⁿ = γⁿ` — hence `γⁿ = d` for a genuine `d ∈ K`: the
class of `c` in `H¹(Γ_K, μₙ)` is the class of `d` in `Kˣ/(Kˣ)ⁿ`, and `γ` is an `n`-th root
of `d` in `Ω`.

This is the form consumed by the sextic-twist descent at `j = 0` in
`Fermat/FLT/ModularCurve/X0.lean` (`n = 3`, `K = ℚ`, `Ω = ℚ̄`) and, at `n = 2`, by
`Field.exists_sq_eq_algebraMap_of_quadraticChar` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/QuarticTwist.lean`.

`[IsGalois K Ω]` is what turns "fixed by `Gal(Ω/K)`" into "in `K`"
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`).  It replaces the `[PerfectField K]`
hypothesis this theorem carried while it was stated for `AlgebraicClosure K`: perfectness
of `K` was only ever used to make `K̄/K` separable, which is now assumed directly.

`hn : n ≠ 0` is genuinely needed and not decoration: at `n = 0` the hypothesis `hcpow`
degenerates to `1 = 1`, so it no longer forces `c σ ≠ 0` and the cocycle need not take
values in `Ωˣ` at all. -/
theorem exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul [IsGalois K Ω]
    (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ} (hn : n ≠ 0)
    (c : (Ω ≃ₐ[K] Ω) → Ω)
    (hcmem : ∀ σ, c σ ∈ L) (hcpow : ∀ σ, c σ ^ n = 1)
    (hcoc : ∀ σ τ, c (σ * τ) = c σ * σ (c τ))
    (hinfl : ∀ σ τ, (∀ x ∈ L, σ x = τ x) → c σ = c τ) :
    ∃ (γ : Ω) (d : K), γ ≠ 0 ∧
      γ ^ n = algebraMap K Ω d ∧
      ∀ σ, σ γ = c σ * γ := by
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ h
    have hσ := hcpow σ
    rw [h, zero_pow hn] at hσ
    exact zero_ne_one hσ
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_ne_zero_forall_absoluteGalois_apply_eq_mul L c hcmem hc0 hcoc hinfl
  have hfix : ∀ σ : Ω ≃ₐ[K] Ω, σ (γ ^ n) = γ ^ n := by
    intro σ
    rw [map_pow, hγ σ, mul_pow, hcpow σ, one_mul]
  obtain ⟨d, hd⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (γ ^ n)).mpr hfix
  exact ⟨γ, d, hγ0, hd.symm, hγ⟩

end Field
