/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import Fermat.FLT.Mathlib.RingTheory.Norm.Quadratic
public import Fermat.FLT.Mathlib.LinearAlgebra.Dimension.IsQuadraticExtension

import Mathlib.RingTheory.Norm.Transitivity

/-!

# Quadratic twists of elliptic curves

Let `E` be an elliptic curve over a field `K` and let `L/K` be a separable quadratic extension.
The *quadratic twist* `Eᴸ` of `E` by `L/K` is an elliptic curve over `K`, well-defined up to
`K`-isomorphism, characterised by the following two properties:

* `Eᴸ` becomes isomorphic to `E` over `L` (but is not isomorphic to `E` over `K`, at least
  when `j(E) ∉ {0, 1728}`);
* the isomorphism `φ : Eᴸ ≅ E` over `L` can be chosen so that the Galois action on the points
  of `Eᴸ` corresponds, under `φ`, to the Galois action on the points of `E` twisted by the
  quadratic character `χ` of `L/K`. More precisely, for every field `M` in a tower
  `K ⊆ L ⊆ M` and every `σ ∈ Aut(M/K)`, we have `φ(σ P) = χ(σ) • σ(φ P)` on `M`-points,
  where `χ(σ) = 1` if `σ` fixes `L` pointwise and `χ(σ) = -1` otherwise.

Taking `M` to be a separable closure of `K`, the second property says exactly that the Galois
representations attached to `Eᴸ` (for example on torsion points, via
`FLT.KnownIn1980s.EllipticCurves.Torsion`) are the twists by `χ` of those attached to `E`.
Taking `M = L` and `σ` the nontrivial element of `Gal(L/K)`, it says `φ(σ P) = -σ(φ P)`,
which is the classical description of the twist by Galois descent: `Eᴸ` is the descent to `K`
of `E ×_K L` along the twisted action `σ ↦ (-1) ∘ σ`.

Concretely, when `char K ≠ 2` we may complete the square and assume
`E : y² = x³ + a₂x² + a₄x + a₆`, and `L = K(√d)`; then `Eᴸ : y² = x³ + da₂x² + d²a₄x + d³a₆`,
with isomorphism `φ : (x, y) ↦ (x/d, y/(d√d))` over `L`.

## The generality

Twisting by a separable quadratic extension `L/K` is the right generality for quadratic twists,
uniformly in all characteristics:

* Quadratic twists of `E/K` are classified by the continuous characters
  `χ : Gal(Kˢᵉᵖ/K) → {±1} = μ₂ ⊆ Aut(E)`, and by Galois theory the nontrivial such characters
  correspond exactly to separable quadratic extensions `L/K` (take the fixed field of `ker χ`).
  In characteristic 2 the separable quadratic extensions are the Artin–Schreier extensions
  `L = K(℘⁻¹(d))`, which are invisible to the familiar "twist by `d ∈ K^×/(K^×)²`"
  parametrisation available only when `char K ≠ 2`.
* Every degree 2 field extension is automatically normal; separability is precisely the
  condition making `Aut(L/K)` have order 2 rather than 1. An inseparable quadratic extension
  has trivial automorphism group, hence carries no quadratic character and produces no twist.
* A mild generalisation, deliberately not adopted here: one can twist by an arbitrary étale
  quadratic `K`-algebra, allowing the split algebra `K × K` which corresponds to the trivial
  character and gives back `E` itself. This makes twisting an action of the group
  `H¹(Gal(Kˢᵉᵖ/K), ℤ/2)` on curves at the cost of formalisation noise; all the content is in
  the field case.
* When `j(E) ∈ {0, 1728}` the curve has automorphisms beyond `±1` and hence also quartic,
  sextic (and, in characteristics 2 and 3, wilder) twists; but the *quadratic* twist by `L/K`,
  i.e. by the cocycle valued in `{±1} ⊆ Aut(E)`, is defined for every `E`, and everything below
  except the two classification statements holds with no hypothesis on `j`.

## Main definitions and statements

The basic algebraic theory of the twist is carried out in full: the explicit Weierstrass model
(`quadraticTwistOf`, `quadraticTwistBy`), its ellipticity, its independence of the choice of
generator of `L/K` (`exists_smul_quadraticTwistBy_eq`), the invariance of the `j`-invariant
(`j_quadraticTwist`), and the fact that twisting is an involution up to `K`-isomorphism
(`exists_smul_quadraticTwist_quadraticTwist_eq`), together with the Galois-theoretic
statements: the isomorphism on points over `L` and its `χ`-twisted equivariance, and the
classification of forms of `E`. The reduction-theoretic statements are in
`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction`.

* `WeierstrassCurve.quadraticTwistOf`, `WeierstrassCurve.quadraticTwistBy` and
  `WeierstrassCurve.quadraticTwist E L` : an explicit Weierstrass model of the quadratic twist,
  uniform in the characteristic — parametrised respectively by a pair `(t, n)`, by a generator
  `θ` of `L/K` (with `t`, `n` its trace and norm), and by the extension `L/K` itself.
* `WeierstrassCurve.quadraticTwistPointEquiv E L M` : the isomorphism `Eᴸ(M) ≅ E(M)` of groups
  of `M`-points, for every field `M` in a tower `K ⊆ L ⊆ M`, natural in `M`
  (`quadraticTwistPointEquiv_map`).
* `WeierstrassCurve.quadraticTwistPointEquiv_galois` : the key statement
  `φ(σ P) = χ(σ) • σ(φ P)` above.
* `WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist` : for `j(E) ∉ {0, 1728}`,
  a curve over `K` becoming isomorphic to `E` over `L` is isomorphic over `K` to `E` or to its
  quadratic twist.

## Design notes

* "Separable quadratic extension" is spelled as the pair of mathlib typeclasses
  `[Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]` (the former is free of rank
  2, which over a field just means `[L:K] = 2`).
* A Weierstrass model of the twist is well defined only up to `K`-isomorphism, i.e. up to the
  action of `WeierstrassCurve.VariableChange K` (over a field, isomorphisms of Weierstrass
  curves are exactly the admissible changes of variables), and the isomorphism `φ` over `L` is
  well defined only up to composition with an `L`-automorphism of `E`. Here `quadraticTwist`
  is an explicit model, depending on a choice of generator of `L/K` which is harmless by
  `exists_smul_quadraticTwistBy_eq`, while `quadraticTwistPointEquiv` is a *choice*, pinned
  down up to exactly this ambiguity by the theorems about it. Note that
  `quadraticTwistPointEquiv_galois` is insensitive to replacing `φ` by `-φ`, so the sign
  ambiguity in `φ` (which is the whole ambiguity, generically) is harmless.
* The isomorphism over `L` is recorded twice: once at the level of Weierstrass equations, as a
  change of variables over `L` (`exists_smul_quadraticTwist_baseChange_eq`), and once at the
  level of points, as an `AddEquiv` on `M`-points for every `M` in a tower `K ⊆ L ⊆ M`,
  natural for `L`-algebra maps (`quadraticTwistPointEquiv_map`). The point-level form is the
  one consumed by Galois representations.

## TODO

* Explicit Artin–Schreier formulas for the twist in characteristic 2 (twisting
  `y² + a₁xy + a₃y = x³ + ⋯` by `L = K(℘⁻¹(d))` modifies `a₂` by `d·a₁²`, etc.), analogous to
  `quadraticTwist_of_two_ne_zero` below.
* Galois descent for points, `E(K) ≃ E(L)^{Gal(L/K)}`, and the resulting statement that
  `E(K) × Eᴸ(K) → E(L)` has kernel and cokernel killed by 2; over a number field this gives
  `rank E(L) = rank E(K) + rank Eᴸ(K)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.§10, X.§2 and X.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points
open Algebra.IsQuadraticExtension

/-! ### Separable quadratic extensions and their quadratic characters

Mathlib's `Algebra.IsQuadraticExtension K L` says that `L` is free of rank 2 over `K`, so for
field extensions it just means `[L:K] = 2`; we add separability as a further hypothesis
`Algebra.IsSeparable K L` throughout. -/

section QuadraticCharacter

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable [Algebra.IsQuadraticExtension K L]

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

variable [Algebra.IsSeparable K L]

end QuadraticCharacter

/-! ### The quadratic twist -/

namespace WeierstrassCurve

universe u

section QuadraticTwistOfRing

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by parameters `t`, `n`, to be
thought of as the trace and norm of a generator `θ` of a separable quadratic extension `L/K`
(see `WeierstrassCurve.quadraticTwistBy`), so that `θ² = tθ - n` and `D := t² - 4n` is the
discriminant of the minimal polynomial of `θ`, nonzero exactly when `θ` is separable.

The construction: writing the equation of `E` as `y² + A(x)y = f(x)` with `A(x) = a₁x + a₃`,
the functions `x` and `Y := (t - 2θ)y - θ·A(x)` on `E` are invariant under the Galois action
twisted by the quadratic character of `L/K`, and satisfy
`Y² + t·A(x)·Y = D·(y² + A(x)y) - n·A(x)²`; clearing denominators via `(x, Y) ↦ (Dx, DY)`
turns this relation into the Weierstrass model below of the twist:

`y² + ta₁·xy + Dta₃·y = x³ + (Da₂ - na₁²)·x² + (D²a₄ - 2Dna₁a₃)·x + (D³a₆ - D²na₃²)`.

Its discriminant is `D⁶·Δ(E)` (`Δ_quadraticTwistOf`), so the twist of an elliptic curve is
elliptic when `D ≠ 0` (`isElliptic_quadraticTwistOf`), with the same `j`-invariant
(`j_quadraticTwistOf`).

Sanity checks. If `char K ≠ 2` we may take `θ = √d`, so `t = 0`, `n = -d`, `D = 4d`; for
`E : y² = x³ + a₂x² + a₄x + a₆` the model is `y² = x³ + 4da₂x² + 16d²a₄x + 64d³a₆`, the
classical twist by `4d ≡ d mod (K^×)²`. If `char K = 2` we may take `θ` with `θ² + θ = d`
(Artin–Schreier), so `t = 1`, `n = -d`, `D = 1`; for ordinary `E : y² + xy = x³ + a₂x² + a₆`
the model is the classical twist `y² + xy = x³ + (a₂ + d)x² + a₆`, and for supersingular
`E : y² + a₃y = x³ + a₄x + a₆` it is `y² + a₃y = x³ + a₄x + (a₆ + da₃²)`. -/
def quadraticTwistOf (t n : A) : WeierstrassCurve A where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

variable (t n : A)

theorem c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [quadraticTwistOf, c₄, b₂, b₄]
  ring

theorem Δ_quadraticTwistOf : (E.quadraticTwistOf t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [quadraticTwistOf, Δ, b₂, b₄, b₆, b₈]
  ring

theorem c₆_quadraticTwistOf : (E.quadraticTwistOf t n).c₆ = (t ^ 2 - 4 * n) ^ 3 * E.c₆ := by
  simp only [quadraticTwistOf, c₆, b₂, b₄, b₆]
  ring

theorem b₂_quadraticTwistOf : (E.quadraticTwistOf t n).b₂ = (t ^ 2 - 4 * n) * E.b₂ := by
  simp only [quadraticTwistOf, b₂]; ring

theorem b₄_quadraticTwistOf : (E.quadraticTwistOf t n).b₄ = (t ^ 2 - 4 * n) ^ 2 * E.b₄ := by
  simp only [quadraticTwistOf, b₄]; ring

theorem b₆_quadraticTwistOf : (E.quadraticTwistOf t n).b₆ = (t ^ 2 - 4 * n) ^ 3 * E.b₆ := by
  simp only [quadraticTwistOf, b₆]; ring

/-- The quadratic twist commutes with a ring homomorphism `f` (in particular with base change):
`(E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n)`. -/
theorem quadraticTwistOf_map {B : Type*} [CommRing B] (f : A →+* B) :
    (E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n) := by
  ext <;>
    simp only [quadraticTwistOf, map_a₁, map_a₂,
      map_a₃, map_a₄, map_a₆, map_mul, map_sub,
      map_pow, map_ofNat]

/-- The node-polynomial constant `κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄` of the quadratic twist by `(t, n)`
in terms of that of `E`: `κ_W = D³ κ - D² n a₁² c₄` where `D = t² - 4n`. -/
theorem kappa_quadraticTwistOf :
    54 * (E.quadraticTwistOf t n).b₆
      - 3 * (E.quadraticTwistOf t n).b₂ * (E.quadraticTwistOf t n).b₄
      + (E.quadraticTwistOf t n).a₂ * (E.quadraticTwistOf t n).c₄
      = (t ^ 2 - 4 * n) ^ 3 * (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)
        - (t ^ 2 - 4 * n) ^ 2 * n * E.a₁ ^ 2 * E.c₄ := by
  rw [b₆_quadraticTwistOf, b₂_quadraticTwistOf, b₄_quadraticTwistOf, c₄_quadraticTwistOf,
    show (E.quadraticTwistOf t n).a₂ = (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2 from rfl]
  ring

end QuadraticTwistOfRing

variable {K : Type u} [Field K]

section QuadraticTwistOf

variable (E : WeierstrassCurve K)

variable (t n : K)

theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : t ^ 2 - 4 * n ≠ 0) :
    (E.quadraticTwistOf t n).IsElliptic := by
  rw [isElliptic_iff, Δ_quadraticTwistOf]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hD)).mul E.isUnit_Δ

theorem j_quadraticTwistOf [E.IsElliptic] (h : (E.quadraticTwistOf t n).IsElliptic) :
    (E.quadraticTwistOf t n).j = E.j := by
  have hD : t ^ 2 - 4 * n ≠ 0 := fun h0 ↦ (E.quadraticTwistOf t n).isUnit_Δ.ne_zero
    (by rw [Δ_quadraticTwistOf, h0]; ring)
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  simp only [j, Units.val_inv_eq_inv_val, coe_Δ', Δ_quadraticTwistOf, c₄_quadraticTwistOf]
  field_simp


/-- Changing the parameters `(t, n)` — the trace and norm of a generator `θ` of a quadratic
extension — into the trace and norm `(at + 2b, b² + abt + a²n)` of another generator `aθ + b`
changes the quadratic twist by an explicit change of variables over `K`. -/
theorem exists_smul_quadraticTwistOf_eq {a : K} (b : K) (ha : a ≠ 0) :
    ∃ C : VariableChange K, C • E.quadraticTwistOf t n
      = E.quadraticTwistOf (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) := by
  refine ⟨⟨(Units.mk0 a ha)⁻¹, 0, a⁻¹ * b * E.a₁, a⁻¹ * b * (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, Units.val_mk0] <;> field

end QuadraticTwistOf

section QuadraticTwistBy

variable {L : Type*} [Field L] [Algebra K L] (E : WeierstrassCurve K)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by an element `θ` of an extension
`L/K`: the twist `WeierstrassCurve.quadraticTwistOf` by the trace and norm of `θ`. This is "the"
quadratic twist of `E` by the extension `L/K` whenever `L/K` is separable quadratic and `θ`
generates it, i.e. `θ ∉ K`; the choice of generator does not matter, up to isomorphism over `K`
(`exists_smul_quadraticTwistBy_eq`). -/
noncomputable def quadraticTwistBy (θ : L) : WeierstrassCurve K :=
  E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

theorem isElliptic_quadraticTwistBy [E.IsElliptic] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) : (E.quadraticTwistBy θ).IsElliptic :=
  E.isElliptic_quadraticTwistOf _ _ (discrim_ne_zero K L hθ)

/-- The quadratic twist by a generator `θ` of a separable quadratic extension `L/K` depends on
the choice of `θ` only up to isomorphism over `K`: all generators give isomorphic twists. -/
theorem exists_smul_quadraticTwistBy_eq {θ θ' : L} (hθ : θ ∉ Set.range (algebraMap K L))
    (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwistBy θ = E.quadraticTwistBy θ' := by
  obtain ⟨a, b, ha, rfl⟩ := exists_eq_algebraMap_add_algebraMap_mul K L hθ hθ'
  simp only [quadraticTwistBy, trace_algebraMap_add_algebraMap_mul K L a b θ,
    norm_algebraMap_add_algebraMap_mul K L a b θ]
  exact E.exists_smul_quadraticTwistOf_eq _ _ b ha

end QuadraticTwistBy

/-- The quadratic twist of an elliptic curve `E` over `K` by a separable quadratic extension
`L/K`: the twist `WeierstrassCurve.quadraticTwistBy` by an arbitrarily chosen generator
`θ ∈ L ∖ K`. The twist is independent of this choice up to isomorphism over `K`
(`exists_smul_quadraticTwist_eq_quadraticTwistBy`), that is, up to the action of
`WeierstrassCurve.VariableChange K`; see `WeierstrassCurve.quadraticTwistOf` for the explicit
Weierstrass model. (The separability hypothesis is not used to write down the model, but the
twist is only meaningful for separable extensions — see the module docstring.) -/
@[nolint unusedArguments]
noncomputable def quadraticTwist (E : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] : WeierstrassCurve K :=
  E.quadraticTwistBy (exists_notMem_range_algebraMap K L).choose

-- Let `E/K` be an elliptic curve and let `L/K` be a separable quadratic extension.
variable (E : WeierstrassCurve K)
variable (L : Type*) [Field L] [Algebra K L]

section

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

end

section

variable [E.IsElliptic]



end

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- The quadratic twist of `E` by `L/K` is isomorphic over `K` to the twist by any given
generator `θ ∈ L ∖ K`: the arbitrary choice made in its definition is harmless. -/
theorem exists_smul_quadraticTwist_eq_quadraticTwistBy {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwist L = E.quadraticTwistBy θ :=
  E.exists_smul_quadraticTwistBy_eq (exists_notMem_range_algebraMap K L).choose_spec hθ

/-- An explicit `L`-isomorphism `(Eᶿ)ᴸ ≅ Eᴸ` (the change of variables of the module docstring)
which moreover is **anti-equivariant** for the Galois action: its conjugate by the nontrivial
`σ ∈ Gal(L/K)` differs from it by the automorphism `[-1]` of `E`. This nontrivial cocycle is the
origin of the twist being a nontrivial form of `E`. -/
theorem exists_smul_baseChange_and_map_eq {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ∃ C : VariableChange L, C • (E.quadraticTwistBy θ).baseChange L = E.baseChange L ∧
      C.map σ.toAlgHom.toRingHom = (E.baseChange L).negVariableChange * C := by
  have hσθ : σ θ ≠ θ := algEquiv_apply_ne K L hσ hθ
  have hw : σ θ - θ ≠ 0 := sub_ne_zero.mpr hσθ
  have hT : algebraMap K L (Algebra.trace K L θ) = θ + σ θ :=
    algebraMap_trace_eq_add K L hσ θ
  have hN : algebraMap K L (Algebra.norm K θ) = θ * σ θ :=
    algebraMap_norm_eq_mul K L hσ θ
  have hσσ : σ (σ θ) = θ := by
    rw [← AlgEquiv.mul_apply, algEquiv_mul_self K L hσ,
      AlgEquiv.one_apply]
  have hap : ⇑σ.toAlgHom.toRingHom = ⇑σ := rfl
  refine ⟨⟨Units.mk0 (σ θ - θ) hw, 0, -(θ * algebraMap K L E.a₁),
    -((σ θ - θ) ^ 2 * θ * algebraMap K L E.a₃)⟩, ?_, ?_⟩
  · rw [variableChange_def]
    ext <;>
      simp only [quadraticTwistBy, quadraticTwistOf, baseChange, map_a₁, map_a₂, map_a₃,
        map_a₄, map_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, map_sub, map_mul,
        map_pow, map_ofNat, hT, hN] <;>
      field
  · ext <;>
      simp only [VariableChange.map, VariableChange.mul_def, negVariableChange, Units.coe_map,
        Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, hap, MonoidHom.coe_coe,
        map_neg, map_mul, map_pow, map_sub, map_zero, map_a₁, map_a₃, baseChange,
        σ.commutes, hσσ] <;>
      ring




/-- A choice of change of variables over `L` carrying `E` to its quadratic twist `Eᴸ`. Using the
explicit isomorphism of `exists_smul_baseChange_and_map_eq` (rather than an arbitrary one) ensures
its Galois cocycle is exactly `[-1]` (`quadraticTwistVarChange_map`), unconditionally in `j`. -/
noncomputable def quadraticTwistVarChange : VariableChange L :=
  (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose⁻¹

lemma quadraticTwistVarChange_smul :
    (E.quadraticTwistVarChange L) • E.baseChange L = (E.quadraticTwist L).baseChange L := by
  unfold quadraticTwistVarChange
  rw [inv_smul_eq_iff]
  exact (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose_spec.1.symm

/-- **The defining cocycle of the quadratic twist.** The nontrivial `σ ∈ Gal(L/K)` conjugates the
change of variables `quadraticTwistVarChange` (carrying `E` to `Eᴸ`) by the automorphism `[-1]` of
`E`. This is the datum expressing that `Eᴸ` is the descent of `E` along the twisted Galois action
`σ ↦ (-1) ∘ σ`, and it holds for every `j`. -/
lemma quadraticTwistVarChange_map {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistVarChange L).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L) * (E.baseChange L).negVariableChange := by
  set σ₀ := (exists_algEquiv_ne_one K L).choose
  have hσ₀ : σ₀ ≠ 1 := (exists_algEquiv_ne_one K L).choose_spec
  obtain rfl : σ = σ₀ := (algEquiv_eq_one_or_eq K L hσ₀ σ).resolve_left hσ
  have hcoc := (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose_spec.2
  have hinv : ∀ C : VariableChange L,
      C⁻¹.map σ₀.toAlgHom.toRingHom = (C.map σ₀.toAlgHom.toRingHom)⁻¹ :=
    fun C ↦ map_inv (VariableChange.mapHom _) C
  unfold quadraticTwistVarChange
  rw [hinv, hcoc, mul_inv_rev, (E.baseChange L).negVariableChange_inv]

section

variable [E.IsElliptic]

/-- The quadratic twist of an elliptic curve is an elliptic curve: the twisted model has
discriminant `D⁶·Δ(E)`, and `D ≠ 0` by separability
(`Algebra.IsQuadraticExtension.discrim_ne_zero`). -/
instance : (E.quadraticTwist L).IsElliptic :=
  E.isElliptic_quadraticTwistBy (exists_notMem_range_algebraMap K L).choose_spec

/-- Twisting does not change the `j`-invariant, since the curves become isomorphic over `L`. -/
theorem j_quadraticTwist : (E.quadraticTwist L).j = E.j :=
  E.j_quadraticTwistOf _ _ (E.isElliptic_quadraticTwistOf _ _
    (discrim_ne_zero K L (exists_notMem_range_algebraMap K L).choose_spec))



end

/-! ### The isomorphism on points and its Galois anti-equivariance -/

section PointEquiv

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

lemma quadraticTwistVarChange_smul_baseChange :
    (E.quadraticTwistVarChange L).baseChange M • E.baseChange M
      = (E.quadraticTwist L).baseChange M := by
  have h := map_variableChange (C := E.quadraticTwistVarChange L) (W := E.baseChange L)
    (φ := algebraMap L M)
  rw [quadraticTwistVarChange_smul, baseChange_map_algebraMap, baseChange_map_algebraMap] at h
  exact h

/-- The `M`-level form of the twist's defining cocycle: any `σ ∈ Aut(M/K)` not fixing `L`
pointwise (i.e. with `χ(σ) = -1`) conjugates the base change to `M` of `quadraticTwistVarChange`
by the automorphism `[-1]` of `E`. This is the base change of `quadraticTwistVarChange_map`. -/
lemma quadraticTwistVarChange_baseChange_map {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    ((E.quadraticTwistVarChange L).baseChange M).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L).baseChange M * (E.baseChange M).negVariableChange := by
  obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
  have hres : σ.restrictNormal L = σ₀ :=
    (algEquiv_eq_one_or_eq K L hσ₀ _).resolve_left
      (fun h ↦ hσ ((forall_apply_algebraMap_iff_restrictNormal_eq_one K L M σ).mpr h))
  have hcomp : σ.toAlgHom.toRingHom.comp (algebraMap L M)
      = (algebraMap L M).comp σ₀.toAlgHom.toRingHom := by
    ext l
    have h := (AlgEquiv.restrictNormal_commutes σ L l).symm
    rw [hres] at h
    simpa using h
  have e1 : ((E.quadraticTwistVarChange L).baseChange M).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L).map (σ.toAlgHom.toRingHom.comp (algebraMap L M)) :=
    (E.quadraticTwistVarChange L).map_map (algebraMap L M) σ.toAlgHom.toRingHom
  have e2 : ((E.quadraticTwistVarChange L) * (E.baseChange L).negVariableChange).map
        (algebraMap L M)
      = (E.quadraticTwistVarChange L).baseChange M
        * (E.baseChange L).negVariableChange.map (algebraMap L M) :=
    map_mul (VariableChange.mapHom (algebraMap L M)) _ _
  rw [e1, hcomp, ← VariableChange.map_map, E.quadraticTwistVarChange_map L hσ₀, e2,
    negVariableChange_map, baseChange_map_algebraMap]

-- `DecidableEq` is needed for the group structure on points.
variable [E.IsElliptic] [DecidableEq M]

/-- The isomorphism `Eᴸ(M) ≅ E(M)` on `M`-points, for any field `M` in a tower `K ⊆ L ⊆ M`:
the base change to `M` of a choice of isomorphism between `Eᴸ` and `E` over `L`. It is natural
in `M` (`quadraticTwistPointEquiv_map`) and transforms the Galois action into the Galois action
twisted by the quadratic character of `L/K` (`quadraticTwistPointEquiv_galois`).

Like the twist itself, this isomorphism is well defined only up to composition with an
`L`-automorphism of `E` — generically, up to sign — and this definition makes an arbitrary but
single choice, consistent across all `M`. -/
noncomputable def quadraticTwistPointEquiv :
    ((E.quadraticTwist L)⁄M).Point ≃+ (E⁄M).Point :=
  have : (E.baseChange M).IsElliptic := inferInstanceAs (E.map (algebraMap K M)).IsElliptic
  (Affine.Point.equivOfEq (E.quadraticTwistVarChange_smul_baseChange L M).symm).trans
    (Affine.Point.equivVariableChange (E.baseChange M) ((E.quadraticTwistVarChange L).baseChange M))

/-- Naturality of `quadraticTwistPointEquiv` in `M`: the isomorphisms on `M`-points over varying
`M ⊇ L` are all induced by a single isomorphism of curves over `L`, so they commute with the
maps on points induced by any `L`-algebra homomorphism. -/
theorem quadraticTwistPointEquiv_map {N : Type*} [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N] [DecidableEq N] (f : M →ₐ[L] N)
    (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L N (Affine.Point.map f P) =
      Affine.Point.map f (E.quadraticTwistPointEquiv L M P) := by
  -- The base-changed change of variables over `N` is the image under `f` of that over `M`.
  have hu : (((E.quadraticTwistVarChange L).baseChange N).u : N)
      = f (((E.quadraticTwistVarChange L).baseChange M).u : M) := by
    simp only [VariableChange.baseChange, VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact (f.commutes _).symm
  have hr : ((E.quadraticTwistVarChange L).baseChange N).r
      = f ((E.quadraticTwistVarChange L).baseChange M).r := (f.commutes _).symm
  have hs : ((E.quadraticTwistVarChange L).baseChange N).s
      = f ((E.quadraticTwistVarChange L).baseChange M).s := (f.commutes _).symm
  have ht : ((E.quadraticTwistVarChange L).baseChange N).t
      = f ((E.quadraticTwistVarChange L).baseChange M).t := (f.commutes _).symm
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some]
    refine Affine.Point.some_eq_some (E.baseChange N) ?_ ?_
    · simp only [map_add, map_mul, map_pow, hu, hr]
    · simp only [map_add, map_mul, map_pow, hu, hs, ht]

/-- The **anti-equivariance** underlying `quadraticTwistPointEquiv_galois`: if `σ ∈ Aut(M/K)` does
not fix `L` pointwise (`χ(σ) = -1`), then transporting its action through `Eᴸ(M) ≅ E(M)` gives
minus its action. This is the point-level shadow of `quadraticTwistVarChange_baseChange_map`. -/
theorem quadraticTwistPointEquiv_map_of_not_fixed {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x)
    (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  have hM := E.quadraticTwistVarChange_baseChange_map L M hσ
  have hu : σ.toAlgHom (((E.quadraticTwistVarChange L).baseChange M).u : M)
      = -(((E.quadraticTwistVarChange L).baseChange M).u : M) := by
    simpa [VariableChange.mul_def, negVariableChange]
      using congrArg (fun C ↦ (VariableChange.u C : M)) hM
  have hr : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).r
      = ((E.quadraticTwistVarChange L).baseChange M).r := by
    simpa [VariableChange.mul_def, negVariableChange] using congrArg VariableChange.r hM
  have hs : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).s
      = -((E.quadraticTwistVarChange L).baseChange M).s - (E.baseChange M).a₁ := by
    simpa [VariableChange.mul_def, negVariableChange, sub_eq_add_neg]
      using congrArg VariableChange.s hM
  have ht : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).t
      = -((E.quadraticTwistVarChange L).baseChange M).t
        - ((E.quadraticTwistVarChange L).baseChange M).r * (E.baseChange M).a₁
        - (E.baseChange M).a₃ := by
    simpa [VariableChange.mul_def, negVariableChange, sub_eq_add_neg, mul_neg_one,
      (by ring : ((-1 : M)) ^ 3 = -1)] using congrArg VariableChange.t hM
  rcases P with _ | ⟨x, y, hns⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some, Affine.Point.neg_some]
    refine Affine.Point.some_eq_some (E.baseChange M) ?_ ?_
    · simp only [map_add, map_mul, map_pow, hu, hr]
      ring
    · simp only [Affine.negY, map_add, map_mul, map_pow, hu, hr, hs, ht]
      ring

/-- **Twisting the Galois action.** The Galois action on the points of the quadratic twist is
the Galois action on the points of `E`, twisted by the quadratic character of `L/K`: for
`σ ∈ Aut(M/K)`, transporting the action of `σ` on `Eᴸ(M)` through `Eᴸ(M) ≅ E(M)` gives `χ(σ)`
times the action of `σ` on `E(M)`.

Taking `M` to be a separable closure of `K`, this says that the Galois representations attached
to `Eᴸ` (e.g. on torsion points) are those attached to `E`, twisted by `χ`. Taking `M = L` and
`σ ≠ 1` recovers the classical anti-equivariance of the isomorphism `φ : Eᴸ ≅ E` over `L`
(see `quadraticTwistPointEquiv_conj`). Note the statement is unchanged under replacing `φ` by
`-φ`, so it does not depend on the sign choice hidden in `quadraticTwistPointEquiv`. Note also
that for `σ` fixing `L` pointwise (i.e. `σ ∈ Aut(M/L)`, `χ(σ) = 1`) it is a special case of
naturality, via the `L`-algebra map underlying `σ`. -/
theorem quadraticTwistPointEquiv_galois (σ : M ≃ₐ[K] M) (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P) =
      (quadraticCharacter K L M σ : ℤ) •
        Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  by_cases hσ : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x
  · -- `σ` fixes `L` pointwise (`χ(σ) = 1`): this is naturality for the `L`-algebra map behind `σ`.
    rw [(quadraticCharacter_eq_one_iff K L M σ).mpr hσ, Units.val_one, one_zsmul]
    exact E.quadraticTwistPointEquiv_map L M ({ σ.toAlgHom with commutes' := hσ } : M →ₐ[L] M) P
  · -- `σ` moves `L` (`χ(σ) = -1`): anti-equivariance.
    have hχ : quadraticCharacter K L M σ = -1 :=
      (Int.units_eq_one_or _).resolve_left
        fun h ↦ hσ ((quadraticCharacter_eq_one_iff K L M σ).mp h)
    rw [hχ, Units.val_neg, Units.val_one, neg_one_zsmul]
    exact E.quadraticTwistPointEquiv_map_of_not_fixed L M hσ P



end PointEquiv

end WeierstrassCurve

end
