/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Velu
-- The two geometric inputs (`nsmul_surjective`, `finite_nsmulKer`) are PROVEN
-- from the division-polynomial development. `PhiPsiCoprime` and
-- `DivisionPolynomial.Degree` are imported PUBLICLY rather than relied on
-- transitively: `TorsionCard.lean` imports both privately, so their lemmas
-- would be unavailable here even in proof bodies.
public import Fermat.FLT.EllipticCurve.TorsionCard
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

/-!
# Isogenies of elliptic curves as morphisms

This file supplies the vocabulary that the `X_0(N)` descent leaves in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` need and that neither mathlib (at this
pin) nor `~/cs/FLT` provides in any form: **an isogeny as a morphism**, with a
`degree`, a `dual`, a `comp`osition, and an endomorphism **ring**.

## Why a bare group homomorphism is not enough

Everything the development had until now — `exists_quotient_isogeny`,
`exists_velu_quotient_isogeny` — produces only an *additive, Galois-equivariant
map on `ℚ̄`-points*. That is provably too weak to state the conditions the
descent needs, and the failure is not a matter of difficulty: the statement one
would write is **empty**.

The concrete instance, which is the reason this file exists. The Atkin–Lehner
condition at level `125` is `ψ² = [−125]` with `ker ψ` cyclic of order `125`.
Written for an arbitrary additive endomorphism of the point group it says nothing
whatever: as an abstract group `E(ℚ̄)` has torsion `(ℚ/ℤ)²`, whose endomorphism
ring is `M₂(Ẑ)`, and the matrix

  `[[0, −125], [1, 0]]`

squares to `−125` and has cyclic kernel of order `125` **on every elliptic curve
over every field**. So the "condition" would be satisfied by all curves and would
carry none of the arithmetic it was supposed to.

What defeats that junk witness — and the whole class it belongs to — is
`IsRationalMap` below: the requirement that the map be given by *rational
functions in the coordinates*. An abstract endomorphism of `(ℚ/ℤ)²` admits no
such description, so it is not an element of `endSubring`, and `ψ * ψ = -125` in
`End W` is a genuine assertion of complex multiplication.

## Design, and why it is this one

The base is a field `F` (in the application, `AlgebraicClosure ℚ`). Two choices
are load-bearing:

* **The rational-function certificate is a `Prop`, not data.** `IsIsogeny φ` is a
  predicate on `φ : W.Point →+ W'.Point`, so `Isogeny W W'` is a *subtype* and two
  isogenies are equal exactly when their point maps are. Had the polynomials been
  fields of a structure, one map with two presentations would give two distinct
  terms and the ring axioms on `End` would fail.

* **`degree` is the cardinality of the kernel.** In characteristic zero every
  isogeny is separable, so this agrees with the classical degree, and — unlike a
  degree read off the presenting polynomials — it is manifestly a function of the
  point map alone, so it needs no well-definedness lemma. The pay-off is large:
  multiplicativity of the degree, the construction of the dual and
  `ψ̂ ∘ ψ = [deg ψ]` all become pure group theory over the two geometric inputs
  `nsmul_surjective` and `finite_nsmulKer`. **This file is therefore correct only
  in characteristic zero**, which is where all its consumers live.

## Main definitions

* `WeierstrassCurve.IsRationalMap` — the algebraicity certificate.
* `WeierstrassCurve.IsIsogeny` — rational, plus surjective with finite kernel
  away from the zero map.
* `WeierstrassCurve.Isogeny` — the subtype; `WeierstrassCurve.Isogeny.degree`.
* `WeierstrassCurve.endSubring` — `End W` as a `Subring (AddMonoid.End W.Point)`,
  hence a `Ring`, in which `(n : End W)` **is** multiplication by `n` (`rfl`, see
  `End.intCast_apply`).
* `WeierstrassCurve.Isogeny.dualHom` / `dual` — the dual isogeny, with
  `Isogeny.dualHom_comp` giving `ψ̂ ∘ ψ = [deg ψ]`.

## Open leaves left by this file

`IsRationalMap.comp`, `IsRationalMap.add`, `IsIsogeny.add`,
`Isogeny.isRationalMap_dualHom`.

`IsRationalMap.neg` was on this list and is now PROVEN. So, as of 2026-07-26,
are all three of `nsmul_surjective`, `finite_nsmulKer` and `Isogeny.degree_comp`
— see the two sections below.

## Correction to the characteristic caveat above

The design note says this file is "correct only in characteristic zero". That
remains true of the *interpretation* of `degree` as the classical degree (which
needs separability), but it is **not** a restriction on the two geometric
inputs: both are proven below over an arbitrary algebraically closed field, in
every characteristic, with no hypothesis beyond `n ≠ 0`. The project's
`TorsionCard.smul_surjective` needs `(n : k) ≠ 0` only because it works over a
*separably* closed field, where the root is produced by
`exists_root_of_derivative_ne_zero` and the derivative of
`Φₙ − ξ·ΨSqₙ` genuinely vanishes when `char k ∣ n`. Over an algebraically closed
field no separability is needed: the polynomial is monic of degree `n²` (its
`n²`-coefficient is `1`, `WeierstrassCurve.coeff_Φ`, while `ΨSqₙ` has degree at
most `n² − 1`), so it has a root outright, and the `y`-fibre quadratic likewise.
-/


@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W W' W'' : Affine F}

/-! ### The algebraicity certificate -/

/-- `IsRationalMap φ` says that the map `φ` on points is computed, away from its
kernel, by **rational functions in the coordinates**: there are polynomials
`A, B, C, D, E` over the base field with

  `x(φ P) = A(x P) / B(x P)`,  `y(φ P) = (C(x P) · y P + D(x P)) / E(x P)`,

written multiplicatively so that no division is needed. This is the normal form
of a morphism of Weierstrass curves in characteristic zero.

This predicate is the entire faithfulness content of `IsIsogeny`. Without it,
`End W` would be the endomorphism ring of an abstract abelian group — see the
`M₂(Ẑ)` discussion in the module docstring — and every condition stated in it
would be vacuous. -/
def IsRationalMap (φ : W.Point →+ W'.Point) : Prop :=
  ∃ A B C D E : F[X], B ≠ 0 ∧ E ≠ 0 ∧
    ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) ∧
      veluPointY (φ P) * E.eval (veluPointX P)
        = C.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)

/-- The zero map is rational: its defining condition is vacuous. -/
theorem IsRationalMap.zero : IsRationalMap (0 : W.Point →+ W'.Point) :=
  ⟨0, 1, 0, 0, 1, one_ne_zero, one_ne_zero, fun P hP =>
    absurd (AddMonoidHom.zero_apply P) hP⟩

/-- The identity is rational, with `A = X`, `B = C = E = 1`, `D = 0`. -/
theorem IsRationalMap.id : IsRationalMap (AddMonoidHom.id W.Point) := by
  refine ⟨X, 1, 1, 0, 1, one_ne_zero, one_ne_zero, fun P _ => ?_⟩
  simp

/-- A negated rational map is rational.

`x(-Q) = x(Q)`, so `A, B` are unchanged; `y(-Q) = negY (x Q) (y Q)
= -y(Q) - a₁ x(Q) - a₃`, so substituting `x(φ P) = A/B` and clearing the extra
denominator gives the `y`-witness
`(C', D', E') = (-C·B, -D·B - a₁·A·E - a₃·B·E, E·B)`. -/
theorem IsRationalMap.neg {φ : W.Point →+ W'.Point} (h : IsRationalMap φ) :
    IsRationalMap (-φ) := by
  obtain ⟨A, B, C, D, E, hB, hE, hcert⟩ := h
  refine ⟨A, B, -(C * B),
    -(D * B) - Polynomial.C W'.a₁ * A * E - Polynomial.C W'.a₃ * B * E, E * B,
    hB, mul_ne_zero hE hB, fun P hP => ?_⟩
  have hφP : φ P ≠ 0 := fun hc => hP (by show -(φ P) = 0; rw [hc, neg_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  have hnegapp : (-φ) P = -(φ P) := rfl
  refine ⟨?_, ?_⟩
  · rw [hnegapp, velu_pointX_neg]
    exact hx
  · rw [hnegapp, velu_pointY_neg _ hφP]
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
      Polynomial.eval_C]
    linear_combination (-(B.eval (veluPointX P))) * hy
      - (W'.a₁ * E.eval (veluPointX P)) * hx

/-- **LEAF.** The composite of two rational maps is rational.

Elementary but not free: one substitutes `A/B` into `A'/B'` and clears
denominators, i.e. homogenises `A'` and `B'` to degree `max (deg A') (deg B')`
against the pair `(A, B)`, and likewise for the `y`-component. -/
theorem IsRationalMap.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (ψ.comp φ) :=
  sorry

/-- **LEAF.** The pointwise sum of two rational maps is rational.

This is the affine addition formula on `W'` applied to the two images: `x` and
`y` of `φ P + ψ P` are rational in `x(φ P), y(φ P), x(ψ P), y(ψ P)`, each of
which is rational in `x P, y P`, and `y P` occurs to degree at most one after
reduction by the Weierstrass equation. The case analysis is over the three
branches of the group law. -/
theorem IsRationalMap.add {φ ψ : W.Point →+ W'.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (φ + ψ) :=
  sorry

/-! ### Isogenies -/

/-- An **isogeny** `W → W'`: a homomorphism of point groups given by rational
functions in the coordinates which, unless it is the zero map, is surjective with
finite kernel.

The zero map is admitted, with degree `0`, so that `End W` is a ring.

`surjective` and `finite_ker` are *fields* rather than consequences on purpose.
Both are genuinely geometric — surjectivity of a non-constant morphism of curves
is properness, and it is false for a general group homomorphism with divisible
image — so a construction that produces an isogeny must discharge them, and the
cost is paid where the geometry is rather than silently. -/
structure IsIsogeny (φ : W.Point →+ W'.Point) : Prop where
  /-- The map is given by rational functions in the coordinates. -/
  isRationalMap : IsRationalMap φ
  /-- A nonzero isogeny is surjective on points. -/
  surjective : φ ≠ 0 → Function.Surjective φ
  /-- A nonzero isogeny has finite kernel. -/
  finite_ker : φ ≠ 0 → (AddMonoidHom.ker φ : Set W.Point).Finite

theorem IsIsogeny.zero : IsIsogeny (0 : W.Point →+ W'.Point) where
  isRationalMap := IsRationalMap.zero
  surjective h := absurd rfl h
  finite_ker h := absurd rfl h

theorem IsIsogeny.id : IsIsogeny (AddMonoidHom.id W.Point) where
  isRationalMap := IsRationalMap.id
  surjective _ := Function.surjective_id
  finite_ker _ := by
    have h : (AddMonoidHom.ker (AddMonoidHom.id W.Point) : Set W.Point) = {0} := by
      ext P; simp
    rw [h]; exact Set.finite_singleton _

theorem IsIsogeny.neg {φ : W.Point →+ W'.Point} (h : IsIsogeny φ) : IsIsogeny (-φ) where
  isRationalMap := h.isRationalMap.neg
  surjective hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    intro Q
    obtain ⟨P, hP⟩ := h.surjective hφ (-Q)
    exact ⟨P, by simp [hP]⟩
  finite_ker hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    have hker : (AddMonoidHom.ker (-φ) : Set W.Point) = (AddMonoidHom.ker φ : Set W.Point) := by
      ext P; simp [AddMonoidHom.mem_ker]
    rw [hker]; exact h.finite_ker hφ

/-- **LEAF.** The pointwise sum of two isogenies is an isogeny.

The rational half is `IsRationalMap.add`; the remaining two fields are the
geometric content — a nonzero sum of isogenies is again surjective with finite
kernel, which is not formal, and is exactly the statement that `Hom(W, W')` is a
group under addition in the category of curves. -/
theorem IsIsogeny.add {φ ψ : W.Point →+ W'.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ) :=
  sorry

/-- The composite of two isogenies is an isogeny. -/
theorem IsIsogeny.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (ψ.comp φ) where
  isRationalMap := hφ.isRationalMap.comp hψ.isRationalMap
  surjective hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    exact (hψ.surjective hψ0).comp (hφ.surjective hφ0)
  finite_ker hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    -- `ker (ψ ∘ φ)` is contained in the union, over the finite set `ker ψ`, of the
    -- fibres of `φ`; each nonempty fibre of `φ` is a coset of the finite `ker φ`.
    have hfib : ∀ Q : W'.Point, {P : W.Point | φ P = Q}.Finite := by
      intro Q
      by_cases hQ : ∃ P₀ : W.Point, φ P₀ = Q
      · obtain ⟨P₀, hP₀⟩ := hQ
        have hcoset : {P : W.Point | φ P = Q}
            = (fun k : W.Point => P₀ + k) '' (AddMonoidHom.ker φ : Set W.Point) := by
          ext P
          simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, AddMonoidHom.mem_ker]
          constructor
          · intro hp
            exact ⟨P - P₀, by rw [map_sub, hp, hP₀, sub_self], by abel⟩
          · rintro ⟨k, hk, rfl⟩
            rw [map_add, hk, add_zero, hP₀]
        rw [hcoset]
        exact Set.Finite.image _ (hφ.finite_ker hφ0)
      · simp only [not_exists] at hQ
        have hempty : {P : W.Point | φ P = Q} = ∅ := by
          ext P; simpa using hQ P
        rw [hempty]; exact Set.finite_empty
    have hsub : (AddMonoidHom.ker (ψ.comp φ) : Set W.Point) ⊆
        ⋃ Q ∈ (AddMonoidHom.ker ψ : Set W'.Point), {P : W.Point | φ P = Q} := by
      intro P hP
      have hQ : φ P ∈ (AddMonoidHom.ker ψ : Set W'.Point) := by
        have := (AddMonoidHom.mem_ker (f := ψ.comp φ)).1 hP
        simpa [SetLike.mem_coe, AddMonoidHom.mem_ker] using this
      exact Set.mem_biUnion hQ rfl
    exact Set.Finite.subset
      (Set.Finite.biUnion (hψ.finite_ker hψ0) (fun Q _ => hfib Q)) hsub

/-- Multiplication by `n` on the points of `W`, as a homomorphism. This is the
`[n]` that appears in `ψ̂ ∘ ψ = [deg ψ]`; it agrees with the image of `n` in
`End W` (`End.natCast_apply`). -/
def mulByHom (W : Affine F) (n : ℕ) : W.Point →+ W.Point :=
  AddMonoidHom.mk' (fun P => n • P) (fun a b => by simp [smul_add])

@[simp] theorem mulByHom_apply (n : ℕ) (P : W.Point) : mulByHom W n P = n • P := rfl

/-- The type of isogenies `W → W'`.

A one-field-plus-proof structure, so that two isogenies are equal precisely when
their maps on points are — which is what makes `End W` a ring. -/
structure Isogeny (W W' : Affine F) where
  /-- The underlying homomorphism of point groups. -/
  toHom : W.Point →+ W'.Point
  /-- The proof that it is an isogeny. -/
  isIsogeny : IsIsogeny toHom

namespace Isogeny

instance : CoeFun (Isogeny W W') (fun _ => W.Point → W'.Point) := ⟨fun φ => φ.toHom⟩

@[ext] theorem ext {φ ψ : Isogeny W W'} (h : ∀ P, φ.toHom P = ψ.toHom P) : φ = ψ := by
  cases φ; cases ψ; simp only [Isogeny.mk.injEq]; exact AddMonoidHom.ext h

/-- The zero isogeny. -/
def zero : Isogeny W W' := ⟨0, IsIsogeny.zero⟩

/-- The identity isogeny. -/
def id (W : Affine F) : Isogeny W W := ⟨AddMonoidHom.id W.Point, IsIsogeny.id⟩

/-- Composition of isogenies. -/
def comp (ψ : Isogeny W' W'') (φ : Isogeny W W') : Isogeny W W'' :=
  ⟨ψ.toHom.comp φ.toHom, IsIsogeny.comp φ.isIsogeny ψ.isIsogeny⟩

@[simp] theorem comp_toHom (ψ : Isogeny W' W'') (φ : Isogeny W W') :
    (ψ.comp φ).toHom = ψ.toHom.comp φ.toHom := rfl

@[simp] theorem comp_apply (ψ : Isogeny W' W'') (φ : Isogeny W W') (P : W.Point) :
    (ψ.comp φ).toHom P = ψ.toHom (φ.toHom P) := rfl

section Degree

open scoped Classical

/-- The **degree** of an isogeny: the cardinality of its kernel, and `0` for the
zero map.

In characteristic zero every isogeny is separable, so this is the classical
degree; see the module docstring for why it is defined this way rather than read
off the presenting polynomials. -/
noncomputable def degree (φ : Isogeny W W') : ℕ :=
  if φ.toHom = 0 then 0 else Nat.card (AddMonoidHom.ker φ.toHom)

theorem degree_of_ne_zero {φ : Isogeny W W'} (h : φ.toHom ≠ 0) :
    φ.degree = Nat.card (AddMonoidHom.ker φ.toHom) := by
  rw [degree, if_neg h]

theorem degree_of_eq_zero {φ : Isogeny W W'} (h : φ.toHom = 0) : φ.degree = 0 := by
  rw [degree, if_pos h]

end Degree

@[simp] theorem degree_zero : (zero : Isogeny W W').degree = 0 := degree_of_eq_zero rfl

/-- An isogeny has degree `0` exactly when it is the zero map. -/
theorem degree_eq_zero_iff (φ : Isogeny W W') : φ.degree = 0 ↔ φ.toHom = 0 := by
  refine ⟨fun h => by_contra fun hne => ?_, degree_of_eq_zero⟩
  rw [degree_of_ne_zero hne] at h
  haveI : Finite (AddMonoidHom.ker φ.toHom) :=
    Set.Finite.to_subtype (φ.isIsogeny.finite_ker hne)
  haveI : Nonempty (AddMonoidHom.ker φ.toHom) := ⟨0⟩
  exact absurd h Nat.card_pos.ne'

theorem degree_pos {φ : Isogeny W W'} (h : φ.toHom ≠ 0) : 0 < φ.degree :=
  Nat.pos_of_ne_zero fun hc => h ((degree_eq_zero_iff φ).1 hc)

/-- The identity has degree `1`.

The hypothesis is not removable: if `W` had only the point at infinity then the
identity *would be* the zero map, of degree `0`. Over an algebraically closed
field it is of course always satisfied. -/
theorem degree_id (h : ∃ P : W.Point, P ≠ 0) : (Isogeny.id W).degree = 1 := by
  obtain ⟨P, hP⟩ := h
  have hne : (Isogeny.id W).toHom ≠ 0 := by
    intro hc
    have hPc := congrArg (fun f : W.Point →+ W.Point => f P) hc
    simp only [Isogeny.id, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at hPc
    exact hP hPc
  rw [degree_of_ne_zero hne]
  have hker : AddMonoidHom.ker (Isogeny.id W).toHom = ⊥ := by
    ext Q; simp [Isogeny.id]
  rw [hker]
  simp

/-- Every element of the kernel of an isogeny is killed by its degree. Lagrange's
theorem in the kernel; it is what lets `[deg φ]` factor through `φ` in the
construction of the dual. -/
theorem degree_nsmul_eq_zero {φ : Isogeny W W'} {k : W.Point}
    (hk : k ∈ AddMonoidHom.ker φ.toHom) (h0 : φ.toHom ≠ 0) : φ.degree • k = 0 := by
  have h : Nat.card (AddMonoidHom.ker φ.toHom) • (⟨k, hk⟩ : AddMonoidHom.ker φ.toHom) = 0 :=
    card_nsmul_eq_zero'
  rw [degree_of_ne_zero h0]
  simpa using congrArg (Subtype.val) h

end Isogeny

/-! ### The endomorphism ring -/

/-- The endomorphisms of `W` that are isogenies form a subring of the endomorphism
ring of the abstract point group.

The `Ring` structure is inherited, and it is the *right* one: multiplication is
composition and, crucially, `((n : ℤ) : End W)` is multiplication by `n` on points
**definitionally** (`End.intCast_apply` below is `rfl`). So `ψ * ψ = -125` in
`End W` says exactly `ψ (ψ P) = -125 • P` for all `P`, with `ψ` an honest
morphism. -/
def endSubring (W : Affine F) : Subring (AddMonoid.End W.Point) where
  carrier := {f | IsIsogeny (f : W.Point →+ W.Point)}
  zero_mem' := IsIsogeny.zero
  one_mem' := IsIsogeny.id
  add_mem' hf hg := IsIsogeny.add hf hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := IsIsogeny.comp hg hf

/-- `End W`, the endomorphism ring of `W`. -/
abbrev End (W : Affine F) : Type _ := ↥(endSubring W)

/-- **The soundness lemma of this file.** In `End W` the integer `n` acts as
multiplication by `n` on points — definitionally. Together with `IsRationalMap`
inside `IsIsogeny`, this is what makes `ψ * ψ = (-125 : End W)` a statement about
complex multiplication rather than about `M₂(Ẑ)`. -/
@[simp] theorem End.intCast_apply (n : ℤ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.natCast_apply (n : ℕ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.mul_apply (f g : End W) (P : W.Point) :
    ((f * g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) ((g : AddMonoid.End W.Point) P) := rfl

/-- **The consumer-facing form of the Atkin–Lehner condition.** `ψ * ψ = (n : End W)`
in the endomorphism ring says exactly that `ψ` applied twice is multiplication by
`n` on points.

This is the lemma the `X_0(N)` descent leaves use: `ψ * ψ = (-125 : End W)` unfolds
to `ψ (ψ P) = -125 • P` for every `P`, with `ψ` carrying its `IsIsogeny` witness —
so the condition is about an actual morphism, not about `M₂(Ẑ)`. -/
theorem End.sq_eq_intCast_iff (ψ : End W) (n : ℤ) :
    ψ * ψ = (n : End W) ↔ ∀ P : W.Point,
      (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) = n • P := by
  constructor
  · intro h P
    have hc := congrArg (fun f : End W => (f : AddMonoid.End W.Point) P) h
    simpa using hc
  · intro h
    refine Subtype.ext (AddMonoidHom.ext fun P => ?_)
    exact h P

/-- Every element of `End W` is an isogeny, so the endomorphism ring maps into the
type of isogenies. -/
def End.toIsogeny (f : End W) : Isogeny W W := ⟨(f : AddMonoid.End W.Point), f.2⟩

@[simp] theorem End.toIsogeny_toHom (f : End W) :
    (End.toIsogeny f).toHom = (f : AddMonoid.End W.Point) := rfl

/-! ### The two geometric inputs -/

/-! Both inputs are PROVEN (2026-07-26) from the division-polynomial development
in `TorsionCard.lean` / `PhiPsiCoprime.lean`, over an arbitrary algebraically
closed field and in every characteristic.

Note on the `(V⁄F)` spelling below. `TorsionCard.lean` states everything for the
base-changed curve `(E⁄k)`, and `(V⁄F) = V` holds by `rfl` — but the two are not
*syntactically* equal, so `rw` cannot cross between them. The helpers are
therefore written uniformly in the `(V⁄F)` form, matching `TorsionCard`, and the
one crossing into the `W.Point` form the rest of this file uses is made by
`exact` (which goes through `whnf`) in the two leaves themselves. -/

omit [DecidableEq F] in
/-- `ΨSqₙ ≠ 0` in ANY characteristic, needing only `n ≠ 0`.

The leading-coefficient route fails at `n = p` in characteristic `p`, where
`coeff_ΨSq n = n²` vanishes. Instead: `IsCoprime a 0` forces `a` to be a unit,
while `Φₙ` has degree `n² > 0`. (This is `TorsionCharP.ΨSq_ne_zero`, inlined
here so that this file's import cone need not grow by the whole
`TorsionCharP`/`WronskianInduction` subtree.) -/
theorem ΨSq_ne_zero' (V : Affine F) [V.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    V.ΨSq n ≠ 0 := by
  intro h0
  have hcop : IsCoprime (V.Φ n) (V.ΨSq n) :=
    WeierstrassCurve.isCoprime_Φ_ΨSq V hn V.isUnit_Δ
  rw [h0] at hcop
  have hdeg0 : (V.Φ n).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp hcop)
  rw [WeierstrassCurve.natDegree_Φ V n] at hdeg0
  exact hn (Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hdeg0))

omit [DecidableEq F] in
/-- **The fibre node over an algebraically closed field.** Given any `ξ`, there
is a curve point `(x₀, y₀)` with `Φₙ(x₀) = ξ · ΨSqₙ(x₀)`.

This is `TorsionCard.exists_point_x_smul` with its `(n : F) ≠ 0` hypothesis
REMOVED, which is exactly what algebraic (rather than separable) closure buys.
That hypothesis is used there only to show the derivative of `Φₙ − C ξ · ΨSqₙ`
is nonzero, so that a root exists over a separably closed field. Here the
polynomial is monic of degree `n² ≥ 1` — its `n²`-coefficient is `1` by
`coeff_Φ`, and `ΨSqₙ` cannot contribute there since its degree is at most
`n² − 1` — so `IsAlgClosed.exists_root` applies directly. The `y`-coordinate is
then a root of the degree-`2` fibre quadratic, again with no separability. -/
theorem exists_point_x_smul_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) (ξ : F) :
    ∃ (x₀ y₀ : F) (_ : (V⁄F).toAffine.Nonsingular x₀ y₀),
      ((V⁄F).Φ n).eval x₀ = ξ * ((V⁄F).ΨSq n).eval x₀ := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hD1 : 1 ≤ n.natAbs ^ 2 := by
    have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have := pow_ne_zero 2 hna
    omega
  set f : F[X] := (V⁄F).Φ n - Polynomial.C ξ * (V⁄F).ΨSq n with hf
  have hcoeff : f.coeff (n.natAbs ^ 2) = 1 := by
    rw [hf, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      WeierstrassCurve.coeff_Φ,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt ((V⁄F).natDegree_ΨSq_le n) (by omega)),
      mul_zero, sub_zero]
  have hf0 : f ≠ 0 := by
    intro hc
    rw [hc, Polynomial.coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hle : n.natAbs ^ 2 ≤ f.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)
  have hdeg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf0]
    intro hc
    have hnd : f.natDegree = 0 := by exact_mod_cast hc
    omega
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root f hdeg
  have hrel : ((V⁄F).Φ n).eval x₀ = ξ * ((V⁄F).ΨSq n).eval x₀ := by
    have hx := hx₀
    rw [Polynomial.IsRoot, hf, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hx
    linear_combination hx
  have hydeg : (TorsionCard.yQuad V x₀).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero V x₀),
      TorsionCard.yQuad_natDegree]
    norm_num
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (TorsionCard.yQuad V x₀) hydeg
  refine ⟨x₀, y₀, ?_, hrel⟩
  exact (V⁄F).toAffine.equation_iff_nonsingular.mp
    ((TorsionCard.eval_yQuad_eq_zero_iff_equation V x₀ y₀).mp hy₀)

/-- **Divisibility of the point group over an algebraically closed field**, for
every nonzero integer and in every characteristic.

Same argument as `TorsionCard.smul_surjective`, over the stronger fibre node
above: `ΨSqₙ(x₀) ≠ 0` by the Bézout identity `isCoprime_Φ_ΨSq` (a common root
would contradict `A·Φ + B·ΨSq = 1`), so `TorsionCard.exists_smul_some_eq`
computes `n • (x₀, y₀)` as an affine point with `x`-coordinate `ξ`; its
`y`-coordinate is `η` or `negY ξ η`, and in the latter case negating the
preimage fixes it. -/
theorem zsmul_surjective_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) : Function.Surjective (fun P : (V⁄F).Point => n • P) := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hpoint : ∀ {x₁ y₁ x₂ y₂ : F} (h₁ : (V⁄F).toAffine.Nonsingular x₁ y₁)
      (h₂ : (V⁄F).toAffine.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
      (Affine.Point.some x₁ y₁ h₁ : (V⁄F).Point) = Affine.Point.some x₂ y₂ h₂ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    subst hx; subst hy; rfl
  intro P₀
  cases P₀ with
  | zero => exact ⟨0, smul_zero _⟩
  | some ξ η h₀ =>
    obtain ⟨x₀, y₀, hns, hrel⟩ := exists_point_x_smul_algClosed V hn ξ
    have hΨ : ((V⁄F).ΨSq n).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨A, B, hAB⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq (V⁄F) hn (V⁄F).isUnit_Δ
      have hev := congrArg (Polynomial.eval x₀) hAB
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_one, hrel, h0] at hev
      simp at hev
    obtain ⟨x', y', h', hsmul, hx'⟩ := TorsionCard.exists_smul_some_eq V hn hns hΨ
    have hx : x' = ξ := by
      rw [hrel] at hx'
      exact mul_right_cancel₀ hΨ hx'
    rcases Affine.Y_eq_of_X_eq h'.1 h₀.1 hx with hy | hy
    · exact ⟨Affine.Point.some x₀ y₀ hns, hsmul.trans (hpoint h' h₀ hx hy)⟩
    · refine ⟨-(Affine.Point.some x₀ y₀ hns), ?_⟩
      show n • (-(Affine.Point.some x₀ y₀ hns) : (V⁄F).Point) = _
      rw [smul_neg, hsmul, Affine.Point.neg_some]
      exact hpoint _ h₀ hx (by rw [hy, hx, Affine.negY_negY])

/-- **Finiteness of the `n`-torsion over an algebraically closed field**, in
every characteristic.

A nonzero `n`-torsion point `(x, y)` has `ΨSqₙ(x) = 0`
(`TorsionCard.smul_some_eq_zero_iff`); `ΨSqₙ ≠ 0` by `ΨSq_ne_zero'`, so there are
finitely many such `x`, and at most two points lie over each
(`TorsionCard.pointsAt`). -/
theorem finite_zsmul_torsion_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) : {P : (V⁄F).Point | n • P = 0}.Finite := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hΨ : (V⁄F).ΨSq n ≠ 0 := ΨSq_ne_zero' (V⁄F) hn
  refine Set.Finite.subset (Finset.finite_toSet (insert (0 : (V⁄F).Point)
    (((V⁄F).ΨSq n).roots.toFinset.biUnion (TorsionCard.pointsAt V)))) ?_
  intro P hP
  simp only [Set.mem_setOf_eq] at hP
  rw [Finset.mem_coe]
  cases P with
  | zero => exact Finset.mem_insert_self _ _
  | some x y h =>
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩)
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hΨ, Polynomial.IsRoot]
      exact (TorsionCard.smul_some_eq_zero_iff V hn h).mp hP
    · exact (TorsionCard.mem_pointsAt_iff V).mpr ⟨y, h, rfl⟩

/-- **PROVEN.** Multiplication by a nonzero integer is surjective on the points of
an elliptic curve over an algebraically closed field.

This is the divisibility of `E(F)`, and it is one of the two geometric inputs on
which the degree/dual arithmetic rests. It is *not* formal: a homomorphic image
of a divisible group need not be the whole target. -/
theorem nsmul_surjective [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun P : W.Point => n • P) := by
  have h : Function.Surjective (fun P : W.Point => (n : ℤ) • P) :=
    zsmul_surjective_algClosed W (Int.natCast_ne_zero.mpr hn)
  intro Q
  obtain ⟨P, hP⟩ := h Q
  exact ⟨P, by simpa only [natCast_zsmul] using hP⟩

/-- **PROVEN.** The `n`-torsion of an elliptic curve is finite.

The second geometric input. Over an algebraically closed field of characteristic
zero it is in fact `(ℤ/n)²`; only finiteness is used here — and, unlike the
count, finiteness needs no hypothesis on the characteristic. -/
theorem finite_nsmulKer [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.Point | n • P = 0}.Finite := by
  have h : {P : W.Point | (n : ℤ) • P = 0}.Finite :=
    finite_zsmul_torsion_algClosed W (Int.natCast_ne_zero.mpr hn)
  refine h.subset ?_
  intro P hP
  simpa only [Set.mem_setOf_eq, natCast_zsmul] using hP

/-! ### The dual isogeny -/

namespace Isogeny

/-- The dual of a nonzero isogeny, as a homomorphism of point groups.

Construction: `ker φ` is a group of order `n = deg φ`, so `n • k = 0` for every
`k ∈ ker φ` (`degree_nsmul_eq_zero`); hence multiplication by `n` on `W` kills
`ker φ` and descends along the isomorphism `W.Point ⧸ ker φ ≃+ W'.Point` supplied
by surjectivity. That the result is again an isogeny is `isRationalMap_dualHom`
plus the two geometric leaves — see `dual`. -/
noncomputable def dualHom (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) : W'.Point →+ W.Point :=
  (QuotientAddGroup.lift (AddMonoidHom.ker φ.toHom) (mulByHom W φ.degree)
      (fun k hk => by
        simpa using degree_nsmul_eq_zero hk h0)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm.toAddMonoidHom

/-- **`ψ̂ ∘ ψ = [deg ψ]`** — the defining property of the dual isogeny. -/
theorem dualHom_comp (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) (P : W.Point) :
    φ.dualHom h0 (φ.toHom P) = φ.degree • P := by
  have hsymm : (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm (φ.toHom P)
      = (QuotientAddGroup.mk P : W.Point ⧸ AddMonoidHom.ker φ.toHom) :=
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm_apply_eq.2 rfl
  simp only [dualHom, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, hsymm]
  rfl

/-- **LEAF.** The dual of an isogeny is again given by rational functions.

This is the one genuinely geometric half of the dual construction: the map
induced on the quotient is a morphism of curves. -/
theorem isRationalMap_dualHom (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) :
    IsRationalMap (φ.dualHom h0) :=
  sorry

/-- The dual isogeny, as an isogeny. -/
noncomputable def dual [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) :
    Isogeny W' W :=
  ⟨φ.dualHom h0,
   { isRationalMap := isRationalMap_dualHom φ h0
     surjective := fun _ Q => by
       obtain ⟨P, hP⟩ := nsmul_surjective (W := W) (degree_pos h0).ne' Q
       exact ⟨φ.toHom P, by rw [dualHom_comp]; exact hP⟩
     finite_ker := fun _ => by
       -- `ker φ̂ = φ (W[n])`, the image of the finite `n`-torsion.
       refine Set.Finite.subset
         ((finite_nsmulKer (W := W) (n := φ.degree) (degree_pos h0).ne').image φ.toHom) ?_
       intro Q hQ
       obtain ⟨P, rfl⟩ := φ.isIsogeny.surjective h0 Q
       refine ⟨P, ?_, rfl⟩
       have hd := dualHom_comp φ h0 P
       have hz : φ.dualHom h0 (φ.toHom P) = 0 := hQ
       rw [hd] at hz
       exact hz }⟩

@[simp] theorem dual_toHom [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W')
    (h0 : φ.toHom ≠ 0) : (φ.dual h0).toHom = φ.dualHom h0 := rfl

/-- **`ψ̂ ∘ ψ = [deg ψ]`**, packaged as an equation of isogenies. -/
theorem dual_comp [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0)
    (P : W.Point) : ((φ.dual h0).comp φ).toHom P = φ.degree • P :=
  dualHom_comp φ h0 P

/-- The group-theoretic core of `degree_comp`, isolated from the curves: for a
composite `h ∘ f` with `f` SURJECTIVE, the kernel cardinalities multiply.

`ker f ↪ ker (h ∘ f) ↠ ker h` is exact — the second map is `f` restricted, which
is onto `ker h` precisely because `f` is onto — so Lagrange in `ker (h ∘ f)`
gives the product. Surjectivity of `f` is not decoration: without it the image
of `f` may meet `ker h` in a proper subgroup and the identity fails. -/
theorem card_ker_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (h : B →+ C) (hf : Function.Surjective f) :
    Nat.card (AddMonoidHom.ker (h.comp f)) =
      Nat.card (AddMonoidHom.ker h) * Nat.card (AddMonoidHom.ker f) := by
  classical
  set K : AddSubgroup A := AddMonoidHom.ker (h.comp f)
  have hmem : ∀ x : K, f (x : A) ∈ AddMonoidHom.ker h := by
    intro x
    have hx : (h.comp f) (x : A) = 0 := (AddMonoidHom.mem_ker).1 x.2
    exact (AddMonoidHom.mem_ker).2 hx
  set g : K →+ AddMonoidHom.ker h :=
    AddMonoidHom.codRestrict (f.comp K.subtype) _ hmem
  have hgapp : ∀ x : K, (g x : B) = f (x : A) := fun _ => rfl
  have hgsurj : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hf b
    have haK : a ∈ K := by
      refine (AddMonoidHom.mem_ker).2 ?_
      show h (f a) = 0
      rw [ha]
      exact (AddMonoidHom.mem_ker).1 hb
    exact ⟨⟨a, haK⟩, Subtype.ext ha⟩
  have hcard1 : Nat.card (K ⧸ AddMonoidHom.ker g) = Nat.card (AddMonoidHom.ker h) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hgsurj).toEquiv
  have hfwd : ∀ x : AddMonoidHom.ker g, ((x : K) : A) ∈ AddMonoidHom.ker f := by
    intro x
    refine (AddMonoidHom.mem_ker).2 ?_
    rw [← hgapp]
    exact congrArg Subtype.val ((AddMonoidHom.mem_ker).1 x.2)
  have hbwd : ∀ y : AddMonoidHom.ker f, ((y : A) ∈ K) := by
    intro y
    refine (AddMonoidHom.mem_ker).2 ?_
    show h (f (y : A)) = 0
    rw [(AddMonoidHom.mem_ker).1 y.2, map_zero]
  have hbwd2 : ∀ y : AddMonoidHom.ker f,
      (⟨(y : A), hbwd y⟩ : K) ∈ AddMonoidHom.ker g := by
    intro y
    refine (AddMonoidHom.mem_ker).2 (Subtype.ext ?_)
    rw [hgapp]
    exact (AddMonoidHom.mem_ker).1 y.2
  have hcard2 : Nat.card (AddMonoidHom.ker g) = Nat.card (AddMonoidHom.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨((x : K) : A), hfwd x⟩
        invFun := fun y => ⟨⟨(y : A), hbwd y⟩, hbwd2 y⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  calc Nat.card K
      = Nat.card (K ⧸ AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker g) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card (AddMonoidHom.ker h) * Nat.card (AddMonoidHom.ker f) := by
        rw [hcard1, hcard2]

/-- **PROVEN.** The degree is multiplicative under composition.

Group-theoretically this is `#ker (ψ ∘ φ) = #ker φ · #ker ψ`, from the short exact
sequence `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ` whose surjectivity is surjectivity of
`φ` — that is `card_ker_comp`. The three degenerate cases are handled first: if
either factor is the zero map the composite is too, and both sides are `0`;
conversely if both are nonzero then so is the composite, again by surjectivity
of `φ`. No hypothesis on the base field is needed, because `degree` is *defined*
as the kernel cardinality.

**AXIOM NOTE.** `#print axioms` on this theorem still reports `sorryAx`, and that
is inherited from the STATEMENT, not from the proof: `Isogeny.comp` is a
structure whose `IsIsogeny` field routes through `IsIsogeny.comp`, whose
`isRationalMap` field is the still-open `IsRationalMap.comp`. So every statement
mentioning `Isogeny.comp` is tainted until that leaf closes, and this one will
become clean automatically when it does. Verified by the control
`Nat.card (ker (ψ.toHom.comp φ.toHom)) = Nat.card (ker ψ.toHom) * Nat.card (ker φ.toHom)`,
which is the same content with `Isogeny.comp` expanded away and reports exactly
`[propext, Classical.choice, Quot.sound]`; `card_ker_comp` itself is clean. -/
theorem degree_comp (φ : Isogeny W W') (ψ : Isogeny W' W'') :
    (ψ.comp φ).degree = ψ.degree * φ.degree := by
  by_cases hφ : φ.toHom = 0
  · have hc : (ψ.comp φ).toHom = 0 := by
      ext P
      show ψ.toHom (φ.toHom P) = 0
      rw [hφ, AddMonoidHom.zero_apply, map_zero]
    rw [degree_of_eq_zero hc, degree_of_eq_zero hφ, mul_zero]
  · by_cases hψ : ψ.toHom = 0
    · have hc : (ψ.comp φ).toHom = 0 := by
        ext P
        show ψ.toHom (φ.toHom P) = 0
        rw [hψ, AddMonoidHom.zero_apply]
      rw [degree_of_eq_zero hc, degree_of_eq_zero hψ, zero_mul]
    · have hcomp : (ψ.comp φ).toHom ≠ 0 := by
        intro hc
        refine hψ (AddMonoidHom.ext fun Q => ?_)
        obtain ⟨P, rfl⟩ := φ.isIsogeny.surjective hφ Q
        exact congrArg (fun f : W.Point →+ W''.Point => f P) hc
      rw [degree_of_ne_zero hcomp, degree_of_ne_zero hψ, degree_of_ne_zero hφ,
        comp_toHom]
      exact card_ker_comp φ.toHom ψ.toHom (φ.isIsogeny.surjective hφ)

end Isogeny

end WeierstrassCurve
