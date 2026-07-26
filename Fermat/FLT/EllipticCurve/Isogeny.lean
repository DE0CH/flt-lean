/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Velu
-- Only for the `𝔽₅` counterexample in the FALSITY AUDIT of `IsIsogeny.add`.
public import Mathlib.Algebra.Field.ZMod

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

## `IsIsogeny` is only usable over an algebraically closed base

`IsIsogeny.add` was FALSE as originally cut, and `endSubring` therefore did not
define a subring. The refutation is machine-checked in
`WeierstrassCurve.NotIsIsogenyAdd` and written out in the FALSITY AUDIT next to
`IsIsogeny.add`; in one line, `IsIsogeny.id` holds over every field, so the
unconditional `IsIsogeny.add` asserts that `[2] = id + id` is surjective on
`W(F)`, which fails already for `y² = x³ - x` over `𝔽₅`.

`IsIsogeny.add`, `endSubring`, `End` and the `End.*` API therefore carry
`[IsAlgClosed F]`, matching `nsmul_surjective`, `finite_nsmulKer` and
`Isogeny.dual`, which always did. All consumers work over `AlgebraicClosure ℚ`,
so nothing downstream changes. `IsIsogeny.zero`, `.id`, `.neg` and `.comp` remain
unconditional and remain proven.

## Open leaves left by this file

`IsRationalMap.comp`, `IsRationalMap.add`, `IsRationalMap.isIsogeny`,
`nsmul_surjective`, `finite_nsmulKer`, `Isogeny.isRationalMap_dualHom`,
`Isogeny.degree_comp`.

`IsRationalMap.neg` was on this list and is now PROVEN. `IsIsogeny.add` was on
this list; it is now PROVEN from `IsRationalMap.add` and `IsRationalMap.isIsogeny`
after being refuted and restated.
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

/-! ### FALSITY AUDIT: `IsIsogeny.add` was FALSE, and is repaired here

**Refuted 2026-07-26 by the machine-checked counterexample below; the axiom audit
of `NotIsIsogenyAdd.isIsogeny_add_is_false` is `[propext, Classical.choice,
Quot.sound]`, so this is a genuine refutation and not a vacuous one.**

The statement as originally cut carried no hypothesis on `F`:

  `theorem IsIsogeny.add {φ ψ : W.Point →+ W'.Point}`
  `    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ)`

Instantiate it at `φ = ψ = AddMonoidHom.id`. That *is* an isogeny over **every**
field — `IsIsogeny.id` is proven unconditionally, because the identity is rational,
surjective, and has kernel `{0}` — so the conclusion asserts that
`[2] : W(F) → W(F)` is surjective whenever it is nonzero, i.e. that `W(F)` is
2-divisible. That is false for most curves over most fields: `E(ℚ)` of positive
rank is the familiar instance, and a finite field gives the cheapest formalisable
one.

Take `W₅ : y² = x³ - x` over `𝔽₅`, whose group of points is `ℤ/2 × ℤ/4`:

* `T = (0,0)` has `y = W₅.negY x y`, so `T + T = 0` while `T ≠ 0`;
* `P = (2,1)` has `y ≠ W₅.negY x y`, so `P + P ≠ 0`, hence `[2] ≠ 0`.

`W₅(𝔽₅)` is finite (via `Affine.nonsingularPointEquiv`), so `[2]` — not injective,
because it kills both `0` and `T` — cannot be surjective either.

**Why it is false, in one line.** Surjectivity *on `F`-points* is not a property of
a morphism of curves at all; it is a property of the base field. The file already
knows this: `nsmul_surjective` carries `[IsAlgClosed F]` for exactly this reason,
and `[2]` is the very map that leaf is about. `IsIsogeny.add` simply failed to
carry the same hypothesis.

**The repair, below.** `IsIsogeny.add` is restated with `[IsAlgClosed F]` and is
then a theorem, proven from `IsRationalMap.add` together with one new leaf,
`IsRationalMap.isIsogeny`, which isolates the honest geometric content: over an
algebraically closed field the `surjective` and `finite_ker` fields of `IsIsogeny`
are automatic.

**Consequence for consumers.** `endSubring` — and hence `End W`,
`End.sq_eq_intCast_iff`, `End.toIsogeny` — inherit `[IsAlgClosed F]`. Every
existing consumer (`MazurTorsion.lean`'s Atkin–Lehner leaves at levels 125 and
169) already works over `AlgebraicClosure ℚ`, so nothing downstream is lost.
`IsIsogeny.zero`, `IsIsogeny.id`, `IsIsogeny.neg` and `IsIsogeny.comp` are
untouched: each is true over an arbitrary field, and each is proven.
-/

namespace NotIsIsogenyAdd

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `y² = x³ - x` over `𝔽₅`. Its group of points is `ℤ/2 × ℤ/4`. -/
def W₅ : Affine (ZMod 5) := ⟨0, 0, 0, -1, 0⟩

theorem nonsingular_zero_zero : W₅.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

theorem nonsingular_two_one : W₅.Nonsingular 2 1 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

/-- The 2-torsion point `(0,0)`. -/
def T : W₅.Point := Affine.Point.some 0 0 nonsingular_zero_zero

/-- A point of order 4, witnessing that `[2] ≠ 0`. -/
def P : W₅.Point := Affine.Point.some 2 1 nonsingular_two_one

theorem T_ne_zero : T ≠ 0 := Affine.Point.some_ne_zero _

theorem T_add_T : T + T = 0 :=
  Affine.Point.add_self_of_Y_eq (h₁ := nonsingular_zero_zero)
    (show (0 : ZMod 5) = W₅.negY 0 0 by decide)

theorem P_add_P_ne_zero : P + P ≠ 0 := by
  rw [show P + P = _ from Affine.Point.add_self_of_Y_ne (h₁ := nonsingular_two_one)
    (show (1 : ZMod 5) ≠ W₅.negY 2 1 by decide)]
  exact Affine.Point.some_ne_zero _

/-- Doubling on `W₅(𝔽₅)` is not an isogeny: it is nonzero, but on a finite group it
is not injective, hence not surjective. -/
theorem not_isIsogeny_add :
    ¬ IsIsogeny (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) := by
  intro h
  haveI : Finite W₅.Point := by
    haveI : Finite (WithZero {xy : ZMod 5 × ZMod 5 // W₅.Nonsingular xy.1 xy.2}) :=
      inferInstanceAs (Finite (Option _))
    exact Finite.of_equiv _ (Affine.nonsingularPointEquiv W₅).symm
  have happ : ∀ Q : W₅.Point,
      (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q = Q + Q := fun Q => rfl
  have hne : AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point ≠ 0 := by
    intro hc
    have hc' := congrArg (fun f : W₅.Point →+ W₅.Point => f P) hc
    simp only [AddMonoidHom.zero_apply, happ] at hc'
    exact P_add_P_ne_zero hc'
  have hinj : Function.Injective (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) :=
    (Finite.injective_iff_surjective
      (f := fun Q => (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q)).2
      (h.surjective hne)
  exact T_ne_zero (hinj (by simp only [happ, T_add_T, add_zero]))

/-- **The refutation, assembled.** Both hypotheses of the original `IsIsogeny.add`
are discharged by `IsIsogeny.id`, so the unconditional statement is false. -/
theorem isIsogeny_add_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] {W W' : Affine F}
        {φ ψ : W.Point →+ W'.Point}, IsIsogeny φ → IsIsogeny ψ → IsIsogeny (φ + ψ) :=
  fun h => not_isIsogeny_add (h IsIsogeny.id IsIsogeny.id)

end NotIsIsogenyAdd

/-- **LEAF.** Over an **algebraically closed** field, a homomorphism of point groups
that is given by rational functions in the coordinates already **is** an isogeny:
the `surjective` and `finite_ker` fields of `IsIsogeny` come for free there.

This is the honest geometric content that the unconditional `IsIsogeny.add`
silently assumed, and the FALSITY AUDIT above is the proof that it cannot be
dropped.

The mathematics. A nonzero homomorphism `φ` is a nonconstant morphism of curves, so
each fibre is finite — in particular `ker φ` is. Its image is then a subgroup of
`W'(F)` of finite index in no proper way: over an algebraically closed field
`W'(F)` is divisible, and a divisible group has no proper subgroup of finite index,
while a nonconstant morphism of complete curves has closed, cofinite image. Hence
`φ` is surjective.

Relation to the other geometric leaves of this file: this statement SUBSUMES
`nsmul_surjective`, and the `n`-torsion half of `finite_nsmulKer`, as soon as
`mulByHom W n` is known to be rational (division polynomials). Those two leaves
have a separate owner and are deliberately left in place; consolidating them is a
cut-level decision, not one to make here. -/
theorem IsRationalMap.isIsogeny [IsAlgClosed F] {φ : W.Point →+ W'.Point}
    (h : IsRationalMap φ) : IsIsogeny φ :=
  sorry

/-- The pointwise sum of two isogenies over an **algebraically closed** field is an
isogeny — this is the statement that `Hom(W, W')` is a group under addition in the
category of curves.

`[IsAlgClosed F]` is NOT removable: see the FALSITY AUDIT above, where dropping it
makes the statement false already for `φ = ψ = id` over `𝔽₅`. -/
theorem IsIsogeny.add [IsAlgClosed F] {φ ψ : W.Point →+ W'.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ) :=
  (hφ.isRationalMap.add hψ.isRationalMap).isIsogeny

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
morphism.

`[IsAlgClosed F]` is inherited from `IsIsogeny.add`, which is FALSE without it —
see the FALSITY AUDIT above. Over a general field the isogenies among the
endomorphisms of `W.Point` are **not** closed under addition, so there is no such
subring; `[2] = id + id` on `W₅(𝔽₅)` is an explicit failure of `add_mem'`. -/
def endSubring [IsAlgClosed F] (W : Affine F) : Subring (AddMonoid.End W.Point) where
  carrier := {f | IsIsogeny (f : W.Point →+ W.Point)}
  zero_mem' := IsIsogeny.zero
  one_mem' := IsIsogeny.id
  add_mem' hf hg := IsIsogeny.add hf hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := IsIsogeny.comp hg hf

/-- `End W`, the endomorphism ring of `W`. -/
abbrev End [IsAlgClosed F] (W : Affine F) : Type _ := ↥(endSubring W)

/-- **The soundness lemma of this file.** In `End W` the integer `n` acts as
multiplication by `n` on points — definitionally. Together with `IsRationalMap`
inside `IsIsogeny`, this is what makes `ψ * ψ = (-125 : End W)` a statement about
complex multiplication rather than about `M₂(Ẑ)`. -/
@[simp] theorem End.intCast_apply [IsAlgClosed F] (n : ℤ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.natCast_apply [IsAlgClosed F] (n : ℕ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.mul_apply [IsAlgClosed F] (f g : End W) (P : W.Point) :
    ((f * g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) ((g : AddMonoid.End W.Point) P) := rfl

/-- **The consumer-facing form of the Atkin–Lehner condition.** `ψ * ψ = (n : End W)`
in the endomorphism ring says exactly that `ψ` applied twice is multiplication by
`n` on points.

This is the lemma the `X_0(N)` descent leaves use: `ψ * ψ = (-125 : End W)` unfolds
to `ψ (ψ P) = -125 • P` for every `P`, with `ψ` carrying its `IsIsogeny` witness —
so the condition is about an actual morphism, not about `M₂(Ẑ)`. -/
theorem End.sq_eq_intCast_iff [IsAlgClosed F] (ψ : End W) (n : ℤ) :
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
def End.toIsogeny [IsAlgClosed F] (f : End W) : Isogeny W W := ⟨(f : AddMonoid.End W.Point), f.2⟩

@[simp] theorem End.toIsogeny_toHom [IsAlgClosed F] (f : End W) :
    (End.toIsogeny f).toHom = (f : AddMonoid.End W.Point) := rfl

/-! ### The two geometric inputs -/

/-- **LEAF.** Multiplication by a nonzero integer is surjective on the points of
an elliptic curve over an algebraically closed field.

This is the divisibility of `E(F)`, and it is one of the two geometric inputs on
which the degree/dual arithmetic rests. It is *not* formal: a homomorphic image
of a divisible group need not be the whole target. -/
theorem nsmul_surjective [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun P : W.Point => n • P) :=
  sorry

/-- **LEAF.** The `n`-torsion of an elliptic curve is finite.

The second geometric input. Over an algebraically closed field of characteristic
zero it is in fact `(ℤ/n)²`; only finiteness is used here. -/
theorem finite_nsmulKer [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.Point | n • P = 0}.Finite :=
  sorry

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

/-- **LEAF.** The degree is multiplicative under composition.

Group-theoretically this is `#ker (ψ ∘ φ) = #ker φ · #ker ψ`, from the short exact
sequence `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ` whose surjectivity is surjectivity of
`φ`. -/
theorem degree_comp (φ : Isogeny W W') (ψ : Isogeny W' W'') :
    (ψ.comp φ).degree = ψ.degree * φ.degree :=
  sorry

end Isogeny

end WeierstrassCurve
