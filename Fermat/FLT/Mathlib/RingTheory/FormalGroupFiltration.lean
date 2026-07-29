/-
Fermat/FLT/Mathlib/RingTheory/FormalGroupFiltration.lean — own work for the
Fermat project (not vendored).
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Tactic.Common

/-!
# The `ℓ`-shift of a formal-group filtration at absolute ramification index one

Let `𝒥` be a smooth commutative group scheme over a complete discrete
valuation ring `A` of residue characteristic `ℓ` and absolute ramification
index `e`, and let

`K_k = ker (𝒥(A) → 𝒥(A ⧸ 𝔪 ^ k))`

be the `𝔪`-adic filtration of the kernel of reduction.  The classical
theorem — Silverman, *AEC* IV.6.1 and IV.4.4; *ATAEC* IV.6 — is that on
`K_1` the group law is given by a formal group law `F` over `A` in `d`
coordinates (`d = dim 𝒥`), that `K_k` is exactly the locus where all
coordinates have valuation `≥ k`, and that multiplication by `ℓ` shifts
the filtration by

`v([ℓ] x) = min (e + v x, ℓ * v x)`,

with the minimum attained by the FIRST term — hence *exactly* one step of
the tower when `e = 1` — precisely when `e < (ℓ − 1) * v x`.

## What this file is, and what it is not

This file does **not** construct the formal group.  It isolates, as a
structure, the exact consequence of the formal group law that the shift
argument consumes, and proves the shift from it.  The point of the
separation is that the arithmetic — the `min` comparison, where `ℓ ≠ 2`
enters, and the cancellation — is finite, checkable and now PROVEN, while
the geometric input is a single named obligation with a precise
statement.

The structure is specialised to **absolute ramification index `e = 1`**,
i.e. to the case where the residue characteristic `ℓ` is itself a
uniformizer of `A`.  That is the only case this development needs
(`𝒥` over `ℤ_(ℓ)`), and it is what makes the divisibility bookkeeping
elementary: the layers are `ℓ ^ k ∣ ·` rather than `π ^ (e * k) ∣ ·`.

## The three fields, and why each is TRUE

Write `[ℓ](T)` for the multiplication-by-`ℓ` endomorphism of `F`, a
`d`-tuple of formal power series in `d` variables over `A`.

* **`coord_mulByL` — the decomposition `[ℓ](T) = ℓ · f(T) + h(T ^ ℓ)`.**
  Modulo `𝔪` the differential of `[ℓ]` is multiplication by `ℓ = 0`, so
  `[ℓ]` kills the cotangent space of the special fibre and therefore
  factors through the relative Frobenius: `[ℓ](T) ≡ h(T ^ ℓ) (mod ℓ)` for
  some `h` with `h(0) = 0`.  Subtracting and dividing by `ℓ` — legitimate
  because `ℓ` is a non-zero-divisor of `A` — produces `f`.  Here
  `lin x = f(coord x)` and `frob x = h(coord x ^ ℓ)`.

* **`lin_notLayer` — `f` preserves the exact level.**  The linear term of
  `[ℓ]` is `ℓ · T` and `h(T ^ ℓ)` has no linear term, so `f(T) = T + (deg
  ≥ 2)`.  Hence `f_i(x) − x_i` has valuation `≥ 2k` whenever `x` has
  level `k`, and `2k > k`, so `f` does not move the level: some
  coordinate of `f(x)` still has valuation exactly `k`.

* **`frob_layer` — the Frobenius part is deep.**  Every monomial of
  `h(T ^ ℓ)` is divisible by some `T_i ^ ℓ`, so at level `k` its value has
  valuation `≥ ℓ * k`.

Nothing here presupposes `d = 1`; `dim` is arbitrary, which is what makes
the interface usable for the Jacobian of a modular curve rather than only
for an elliptic curve.

## The `ℓ ≠ 2` hypothesis

`FormalGroupChart.not_layer_mulByL` needs `3 ≤ ℓ` and `1 ≤ k`, and the two
places it is used are exactly the two inequalities `ℓ * k ≥ k + 2` and
`k + 2 > k + 1`.  At `ℓ = 2` and `k = 1` the first fails — `2 * 1 = 2 <
3` — and the conclusion is genuinely FALSE: `𝔾ₘ` over `ℤ_p[ζ_p]` (where
`e = 1 = p − 1`) has the `p`-torsion point `ζ_p − 1` in the kernel of
reduction, so the two terms of `[ℓ](T)` have equal valuation and cancel.
The hypothesis is therefore load-bearing rather than an artefact of the
proof.

## Deliberately no `layer`-monotonicity or additivity

The structure asks for no compatibility between `layer` and any group
structure on `G`, and `G` carries no algebraic instances at all:
multiplication by `ℓ` enters as a bare function `mulByL : G → G`.  This is
what lets a consumer instantiate it at a group whose `AddCommGroup`
structure is a *term* (as `AbelianSchemeStruct.addCommGroup` is) rather
than an instance.
-/

@[expose] public section

namespace Fermat

/-- **Formal-group coordinates for an `𝔪`-adic filtration at absolute
ramification index one.**

`G` is the group of points, `layer k` is the `k`-th stage `K_k` of the
filtration as a predicate, and `mulByL` is multiplication by `ℓ`.  The
data is `dim` coordinate functions `coord` on `G` presenting the layers as
divisibility by `ℓ ^ k`, together with the decomposition of the
multiplication-by-`ℓ` series into its linear part `lin` and its Frobenius
part `frob`.

See the module docstring for why each field is true of the formal group of
a smooth commutative group scheme over a discrete valuation ring with `ℓ`
as uniformizer. -/
structure FormalGroupChart (ℓ : ℕ) (A : Type*) [CommRing A] (G : Type*)
    (layer : ℕ → G → Prop) (mulByL : G → G) where
  /-- The number of formal coordinates — the relative dimension. -/
  dim : ℕ
  /-- The formal coordinates of a point. -/
  coord : G → Fin dim → A
  /-- The `k`-th layer is exactly the locus where every coordinate is
  divisible by `ℓ ^ k`.  (Outside the kernel of reduction the coordinates
  may be junk; all that is asked is that they detect the layers.) -/
  mem_layer_iff : ∀ (k : ℕ) (x : G), layer k x ↔ ∀ i, (ℓ : A) ^ k ∣ coord x i
  /-- The linear part of the multiplication-by-`ℓ` series, `f(coord x)`
  for `[ℓ](T) = ℓ · f(T) + h(T ^ ℓ)`. -/
  lin : G → Fin dim → A
  /-- The Frobenius part of the multiplication-by-`ℓ` series,
  `h(coord x ^ ℓ)`. -/
  frob : G → Fin dim → A
  /-- `[ℓ](T) = ℓ · f(T) + h(T ^ ℓ)`, read on points. -/
  coord_mulByL : ∀ (x : G) (i : Fin dim),
    coord (mulByL x) i = (ℓ : A) * lin x i + frob x i
  /-- `f(T) = T + (deg ≥ 2)`, so `f` does not move the exact level. -/
  lin_notLayer : ∀ (k : ℕ) (x : G), layer k x → ¬ layer (k + 1) x →
    ∃ i, ¬ (ℓ : A) ^ (k + 1) ∣ lin x i
  /-- Every monomial of `h(T ^ ℓ)` is divisible by an `ℓ`-th power of a
  coordinate. -/
  frob_layer : ∀ (k : ℕ) (x : G), layer k x → ∀ i, (ℓ : A) ^ (ℓ * k) ∣ frob x i

/-- **THE `ℓ`-SHIFT: multiplication by `ℓ` moves a point of the tower up by
EXACTLY one step** (PROVEN, from a `FormalGroupChart`).

If `x` has exact level `k ≥ 1` then `ℓ • x` does not lie in level `k + 2`
— so, together with the (unused here) upper bound, its level is exactly
`k + 1`.

The proof is the valuation comparison `v([ℓ] x) = min (1 + k, ℓ * k)` in
divisibility form.  Choose by `lin_notLayer` a coordinate `i` at which
`f(x)` still has valuation exactly `k`.  The Frobenius part at `i` is
divisible by `ℓ ^ (ℓ * k)`, and `ℓ * k ≥ k + 2` because `ℓ ≥ 3` and
`k ≥ 1`; so if `ℓ • x` were in level `k + 2` then `ℓ ^ (k + 2)` would
divide `ℓ · f(x)_i`, and cancelling the non-zero-divisor `ℓ` would give
`ℓ ^ (k + 1) ∣ f(x)_i`, contradicting the choice of `i`.

**Both hypotheses are used exactly once and neither can be dropped.**
`3 ≤ ℓ` and `1 ≤ k` together give `ℓ * k ≥ 3 * k = k + 2 * k ≥ k + 2`,
which is the only inequality in the argument; at `ℓ = 2, k = 1` it fails,
and the statement itself is false there (`𝔾ₘ` over `ℤ_p[ζ_p]`). -/
theorem FormalGroupChart.not_layer_mulByL {ℓ : ℕ} {A : Type*} [CommRing A] [IsDomain A]
    {G : Type*} {layer : ℕ → G → Prop} {mulByL : G → G}
    (C : FormalGroupChart ℓ A G layer mulByL) (hℓ0 : (ℓ : A) ≠ 0) (hℓ3 : 3 ≤ ℓ)
    {k : ℕ} (hk : 1 ≤ k) {x : G} (hx : layer k x) (hx' : ¬ layer (k + 1) x) :
    ¬ layer (k + 2) (mulByL x) := by
  intro hcon
  obtain ⟨i, hi⟩ := C.lin_notLayer k x hx hx'
  refine hi ?_
  -- the Frobenius part is divisible by `ℓ ^ (ℓ * k)`, hence by `ℓ ^ (k + 2)`
  have hdeep : (ℓ : A) ^ (k + 2) ∣ C.frob x i := by
    refine dvd_trans (pow_dvd_pow ((ℓ : A)) ?_) (C.frob_layer k x hx i)
    calc k + 2 ≤ k + 2 * k := by omega
      _ = 3 * k := by ring
      _ ≤ ℓ * k := Nat.mul_le_mul_right k hℓ3
  -- the whole coordinate of `ℓ • x` is divisible by `ℓ ^ (k + 2)`
  have hall : (ℓ : A) ^ (k + 2) ∣ (ℓ : A) * C.lin x i + C.frob x i := by
    rw [← C.coord_mulByL x i]
    exact ((C.mem_layer_iff (k + 2) (mulByL x)).mp hcon) i
  -- hence so is the linear part
  have hlin : (ℓ : A) ^ (k + 2) ∣ (ℓ : A) * C.lin x i := by
    simpa using dvd_sub hall hdeep
  -- cancel the non-zero-divisor `ℓ`
  have hfac : (ℓ : A) ^ (k + 2) = (ℓ : A) * (ℓ : A) ^ (k + 1) := by ring
  rw [hfac] at hlin
  exact (mul_dvd_mul_iff_left hℓ0).mp hlin

end Fermat
