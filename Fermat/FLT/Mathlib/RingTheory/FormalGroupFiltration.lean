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

/-! ## The converse: a chart costs no more than the shift it proves

`not_layer_mulByL` above extracts the `ℓ`-shift from a chart.  The three
declarations below go the other way and show that, for a filtration that
is *antitone* and *exhaustive*, the chart is not extra content: the
EXACT shift alone builds one, in a single coordinate.

This matters for the consumer in
`Fermat/FLT/ModularCurve/X0.lean`, where the chart was the open leaf and
its docstring recorded the price as the formal group of a Jacobian along
its zero section — a `d`-dimensional formal group law and the
substitution calculus to evaluate it.  With `nonempty_ofExactShift` in
hand the price is instead one valuation statement about the tower, which
is what Silverman *ATAEC* IV.6.1 actually states.  Neither route is
forced: a prover who really constructs the formal group still gets a
chart directly.

**Why one coordinate suffices, and why this is not a cheat.**
`mem_layer_iff` asks only that the coordinates DETECT the layers, not
that they come from a chart of the scheme.  So `coord x := ℓ ^ (level of
x)` (and `0` when `x` lies in every layer) presents the filtration
faithfully as soon as it is antitone and `layer 0` is everything.  What
this construction cannot fake is `frob_layer`: with `lin := coord` the
Frobenius part is `coord (ℓ • x) − ℓ · coord x`, which vanishes exactly
when the level shifts by ONE, and is otherwise too shallow.  So the
whole mathematical content of the chart is concentrated in `hshift`, and
nothing is obtained for free — which is the check that this reduction is
sound rather than vacuous.

**`hshift` cannot be weakened to the half `not_layer_mulByL` produces.**
The upper bound `layer (k + 1) (mulByL x)` is needed too: without it
`coord (ℓ • x)` is only known to have level `≥ k`, and at level exactly
`k` the difference `coord (ℓ • x) − ℓ · coord x` has level `k`, against
the `ℓ * k ≥ k + 2` that `frob_layer` demands.  This is not an artefact:
a filtration where multiplication by `ℓ` does not move the level at all
has no chart, since `not_layer_mulByL` would then be false of it. -/

/-- **An antitone layer predicate is downward closed** (PROVEN). -/
theorem layer_of_le {G : Type*} {layer : ℕ → G → Prop}
    (hmono : ∀ (k : ℕ) (x : G), layer (k + 1) x → layer k x)
    {a b : ℕ} (hab : a ≤ b) {x : G} (h : layer b x) : layer a x := by
  obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
  clear hab
  induction t with
  | zero => simpa using h
  | succ t ih => exact ih (hmono _ x h)

/-- **The LEVEL COORDINATE of an antitone, exhaustive filtration**
(PROVEN).

`coord x = ℓ ^ (level of x)`, with `coord x = 0` when `x` lies in every
layer; the level is `Nat.find` of the first layer `x` escapes, minus one,
and `hzero` is what makes that subtraction harmless.  The three
conclusions are exactly what `nonempty_ofExactShift` consumes: the layers
are read off as divisibility, the value is pinned at a point of exact
level, and it is `0` on the intersection of the whole filtration.

`¬ IsUnit (ℓ : A)` together with `IsDomain A` is what makes
`ℓ ^ m ∣ ℓ ^ n ↔ m ≤ n`, and hence makes the presentation faithful; both
hypotheses are used only for that. -/
theorem exists_levelCoord {ℓ : ℕ} {A : Type*} [CommRing A] [IsDomain A]
    {G : Type*} {layer : ℕ → G → Prop}
    (hℓ0 : (ℓ : A) ≠ 0) (hℓu : ¬ IsUnit (ℓ : A))
    (hzero : ∀ x, layer 0 x)
    (hmono : ∀ (k : ℕ) (x : G), layer (k + 1) x → layer k x) :
    ∃ coord : G → A,
      (∀ (k : ℕ) (x : G), layer k x ↔ (ℓ : A) ^ k ∣ coord x) ∧
      (∀ (x : G) (n : ℕ), layer n x → ¬ layer (n + 1) x → coord x = (ℓ : A) ^ n) ∧
      (∀ x : G, (∀ k, layer k x) → coord x = 0) := by
  classical
  have hdvd : ∀ m n : ℕ, ((ℓ : A) ^ m ∣ (ℓ : A) ^ n) ↔ m ≤ n := by
    intro m n
    refine ⟨fun h => ?_, fun h => pow_dvd_pow _ h⟩
    by_contra hlt
    obtain ⟨j, rfl⟩ : ∃ j, m = n + (j + 1) := ⟨m - n - 1, by omega⟩
    obtain ⟨c, hc⟩ := h
    have hne : (ℓ : A) ^ n ≠ 0 := pow_ne_zero _ hℓ0
    have h1 : (1 : A) = (ℓ : A) ^ (j + 1) * c := by
      refine mul_left_cancel₀ hne ?_
      rw [mul_one, ← mul_assoc, ← pow_add]
      exact hc
    exact hℓu (isUnit_of_dvd_one ⟨(ℓ : A) ^ j * c, by rw [h1]; ring⟩)
  -- the first layer a point escapes is never the bottom one
  have hfindpos : ∀ (x : G) (h : ∃ k, ¬ layer k x), 1 ≤ Nat.find h := by
    intro x h
    rcases Nat.eq_zero_or_pos (Nat.find h) with hz | hp
    · exact absurd (hz ▸ hzero x) (Nat.find_spec h)
    · exact hp
  refine ⟨fun x => if h : ∃ k, ¬ layer k x then (ℓ : A) ^ (Nat.find h - 1) else 0, ?_, ?_, ?_⟩
  · intro k x
    dsimp only
    by_cases h : ∃ k, ¬ layer k x
    · have hlt : layer k x ↔ k < Nat.find h := by
        refine ⟨fun hk => ?_, fun hk => not_not.mp (Nat.find_min h hk)⟩
        by_contra hcon
        exact Nat.find_spec h (layer_of_le hmono (by omega) hk)
      rw [dif_pos h, hdvd, hlt]
      have := hfindpos x h
      omega
    · rw [dif_neg h]
      have hx : layer k x := not_not.mp (not_exists.mp h k)
      simpa using hx
  · intro x n hn hn'
    dsimp only
    have h : ∃ k, ¬ layer k x := ⟨n + 1, hn'⟩
    have hfy : Nat.find h = n + 1 := by
      refine le_antisymm (Nat.find_le hn') ?_
      by_contra hcon
      exact Nat.find_spec h (layer_of_le hmono (by omega) hn)
    rw [dif_pos h, hfy]
    congr 1
  · intro x hx
    dsimp only
    rw [dif_neg (not_exists.mpr (fun k => not_not.mpr (hx k)))]

/-- **A `FormalGroupChart` EXISTS AS SOON AS THE `ℓ`-SHIFT IS EXACT**
(PROVEN) — the converse of `not_layer_mulByL`, in one coordinate.

`hshift` is the classical statement (Silverman *ATAEC* IV.6.1) that
multiplication by `ℓ` moves a point of exact level `k ≥ 1` to one of
exact level `k + 1`; `hzero`, `hmono` and `hmul` are the bookkeeping
facts that the layers are exhaustive, decreasing, and stable under
multiplication by `ℓ`.

See the section docstring above for why the single coordinate
`ℓ ^ (level)` is a faithful presentation and why `frob_layer` is the
field that forces `hshift` rather than being satisfiable for free. -/
theorem FormalGroupChart.nonempty_ofExactShift {ℓ : ℕ} {A : Type*} [CommRing A] [IsDomain A]
    {G : Type*} {layer : ℕ → G → Prop} {mulByL : G → G}
    (hℓ0 : (ℓ : A) ≠ 0) (hℓu : ¬ IsUnit (ℓ : A))
    (hzero : ∀ x, layer 0 x)
    (hmono : ∀ (k : ℕ) (x : G), layer (k + 1) x → layer k x)
    (hmul : ∀ (k : ℕ) (x : G), layer k x → layer k (mulByL x))
    (hshift : ∀ (k : ℕ) (x : G), 1 ≤ k → layer k x → ¬ layer (k + 1) x →
      layer (k + 1) (mulByL x) ∧ ¬ layer (k + 2) (mulByL x)) :
    Nonempty (FormalGroupChart ℓ A G layer mulByL) := by
  classical
  obtain ⟨coord, hmem, hexact, hall⟩ := exists_levelCoord (layer := layer) hℓ0 hℓu hzero hmono
  refine ⟨⟨1, fun x _ => coord x, fun k x => ?_, fun x _ => coord x,
    fun x _ => coord (mulByL x) - (ℓ : A) * coord x, fun x i => by ring, fun k x h1 h2 => ?_,
    fun k x h i => ?_⟩⟩
  · exact ⟨fun hx _ => (hmem k x).mp hx, fun hx => (hmem k x).mpr (hx 0)⟩
  · exact ⟨0, fun hcon => h2 ((hmem (k + 1) x).mpr hcon)⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · -- at every level the shift is exact, so the Frobenius part VANISHES
      have hfr : coord (mulByL x) - (ℓ : A) * coord x = 0 := by
        by_cases hex : ∃ j, ¬ layer j x
        · have hpos : 1 ≤ Nat.find hex := by
            rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
            · exact absurd (hz ▸ hzero x) (Nat.find_spec hex)
            · exact hp
          obtain ⟨n, hn, hn'⟩ : ∃ n, layer n x ∧ ¬ layer (n + 1) x := by
            refine ⟨Nat.find hex - 1, not_not.mp (Nat.find_min hex (by omega)), ?_⟩
            have he : Nat.find hex - 1 + 1 = Nat.find hex := by omega
            rw [he]
            exact Nat.find_spec hex
          have hkn : 1 ≤ n := by
            by_contra hcon
            exact hn' (by
              have hz : n = 0 := by omega
              rw [hz]
              exact layer_of_le hmono hk h)
          obtain ⟨hu, hv⟩ := hshift n x hkn hn hn'
          rw [hexact x n hn hn', hexact (mulByL x) (n + 1) hu hv, pow_succ]
          ring
        · have hx : ∀ j, layer j x := fun j => not_not.mp (not_exists.mp hex j)
          rw [hall x hx, hall (mulByL x) (fun j => hmul j x (hx j))]
          ring
      rw [hfr]
      exact dvd_zero _

end Fermat
