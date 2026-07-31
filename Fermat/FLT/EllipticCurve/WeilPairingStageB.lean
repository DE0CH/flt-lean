/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairingDescent

@[expose] public section

/-!
# Stage B of the translation-character witness: the Ex. 3.16(c) cross-ratio

The three stage leaves of `WeilPairing.translationChar_setup_value`
(WeilPairing.lean, Stage B of the μ-node's translation-character
bridge — Silverman *AEC* Ex. 3.16(c), HLEG-NOTES.md §4(B) L4-9 second
branch).  They are stated generically over `(F, W)` in the vocabulary
of `WeilPairingDescent.lean`'s `TautSubstrate` (`pointIdeal`,
`enumVertical`, `constHom`, `curveK`, `tautPoint`, `constPoint`,
`pointEval`), and instantiated at
`W = (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).toAffine`
by the Stage-B glue.

## The derivation being decomposed

The Miller data: `Q = p•T'`, `a` generates
`∏_κ I_{T'⊕κ}·I_{⊖κ}`, so `g := a / ∏_κ (X − x_κ)` (denominator
`enumVertical W val`) has divisor `[p]^*((Q) − (O))`; the translation
character is `g∘τ_{κ₀} = c·g` with `c ≠ 1`, `c^p = 1` (the data
produced by `descent_toClass_eq_zero_or_translationChar`).

An admissible Miller setup for the pair `(P, Q) = (κ₀, x)` supplies
generators `aP`, `aQ` of
`I_{P⊕S}^p·I_{⊖S}^p` and `I_{Q⊕R}^p·I_{⊖R}^p`, so that
`f_P := aP/(X − x_S)^p` has divisor `p(P⊕S) − p(S)` and
`f_Q := aQ/(X − x_R)^p` has divisor `p(Q⊕R) − p(R)`; the setup's Weil
value is the cross-ratio `f_P(D_Q)/f_Q(D_P)` for the balanced divisors
`D_P = (P⊕S) − (S)`, `D_Q = (Q⊕R) − (R)`, written out as a ratio of
two four-fold products of `AdjoinRoot.evalEval`s.

Fix `p`-division points `p•S' = S`, `p•R' = R`, `p•P' = P` and put
`U := S' ⊖ R'`, `V := P' ⊕ U`.  Then

* `f_Q∘[p] = c'·(g∘τ_{⊖R'})^p` (the L4-7 span comparison), and
  evaluating the BALANCED ratio at `P'⊕S'` and `S'` cancels `c'`:
  `f_Q(D_P) = [g(V)/g(U)]^p` — **stage leaf 2**
  (`millerRatio_eval_pow_of_pullback`);
* the mirror side, by Weil reciprocity between `f_P` and `g` together
  with the level-`p²` telescope
  `∏_{j<p} g((j+1)P'⊕U)/g(jP'⊕U) = g(P⊕U)/g(U) = c` (the character
  equation `heq` evaluated away from `div g`), gives
  `f_P(D_Q) = c^{±1}·[g(V)/g(U)]^p` — **stage leaf 3**
  (`exists_millerRatio_eval_translationChar`);
* both evaluations need `U`, `V` to be affine and off the support of
  `div g`, which is what the setup's field hierarchy
  `G₀ ≤ F₁ ≤ F₂` plus the abscissa avoidances buy — **stage leaf 1**
  (`exists_generic_pDivision_offset`).

Dividing the two displayed identities cancels `[g(V)/g(U)]^p` and
leaves the cross-ratio `= c^{±1}`, which is the Stage-B conclusion;
that last step is proven glue in `translationChar_setup_value`.

## The bad set

The genericity input `hbad` is the "bad subfield contains the
derivation's bad coordinates" hypothesis in the only form Stage B's
caller can supply it: the coordinates of the `p²`-torsion translates
`T'⊕κ⊕λ` and `⊖κ⊕λ` (`κ ∈ E[p]`, `λ ∈ E[p²]`) of the divisor support
of `g` all lie in the small subfield `F₁`.  Taking `λ = O` this
contains the support itself; the `λ`-translates are what the telescope
points `jP'⊕U` (`P' ∈ E[p²]`) need.
-/

namespace WeilPairing

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  {W : WeierstrassCurve.Affine F} {p : ℕ} [Fact (1 < p)]

/-- **Stage B cross-ratio bookkeeping (PROVEN)**: dividing the two
evaluation stages cancels their common `g`-ratio `p`-th power.  With
`X = [g(V)·(stuff)]`-numerator and `Y`-denominator data as produced by
the two stage leaves — `γ'δ'·Y = γδ·X` (the `Q`-side pullback
evaluation) and `αβ·Y = c^e·(α'β'·X)` (the mirror side) — the
four-fold cross-ratio products satisfy `αβγδ = c^e·(α'β'γ'δ')`. -/
theorem crossRatio_eq_of_stages {K : Type*} [Field K]
    {α β γ δ α' β' γ' δ' X Y ce : K} (hY : Y ≠ 0)
    (hpull : γ' * δ' * Y = γ * δ * X)
    (hmirror : α * β * Y = ce * (α' * β' * X)) :
    α * β * γ * δ = ce * (α' * β' * γ' * δ') := by
  refine mul_right_cancel₀ hY ?_
  calc α * β * γ * δ * Y = α * β * Y * (γ * δ) := by ring
    _ = ce * (α' * β' * X) * (γ * δ) := by rw [hmirror]
    _ = ce * α' * β' * (γ * δ * X) := by ring
    _ = ce * α' * β' * (γ' * δ' * Y) := by rw [← hpull]
    _ = ce * (α' * β' * γ' * δ') * Y := by ring

omit [IsAlgClosed F] in
/-- **The `F₂`-rational points form a subgroup** (PROVEN): if a subfield
`F₂` contains the curve's coefficients, the curve descends to `F₂` and
the points with both coordinates in `F₂` are exactly the image of the
`F₂`-points under the base-change map `pointMap F₂.subtype` — an
additive group homomorphism, so its range is a subgroup.  This is the
"addition formulas preserve the subfield" step of leaf 1, obtained from
`pointMap_add` rather than from the formulas themselves. -/
theorem exists_pointSubgroup_of_subfield {F₂ : Subfield F}
    (ha₁ : W.a₁ ∈ F₂) (ha₂ : W.a₂ ∈ F₂) (ha₃ : W.a₃ ∈ F₂)
    (ha₄ : W.a₄ ∈ F₂) (ha₆ : W.a₆ ∈ F₂) :
    ∃ G : AddSubgroup W.Point,
      (∀ (x y : F) (h : W.Nonsingular x y), x ∈ F₂ → y ∈ F₂ →
        (WeierstrassCurve.Affine.Point.some x y h : W.Point) ∈ G) ∧
      (∀ (x y : F) (h : W.Nonsingular x y),
        (WeierstrassCurve.Affine.Point.some x y h : W.Point) ∈ G →
          x ∈ F₂ ∧ y ∈ F₂) := by
  classical
  set W₂ : WeierstrassCurve.Affine F₂ :=
    ⟨⟨W.a₁, ha₁⟩, ⟨W.a₂, ha₂⟩, ⟨W.a₃, ha₃⟩, ⟨W.a₄, ha₄⟩, ⟨W.a₆, ha₆⟩⟩ with hW₂
  have hmap : (W₂.map F₂.subtype).toAffine = W := rfl
  set f : W₂.Point →+ W.Point :=
    { toFun := fun Z => castPoint hmap (pointMap F₂.subtype Z)
      map_zero' := by rw [pointMap_zero, castPoint_zero]
      map_add' := fun P R => by rw [pointMap_add, castPoint_add] } with hfdef
  have hns' : ∀ (u v : F₂), W₂.Nonsingular u v →
      W.Nonsingular (F₂.subtype u) (F₂.subtype v) := fun u v huv =>
    (W₂.map_nonsingular F₂.subtype.injective u v).mpr huv
  have hfsome : ∀ (u v : F₂) (huv : W₂.Nonsingular u v),
      f (WeierstrassCurve.Affine.Point.some u v huv) =
        (WeierstrassCurve.Affine.Point.some (F₂.subtype u) (F₂.subtype v)
          (hns' u v huv) : W.Point) := by
    intro u v huv
    show castPoint hmap (pointMap F₂.subtype
      (WeierstrassCurve.Affine.Point.some u v huv)) = _
    rw [pointMap_some]
    exact castPoint_some hmap _
  refine ⟨AddMonoidHom.range f, ?_, ?_⟩
  · intro x y h hx hy
    have hns : W₂.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
      (W₂.map_nonsingular F₂.subtype.injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
    exact ⟨WeierstrassCurve.Affine.Point.some ⟨x, hx⟩ ⟨y, hy⟩ hns,
      hfsome ⟨x, hx⟩ ⟨y, hy⟩ hns⟩
  · rintro x y h ⟨Z, hZ⟩
    cases Z with
    | zero =>
      exact absurd (hZ.symm.trans f.map_zero)
        (WeierstrassCurve.Affine.Point.some_ne_zero h)
    | some u v huv =>
      rw [hfsome, WeierstrassCurve.Affine.Point.some.injEq] at hZ
      refine ⟨?_, ?_⟩
      · rw [← hZ.1]; exact u.2
      · rw [← hZ.2]; exact v.2

omit [IsAlgClosed F] in
/-- **Vanishing locates a point in the divisor** (PROVEN): if a
generator `a` of a point-ideal product `∏_{w ∈ D} I_w` vanishes at an
affine point `ξ`, then `ξ` occurs in `D`.  Indeed `a ∈ I_ξ` gives
`∏_{w} I_w ≤ I_ξ`, and `I_ξ` is maximal hence prime, so it contains one
factor `I_w`; distinct points have coprime point ideals
(`isCoprime_pointIdeal`), which would force `I_ξ = ⊤`. -/
theorem mem_of_evalEval_eq_zero {D : Multiset W.Point} {a : W.CoordinateRing}
    (hspan : Ideal.span {a} = (D.map (pointIdeal W)).prod)
    {x y : F} (h : W.Nonsingular x y)
    (hz : AdjoinRoot.evalEval h.left a = 0) :
    (WeierstrassCurve.Affine.Point.some x y h : W.Point) ∈ D := by
  classical
  have hmem : a ∈ pointIdeal W (.some x y h) :=
    mem_pointIdeal_of_coordEval_eq_zero h hz
  have hle : (D.map (pointIdeal W)).prod ≤ pointIdeal W (.some x y h) := by
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hprime : (pointIdeal W (.some x y h)).IsPrime :=
    (xyIdeal_isMaximal h.left).isPrime
  obtain ⟨I, hI, hIle⟩ := hprime.multiset_prod_le.mp hle
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hI
  by_cases hwe : w = (WeierstrassCurve.Affine.Point.some x y h : W.Point)
  · exact hwe ▸ hw
  · exfalso
    have hsup := Ideal.isCoprime_iff_sup_eq.mp (isCoprime_pointIdeal hwe)
    rw [sup_eq_right.mpr hIle] at hsup
    exact hprime.ne_top hsup

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Constants evaluate to themselves** (PROVEN): `coordEval_coordC` in
the `AdjoinRoot.evalEval` spelling the Stage-B statements use
(`coordEval W h` is by definition `AdjoinRoot.evalEval h`). -/
lemma evalEval_coordC {x y : F} (h : W.Equation x y) (d : F) :
    AdjoinRoot.evalEval h (coordC W d) = d :=
  coordEval_coordC (W := W) h d

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The coordinate function `X` evaluates to the abscissa** (PROVEN):
`coordEval_coordX` in the `AdjoinRoot.evalEval` spelling. -/
lemma evalEval_coordX {x y : F} (h : W.Equation x y) :
    AdjoinRoot.evalEval h (coordX W) = x :=
  coordEval_coordX (W := W) h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The coordinate function `Y` evaluates to the ordinate** (PROVEN):
`coordEval_coordY` in the `AdjoinRoot.evalEval` spelling. -/
lemma evalEval_coordY {x y : F} (h : W.Equation x y) :
    AdjoinRoot.evalEval h (coordY W) = y :=
  coordEval_coordY (W := W) h

/-! ### Specialization at an affine point: reduction, away from its kernel

`exists_pointEval_specialization` below asks for the VALUE at an affine
point `Z` of a function `z ∘ (τ_Q ∘ [m])` that the substrate only ever
presents as an element of the function field `K = Frac F[W]`.  There is
no ring map `K → F` — specialization at `Z` is only partially defined —
so everything here is organised around a RELATION rather than a map.

`EvalsTo hZ w c` says "`w ∈ K` is regular at `Z` with value `c`", spelled
without any localisation as "`w` is a fraction `n/d` of coordinate-ring
elements with `d(Z) ≠ 0` and `n(Z) = c·d(Z)`" — literally the conclusion
shape of the leaf.  It is a partial ring homomorphism (`EvalsTo.add`,
`.mul`, `.div`, and uniqueness of the value), which is all that is needed
to transport the group law: `SpecPoint hZ ω P` says the `K`-point `ω` of
`curveK W` reduces to the `F`-point `P` of `W`, and `SpecPoint.add`
proves the reduction of a sum is the sum of the reductions **whenever the
sum of the reductions is affine**.

That side condition is the whole design.  Silverman *AEC* VII.2.1 proves
reduction is a homomorphism on all of `E(K)`, but its kernel `E₁` — the
points with a pole at `Z` — is the formal group, which mathlib does not
have (nor does mathlib connect its division polynomials to `n • P`, the
other classical route).  Neither is needed: the induction on `m` that
computes the reduction of `Q ⊕ m•taut` splits `Q = Q' ⊕ R`, with `Q'`
chosen — using that `W(F)` is INFINITE, `F` being algebraically closed —
so that BOTH partial sums `Q' ⊕ k•Z` and `R ⊕ Z` stay affine.  Only two
points of `W(F)` are excluded per step, and there is always a third.

The one substantial input is that `slope` specializes.  It does, because
of the cleared relation `(y₁ − y₂)·A = (x₁ − x₂)·B` obtained by
subtracting the two Weierstrass equations, where
`A = y₁ + y₂ + a₁x₁ + a₃` and `B = x₁² + x₁x₂ + x₂² + a₂(x₁+x₂) + a₄ −
a₁y₂`: when the two points have the SAME reduction the reductions of `A`
and `B` are exactly the denominator `2v + a₁u + a₃` and numerator
`3u² + 2a₂u + a₄ − a₁v` of the TANGENT slope downstairs, and `Ā ≠ 0` is
precisely "the reduced sum is not `O`".  So the secant slope upstairs
specializes to the tangent slope downstairs even though its own numerator
and denominator both degenerate.  `addX` and `addY` are polynomial in the
slope and go along for the ride. -/

section Specialization

variable {xZ yZ : F}

/-- **Regularity with a value at an affine point**, stated without a
partial specialization map `K → F` (which does not exist): `EvalsTo hZ w
c` says the function-field element `w` is a fraction `n/d` of two
coordinate-ring elements whose denominator does not vanish at
`Z = (xZ, yZ)` and whose numerator has value `c·d(Z)` there — i.e. `w` is
regular at `Z` with value `c`.  This is literally the conclusion shape of
`exists_pointEval_specialization`. -/
def EvalsTo (hZ : W.Equation xZ yZ) (w : W.FunctionField) (c : F) : Prop :=
  ∃ n d : W.CoordinateRing,
    AdjoinRoot.evalEval hZ d ≠ 0 ∧
      w * algebraMap W.CoordinateRing W.FunctionField d =
        algebraMap W.CoordinateRing W.FunctionField n ∧
      AdjoinRoot.evalEval hZ n = c * AdjoinRoot.evalEval hZ d

variable {hZ : W.Equation xZ yZ}

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The value of a regular element is unique** (PROVEN): two
presentations `n/d` and `n'/d'` of the same `w` satisfy `n·d' = n'·d` in
the coordinate ring (clear denominators and use injectivity of
`F[W] → K`), and evaluating that at `Z` gives `c·d(Z)·d'(Z) =
c'·d(Z)·d'(Z)` with both denominators nonzero. -/
theorem EvalsTo.unique {w : W.FunctionField} {c c' : F}
    (h : EvalsTo hZ w c) (h' : EvalsTo hZ w c') : c = c' := by
  obtain ⟨n, d, hd, hK, hv⟩ := h
  obtain ⟨n', d', hd', hK', hv'⟩ := h'
  have hcross : n * d' = n' * d :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField (by
      rw [map_mul, map_mul, ← hK, ← hK']; ring)
  have hev := congrArg (AdjoinRoot.evalEval hZ) hcross
  rw [map_mul, map_mul, hv, hv'] at hev
  have h0 : (c - c') * (AdjoinRoot.evalEval hZ d * AdjoinRoot.evalEval hZ d') = 0 := by
    linear_combination hev
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 (mul_ne_zero hd hd')

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Coordinate-ring elements are regular with their own value**
(PROVEN): take `d = 1`. -/
theorem evalsTo_algebraMap (hZ : W.Equation xZ yZ) (a : W.CoordinateRing) :
    EvalsTo hZ (algebraMap W.CoordinateRing W.FunctionField a)
      (AdjoinRoot.evalEval hZ a) :=
  ⟨a, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one],
    by rw [map_one, mul_one]⟩

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Constants are regular with themselves as value** (PROVEN). -/
theorem evalsTo_constHom (hZ : W.Equation xZ yZ) (c : F) :
    EvalsTo hZ (constHom W c) c := by
  have h := evalsTo_algebraMap hZ (coordC W c)
  rwa [algebraMap_coordC, evalEval_coordC hZ c] at h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **`1` is regular with value `1`** (PROVEN). -/
theorem evalsTo_one (hZ : W.Equation xZ yZ) : EvalsTo hZ 1 1 := by
  have h := evalsTo_algebraMap hZ 1
  rwa [map_one, map_one] at h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under addition** (PROVEN): common
denominator. -/
theorem EvalsTo.add {w₁ w₂ : W.FunctionField} {c₁ c₂ : F}
    (h₁ : EvalsTo hZ w₁ c₁) (h₂ : EvalsTo hZ w₂ c₂) :
    EvalsTo hZ (w₁ + w₂) (c₁ + c₂) := by
  obtain ⟨n₁, d₁, hd₁, hK₁, hv₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hK₂, hv₂⟩ := h₂
  refine ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hd₁ hd₂
  · rw [map_mul, map_add, map_mul, map_mul]
    linear_combination (algebraMap W.CoordinateRing W.FunctionField d₂) * hK₁ +
      (algebraMap W.CoordinateRing W.FunctionField d₁) * hK₂
  · rw [map_mul, map_add, map_mul, map_mul]
    linear_combination (AdjoinRoot.evalEval hZ d₂) * hv₁ +
      (AdjoinRoot.evalEval hZ d₁) * hv₂

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under multiplication** (PROVEN). -/
theorem EvalsTo.mul {w₁ w₂ : W.FunctionField} {c₁ c₂ : F}
    (h₁ : EvalsTo hZ w₁ c₁) (h₂ : EvalsTo hZ w₂ c₂) :
    EvalsTo hZ (w₁ * w₂) (c₁ * c₂) := by
  obtain ⟨n₁, d₁, hd₁, hK₁, hv₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hK₂, hv₂⟩ := h₂
  refine ⟨n₁ * n₂, d₁ * d₂, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hd₁ hd₂
  · rw [map_mul, map_mul]
    linear_combination (w₂ * algebraMap W.CoordinateRing W.FunctionField d₂) * hK₁ +
      (algebraMap W.CoordinateRing W.FunctionField n₁) * hK₂
  · rw [map_mul, map_mul]
    linear_combination (AdjoinRoot.evalEval hZ n₂) * hv₁ +
      (c₁ * AdjoinRoot.evalEval hZ d₁) * hv₂

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under negation** (PROVEN). -/
theorem EvalsTo.neg {w : W.FunctionField} {c : F} (h : EvalsTo hZ w c) :
    EvalsTo hZ (-w) (-c) := by
  obtain ⟨n, d, hd, hK, hv⟩ := h
  refine ⟨-n, d, hd, ?_, ?_⟩
  · rw [map_neg]; linear_combination -hK
  · rw [map_neg]; linear_combination -hv

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under subtraction** (PROVEN). -/
theorem EvalsTo.sub {w₁ w₂ : W.FunctionField} {c₁ c₂ : F}
    (h₁ : EvalsTo hZ w₁ c₁) (h₂ : EvalsTo hZ w₂ c₂) :
    EvalsTo hZ (w₁ - w₂) (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under powers** (PROVEN). -/
theorem EvalsTo.pow {w : W.FunctionField} {c : F} (h : EvalsTo hZ w c) :
    ∀ k : ℕ, EvalsTo hZ (w ^ k) (c ^ k)
  | 0 => by simpa only [pow_zero] using evalsTo_one hZ
  | (k + 1) => by rw [pow_succ, pow_succ]; exact (h.pow k).mul h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **A regular element with nonzero value is nonzero** (PROVEN): if
`w = 0` then its numerator is `0`, so `c·d(Z) = 0` with `d(Z) ≠ 0`. -/
theorem EvalsTo.ne_zero {w : W.FunctionField} {c : F} (h : EvalsTo hZ w c)
    (hc : c ≠ 0) : w ≠ 0 := by
  obtain ⟨n, d, hd, hK, hv⟩ := h
  intro h0
  rw [h0, zero_mul] at hK
  have hn : n = 0 :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
      (hK.symm.trans (map_zero _).symm)
  rw [hn, map_zero] at hv
  rcases mul_eq_zero.mp hv.symm with h1 | h1
  · exact hc h1
  · exact hd h1

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Regularity is closed under division with nonvanishing
denominator** (PROVEN): `(n₁/d₁)/(n₂/d₂) = (n₁d₂)/(d₁n₂)`, and `n₂(Z) =
c₂·d₂(Z) ≠ 0` is what makes the new denominator survive. -/
theorem EvalsTo.div {w₁ w₂ : W.FunctionField} {c₁ c₂ : F}
    (h₁ : EvalsTo hZ w₁ c₁) (h₂ : EvalsTo hZ w₂ c₂) (hc₂ : c₂ ≠ 0) :
    EvalsTo hZ (w₁ / w₂) (c₁ / c₂) := by
  have hw₂ : w₂ ≠ 0 := h₂.ne_zero hc₂
  obtain ⟨n₁, d₁, hd₁, hK₁, hv₁⟩ := h₁
  obtain ⟨n₂, d₂, hd₂, hK₂, hv₂⟩ := h₂
  have hn₂ : AdjoinRoot.evalEval hZ n₂ ≠ 0 := by
    rw [hv₂]; exact mul_ne_zero hc₂ hd₂
  refine ⟨n₁ * d₂, d₁ * n₂, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hd₁ hn₂
  · rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hw₂]
    linear_combination (algebraMap W.CoordinateRing W.FunctionField n₂) * hK₁ -
      (algebraMap W.CoordinateRing W.FunctionField n₁) * hK₂
  · rw [map_mul, map_mul, hv₁, hv₂, div_mul_eq_mul_div, eq_div_iff hc₂]
    ring

end Specialization

omit [DecidableEq F] [IsAlgClosed F] in
/-- The base-changed curve's `a₁` is the constant `a₁` (PROVEN, `rfl`). -/
lemma curveK_a₁ (W : WeierstrassCurve.Affine F) :
    (curveK W).a₁ = constHom W W.a₁ := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- The base-changed curve's `a₂` is the constant `a₂` (PROVEN, `rfl`). -/
lemma curveK_a₂ (W : WeierstrassCurve.Affine F) :
    (curveK W).a₂ = constHom W W.a₂ := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- The base-changed curve's `a₃` is the constant `a₃` (PROVEN, `rfl`). -/
lemma curveK_a₃ (W : WeierstrassCurve.Affine F) :
    (curveK W).a₃ = constHom W W.a₃ := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- The base-changed curve's `a₄` is the constant `a₄` (PROVEN, `rfl`). -/
lemma curveK_a₄ (W : WeierstrassCurve.Affine F) :
    (curveK W).a₄ = constHom W W.a₄ := rfl

section Specialization2

variable {xZ yZ : F} {hZ : W.Equation xZ yZ}

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The negation formula specializes** (PROVEN): `negY` is a
polynomial in the coordinates and the constants. -/
theorem evalsTo_negY {x y : W.FunctionField} {u v : F}
    (hx : EvalsTo hZ x u) (hy : EvalsTo hZ y v) :
    EvalsTo hZ ((curveK W).negY x y) (W.negY u v) := by
  simp only [WeierstrassCurve.Affine.negY, curveK_a₁, curveK_a₃]
  exact (hy.neg.sub ((evalsTo_constHom hZ W.a₁).mul hx)).sub (evalsTo_constHom hZ W.a₃)

omit [IsAlgClosed F] in
/-- **The group-law slope specializes** (PROVEN) — the one substantial
step of the reduction argument.

When the two reduced points have distinct abscissae the upstairs slope is
the secant `(y₁ − y₂)/(x₁ − x₂)` with a denominator that does not
degenerate, and there is nothing to do.

When they coincide the secant's numerator AND denominator both vanish at
`Z`, and the value has to be recovered from the cleared relation
`(y₁ − y₂)·A = (x₁ − x₂)·B` obtained by subtracting the two Weierstrass
equations, with `A = y₁ + y₂ + a₁x₁ + a₃` and
`B = x₁² + x₁x₂ + x₂² + a₂(x₁+x₂) + a₄ − a₁y₂`.  Their reductions are
`2v + a₁u + a₃` and `3u² + 2a₂u + a₄ − a₁v`, i.e. exactly the denominator
and numerator of the TANGENT slope at the common reduction; and `A`'s
reduction is nonzero precisely because the reduced sum is assumed affine
(`hne'`).  Since `A ≠ 0` upstairs too, the slope equals `B/A` in BOTH
upstairs configurations (`x₁ = x₂`, where it is the tangent slope
outright, and `x₁ ≠ x₂`, by the cleared relation), so it specializes. -/
theorem evalsTo_slope
    {x₁ y₁ x₂ y₂ : W.FunctionField} {u₁ v₁ u₂ v₂ : F}
    (hk₁ : (curveK W).Equation x₁ y₁) (hk₂ : (curveK W).Equation x₂ y₂)
    (hg₁ : W.Equation u₁ v₁) (hg₂ : W.Equation u₂ v₂)
    (hx₁ : EvalsTo hZ x₁ u₁) (hy₁ : EvalsTo hZ y₁ v₁)
    (hx₂ : EvalsTo hZ x₂ u₂) (hy₂ : EvalsTo hZ y₂ v₂)
    (hne' : ¬(u₁ = u₂ ∧ v₁ = W.negY u₂ v₂))
    (hneK : ¬(x₁ = x₂ ∧ y₁ = (curveK W).negY x₂ y₂)) :
    EvalsTo hZ ((curveK W).slope x₁ x₂ y₁ y₂) (W.slope u₁ u₂ v₁ v₂) := by
  by_cases hu : u₁ = u₂
  · -- the two reductions coincide: the tangent case downstairs
    have hvne : v₁ ≠ W.negY u₂ v₂ := fun hc => hne' ⟨hu, hc⟩
    have hv : v₁ = v₂ := Y_eq_of_Y_ne hg₁ hg₂ hu hvne
    have hnegeq : W.negY u₁ v₁ = W.negY u₂ v₂ := by rw [hu, hv]
    have hA0 : v₁ - W.negY u₁ v₁ ≠ 0 := sub_ne_zero.mpr (hnegeq ▸ hvne)
    obtain ⟨AK, hAK⟩ : ∃ t : W.FunctionField,
        t = y₁ + y₂ + (curveK W).a₁ * x₁ + (curveK W).a₃ := ⟨_, rfl⟩
    obtain ⟨BK, hBK⟩ : ∃ t : W.FunctionField,
        t = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (curveK W).a₂ * (x₁ + x₂) + (curveK W).a₄ -
          (curveK W).a₁ * y₂ := ⟨_, rfl⟩
    have hAF : EvalsTo hZ AK (v₁ - W.negY u₁ v₁) := by
      rw [hAK, curveK_a₁, curveK_a₃]
      have he : v₁ - W.negY u₁ v₁ = v₁ + v₂ + W.a₁ * u₁ + W.a₃ := by
        simp only [WeierstrassCurve.Affine.negY]; rw [← hv]; ring
      rw [he]
      exact ((hy₁.add hy₂).add ((evalsTo_constHom hZ W.a₁).mul hx₁)).add
        (evalsTo_constHom hZ W.a₃)
    have hBF : EvalsTo hZ BK (3 * u₁ ^ 2 + 2 * W.a₂ * u₁ + W.a₄ - W.a₁ * v₁) := by
      rw [hBK, curveK_a₁, curveK_a₂, curveK_a₄]
      have he : 3 * u₁ ^ 2 + 2 * W.a₂ * u₁ + W.a₄ - W.a₁ * v₁ =
          u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 + W.a₂ * (u₁ + u₂) + W.a₄ - W.a₁ * v₂ := by
        rw [← hu, ← hv]; ring
      rw [he]
      exact ((((hx₁.pow 2).add (hx₁.mul hx₂)).add (hx₂.pow 2)).add
        ((evalsTo_constHom hZ W.a₂).mul (hx₁.add hx₂))).add
        (evalsTo_constHom hZ W.a₄) |>.sub ((evalsTo_constHom hZ W.a₁).mul hy₂)
    have hAK0 : AK ≠ 0 := hAF.ne_zero hA0
    have he₁ : y₁ ^ 2 + (curveK W).a₁ * x₁ * y₁ + (curveK W).a₃ * y₁ =
        x₁ ^ 3 + (curveK W).a₂ * x₁ ^ 2 + (curveK W).a₄ * x₁ + (curveK W).a₆ := by
      rw [← WeierstrassCurve.Affine.equation_iff]; exact hk₁
    have he₂ : y₂ ^ 2 + (curveK W).a₁ * x₂ * y₂ + (curveK W).a₃ * y₂ =
        x₂ ^ 3 + (curveK W).a₂ * x₂ ^ 2 + (curveK W).a₄ * x₂ + (curveK W).a₆ := by
      rw [← WeierstrassCurve.Affine.equation_iff]; exact hk₂
    have hident : (y₁ - y₂) * AK = (x₁ - x₂) * BK := by
      rw [hAK, hBK]; linear_combination he₁ - he₂
    have hslopeK : (curveK W).slope x₁ x₂ y₁ y₂ = BK / AK := by
      by_cases hxK : x₁ = x₂
      · have hyK : y₁ ≠ (curveK W).negY x₂ y₂ := fun hc => hneK ⟨hxK, hc⟩
        have hyyK : y₁ = y₂ := Y_eq_of_Y_ne hk₁ hk₂ hxK hyK
        have hnegeqK : (curveK W).negY x₁ y₁ = (curveK W).negY x₂ y₂ := by
          rw [hxK, hyyK]
        have hden : y₁ - (curveK W).negY x₁ y₁ ≠ 0 :=
          sub_ne_zero.mpr (hnegeqK ▸ hyK)
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hxK hyK,
          div_eq_div_iff hden hAK0, hAK, hBK]
        simp only [WeierstrassCurve.Affine.negY]
        rw [← hxK, ← hyyK]
        ring
      · rw [WeierstrassCurve.Affine.slope_of_X_ne hxK,
          div_eq_div_iff (sub_ne_zero.mpr hxK) hAK0]
        linear_combination hident
    rw [hslopeK, WeierstrassCurve.Affine.slope_of_Y_ne hu hvne]
    exact hBF.div hAF hA0
  · have hxne : x₁ ≠ x₂ := fun hc => hu ((hc ▸ hx₁).unique hx₂)
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne,
      WeierstrassCurve.Affine.slope_of_X_ne hu]
    exact (hy₁.sub hy₂).div (hx₁.sub hx₂) (sub_ne_zero.mpr hu)

end Specialization2

section SpecPointSection

variable {xZ yZ : F}

/-- **Reduction of a `K`-point of `curveK W` at the affine point `Z`**:
`SpecPoint hZ ω P` says `ω` is either the origin with `P` the origin, or
affine with both coordinates regular at `Z` and reducing to the
coordinates of the affine point `P`.  This is the graph of Silverman's
reduction map `E(K) → E(F)`, RESTRICTED to the complement of its kernel
(points with a pole at `Z` are simply not related to anything). -/
def SpecPoint (hZ : W.Nonsingular xZ yZ) (ω : (curveK W).Point) (P : W.Point) :
    Prop :=
  (ω = 0 ∧ P = 0) ∨
    ∃ (x y : W.FunctionField) (h : (curveK W).Nonsingular x y) (u v : F)
      (g : W.Nonsingular u v),
      ω = WeierstrassCurve.Affine.Point.some x y h ∧
        P = WeierstrassCurve.Affine.Point.some u v g ∧
        EvalsTo hZ.left x u ∧ EvalsTo hZ.left y v

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Constant points reduce to themselves** (PROVEN). -/
theorem specPoint_constPoint (hZ : W.Nonsingular xZ yZ) (Q : W.Point) :
    SpecPoint hZ (constPoint W Q) Q := by
  cases Q with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | some u v g =>
    exact Or.inr ⟨constHom W u, constHom W v, _, u, v, g, rfl, rfl,
      evalsTo_constHom hZ.left u, evalsTo_constHom hZ.left v⟩

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The tautological point reduces to `Z`** (PROVEN): its coordinates
are the images of the coordinate atoms `X`, `Y`, whose values at `Z` are
`xZ`, `yZ`. -/
theorem specPoint_tautPoint (hΔ : W.Δ ≠ 0) (hZ : W.Nonsingular xZ yZ) :
    SpecPoint hZ (tautPoint W hΔ)
      (WeierstrassCurve.Affine.Point.some xZ yZ hZ) := by
  refine Or.inr ⟨tautX W, tautY W, taut_nonsingular W hΔ, xZ, yZ, hZ, rfl, rfl, ?_, ?_⟩
  · have h := evalsTo_algebraMap hZ.left (coordX W)
    rwa [algebraMap_coordX, evalEval_coordX hZ.left] at h
  · have h := evalsTo_algebraMap hZ.left (coordY W)
    rwa [algebraMap_coordY, evalEval_coordY hZ.left] at h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Reduction commutes with negation** (PROVEN). -/
theorem SpecPoint.neg {hZ : W.Nonsingular xZ yZ} {ω : (curveK W).Point}
    {P : W.Point} (h : SpecPoint hZ ω P) : SpecPoint hZ (-ω) (-P) := by
  rcases h with ⟨h1, h2⟩ | ⟨x, y, hk, u, v, hg, rfl, rfl, hx, hy⟩
  · exact Or.inl ⟨by rw [h1]; exact WeierstrassCurve.Affine.Point.neg_zero,
      by rw [h2]; exact WeierstrassCurve.Affine.Point.neg_zero⟩
  · rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.neg_some]
    exact Or.inr ⟨x, (curveK W).negY x y, _, u, W.negY u v, _, rfl, rfl, hx,
      evalsTo_negY hx hy⟩

omit [IsAlgClosed F] in
/-- **Reduction commutes with addition, away from the kernel** (PROVEN):
if `ω₁`, `ω₂` reduce to `P₁`, `P₂` and `P₁ ⊕ P₂` is AFFINE, then
`ω₁ ⊕ ω₂` reduces to `P₁ ⊕ P₂`.

The affineness hypothesis does two things at once: it rules out the
vertical configuration downstairs, and (by uniqueness of reduced values)
the vertical configuration upstairs, so both sums are computed by
`Point.add_some` from the slope — which specializes by
`evalsTo_slope` — and `addX`, `addY` are polynomial in it. -/
theorem SpecPoint.add {hZ : W.Nonsingular xZ yZ}
    {ω₁ ω₂ : (curveK W).Point} {P₁ P₂ : W.Point}
    (h₁ : SpecPoint hZ ω₁ P₁) (h₂ : SpecPoint hZ ω₂ P₂) (hne : P₁ + P₂ ≠ 0) :
    SpecPoint hZ (ω₁ + ω₂) (P₁ + P₂) := by
  rcases h₁ with ⟨hz₁, hp₁⟩ | ⟨x₁, y₁, hk₁, u₁, v₁, hg₁, rfl, rfl, hx₁, hy₁⟩
  · rw [hz₁, hp₁, zero_add, zero_add]; exact h₂
  rcases h₂ with ⟨hz₂, hp₂⟩ | ⟨x₂, y₂, hk₂, u₂, v₂, hg₂, rfl, rfl, hx₂, hy₂⟩
  · rw [hz₂, hp₂, add_zero, add_zero]
    exact Or.inr ⟨x₁, y₁, hk₁, u₁, v₁, hg₁, rfl, rfl, hx₁, hy₁⟩
  have hne' : ¬(u₁ = u₂ ∧ v₁ = W.negY u₂ v₂) := fun hc =>
    hne (WeierstrassCurve.Affine.Point.add_of_Y_eq hc.1 hc.2)
  have hneK : ¬(x₁ = x₂ ∧ y₁ = (curveK W).negY x₂ y₂) := by
    rintro ⟨hxx, hyy⟩
    exact hne' ⟨(hxx ▸ hx₁).unique hx₂, (hyy ▸ hy₁).unique (evalsTo_negY hx₂ hy₂)⟩
  have hslope := evalsTo_slope (hZ := hZ.left) hk₁.left hk₂.left hg₁.left hg₂.left
    hx₁ hy₁ hx₂ hy₂ hne' hneK
  have haddX : EvalsTo hZ.left
      ((curveK W).addX x₁ x₂ ((curveK W).slope x₁ x₂ y₁ y₂))
      (W.addX u₁ u₂ (W.slope u₁ u₂ v₁ v₂)) := by
    simp only [WeierstrassCurve.Affine.addX, curveK_a₁, curveK_a₂]
    exact ((((hslope.pow 2).add ((evalsTo_constHom hZ.left W.a₁).mul hslope)).sub
      (evalsTo_constHom hZ.left W.a₂)).sub hx₁).sub hx₂
  have hnegAddY : EvalsTo hZ.left
      ((curveK W).negAddY x₁ x₂ y₁ ((curveK W).slope x₁ x₂ y₁ y₂))
      (W.negAddY u₁ u₂ v₁ (W.slope u₁ u₂ v₁ v₂)) := by
    simp only [WeierstrassCurve.Affine.negAddY]
    exact (hslope.mul (haddX.sub hx₁)).add hy₁
  rw [WeierstrassCurve.Affine.Point.add_some hneK,
    WeierstrassCurve.Affine.Point.add_some hne']
  refine Or.inr ⟨_, _, _, _, _, _, rfl, rfl, haddX, ?_⟩
  simp only [WeierstrassCurve.Affine.addY]
  exact evalsTo_negY haddX hnegAddY

end SpecPointSection

omit [DecidableEq F] in
/-- **`W(F)` has a point outside any pair** (PROVEN): `F` is
algebraically closed hence infinite, every abscissa carries a point
(`exists_equation`, nonsingular since `Δ ≠ 0`), and distinct abscissae
give distinct points — so `W.Point` is infinite and cannot be exhausted
by two elements.  This is what lets the reduction induction below choose
a splitting `Q = Q' ⊕ R` avoiding both degenerate configurations. -/
theorem exists_point_ne_pair (hΔ : W.Δ ≠ 0) (a b : W.Point) :
    ∃ R : W.Point, R ≠ a ∧ R ≠ b := by
  classical
  have hpt : ∀ x₀ : F, ∃ v : F, W.Nonsingular x₀ v := by
    intro x₀
    obtain ⟨v, hv⟩ := exists_equation W x₀
    exact ⟨v, (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hv⟩
  choose vv hvv using hpt
  by_contra hcon
  have hsub : ∀ R : W.Point, R = a ∨ R = b := by
    intro R
    by_cases h : R = a
    · exact Or.inl h
    · by_cases h2 : R = b
      · exact Or.inr h2
      · exact absurd ⟨R, h, h2⟩ hcon
  have hinj : Function.Injective
      (fun x₀ : F =>
        (WeierstrassCurve.Affine.Point.some x₀ (vv x₀) (hvv x₀) : W.Point)) := by
    intro s t hst
    have hst' := hst
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hst'
    exact hst'.1
  have hs : (Set.univ : Set W.Point) ⊆ {a, b} := fun R _ => hsub R
  haveI : Finite W.Point :=
    Set.finite_univ_iff.mp (Set.Finite.subset ((Set.finite_singleton b).insert a) hs)
  haveI : Finite F := Finite.of_injective _ hinj
  exact not_finite F

/-- **Reduction of `Q ⊕ k•taut`, for a natural `k`** (PROVEN, by
induction on `k`).

The step is where the kernel of reduction is dodged.  Naively
`Q ⊕ (k+1)•taut = (Q ⊕ k•taut) ⊕ taut` needs `Q ⊕ k•Z ≠ O`, which can
fail at intermediate `k` even when the final `Q ⊕ (k+1)•Z` is affine (it
fails exactly when `k•Z = ⊖Q`).  Instead the constant is SPLIT,
`Q = Q' ⊕ R`, and `Q'` is chosen by `exists_point_ne_pair` to avoid the
only two bad values `⊖(k•Z)` and `Q ⊕ Z`; then `Q' ⊕ k•Z` and `R ⊕ Z` are
both affine, both reduce by the induction hypothesis and the one-step
case, and `SpecPoint.add` assembles them. -/
theorem specPoint_natCast_zsmul (hΔ : W.Δ ≠ 0) {xZ yZ : F}
    (hZ : W.Nonsingular xZ yZ) :
    ∀ (k : ℕ) (Q : W.Point),
      Q + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 →
      SpecPoint hZ (constPoint W Q + (k : ℤ) • tautPoint W hΔ)
        (Q + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) := by
  have hcp : ∀ A B : W.Point, constPoint W (A + B) = constPoint W A + constPoint W B :=
    fun A B => map_add (constPointHom W) A B
  have hstep : ∀ Q : W.Point,
      Q + (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 →
      SpecPoint hZ (constPoint W Q + (1 : ℤ) • tautPoint W hΔ)
        (Q + (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) := by
    intro Q hQ
    rw [one_zsmul]
    exact (specPoint_constPoint hZ Q).add (specPoint_tautPoint hΔ hZ) hQ
  intro k
  induction k with
  | zero =>
    intro Q _
    rw [Nat.cast_zero, zero_zsmul, add_zero, zero_zsmul, add_zero]
    exact specPoint_constPoint hZ Q
  | succ k ih =>
    intro Q hQ
    obtain ⟨Q', hQ'1, hQ'2⟩ := exists_point_ne_pair hΔ
      (-((k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)))
      (Q + (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point))
    obtain ⟨R, rfl⟩ : ∃ R : W.Point, Q = Q' + R := ⟨Q - Q', by abel⟩
    have hA : Q' + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 :=
      fun hc => hQ'1 (by rwa [add_eq_zero_iff_eq_neg] at hc)
    have hB : R + (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 := by
      intro hc
      refine hQ'2 ?_
      rw [add_assoc, hc, add_zero]
    have hω : (constPoint W Q' + (k : ℤ) • tautPoint W hΔ) +
        (constPoint W R + (1 : ℤ) • tautPoint W hΔ) =
        constPoint W (Q' + R) + ((k : ℤ) + 1) • tautPoint W hΔ := by
      rw [hcp, add_zsmul, one_zsmul]; abel
    have hP : (Q' + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) +
        (R + (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) =
        (Q' + R) + ((k : ℤ) + 1) •
          (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [add_zsmul, one_zsmul]; abel
    rw [Nat.cast_add, Nat.cast_one] at hQ ⊢
    rw [← hω, ← hP]
    exact (ih Q' hA).add (hstep R hB) (by rw [hP]; exact hQ)

/-- **Reduction of `Q ⊕ m•taut` for an arbitrary integer `m`** (PROVEN):
the natural-number case together with `SpecPoint.neg`. -/
theorem specPoint_zsmul (hΔ : W.Δ ≠ 0) {xZ yZ : F} (hZ : W.Nonsingular xZ yZ)
    (m : ℤ) (Q : W.Point)
    (hQ : Q + m • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0) :
    SpecPoint hZ (constPoint W Q + m • tautPoint W hΔ)
      (Q + m • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) := by
  obtain ⟨k, hk | hk⟩ : ∃ k : ℕ, m = (k : ℤ) ∨ m = -(k : ℤ) :=
    ⟨m.natAbs, by rcases Int.natAbs_eq m with h | h; exacts [Or.inl h, Or.inr h]⟩
  · subst hk; exact specPoint_natCast_zsmul hΔ hZ k Q hQ
  · subst hk
    have hcpneg : ∀ A : W.Point, constPoint W (-A) = -constPoint W A :=
      fun A => map_neg (constPointHom W) A
    have hQ' : (-Q) + (k : ℤ) •
        (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 := by
      intro hc
      refine hQ ?_
      have he : Q + (-(k : ℤ)) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) =
          -((-Q) + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) := by
        rw [neg_zsmul]; abel
      rw [he, hc, neg_zero]
    have h := (specPoint_natCast_zsmul hΔ hZ k (-Q) hQ').neg
    have e1 : -(constPoint W (-Q) + (k : ℤ) • tautPoint W hΔ) =
        constPoint W Q + (-(k : ℤ)) • tautPoint W hΔ := by
      rw [hcpneg, neg_zsmul]; abel
    have e2 : -((-Q) + (k : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point)) =
        Q + (-(k : ℤ)) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [neg_zsmul]; abel
    rwa [e1, e2] at h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Every coordinate-ring element pulled back to `ω` is regular at `Z`
with the expected value** (PROVEN): the set of `z` for which
`pointEval (constHom W) hω z` is regular at `Z` with value `z(Z')` is
closed under sums and products and contains the three generators
(constants, `X`, `Y`) of the coordinate ring, so it is everything.  The
induction mirrors `coordinateRing_ringHom_ext`. -/
theorem evalsTo_pointEval {xZ yZ : F} (hZ : W.Equation xZ yZ)
    {xω yω : W.FunctionField} (hω : (curveK W).Equation xω yω)
    {xZ' yZ' : F} (hZ' : W.Equation xZ' yZ')
    (hx : EvalsTo hZ xω xZ') (hy : EvalsTo hZ yω yZ') (z : W.CoordinateRing) :
    EvalsTo hZ (pointEval (constHom W) hω z) (AdjoinRoot.evalEval hZ' z) := by
  have hXgen : EvalsTo hZ
      (pointEval (constHom W) hω (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
      (AdjoinRoot.evalEval hZ' (CoordinateRing.mk W (Polynomial.C Polynomial.X))) := by
    rw [pointEval_X, show AdjoinRoot.evalEval hZ' (CoordinateRing.mk W
      (Polynomial.C Polynomial.X)) = xZ' from evalEval_coordX hZ']
    exact hx
  have hYgen : EvalsTo hZ
      (pointEval (constHom W) hω (CoordinateRing.mk W Polynomial.X))
      (AdjoinRoot.evalEval hZ' (CoordinateRing.mk W Polynomial.X)) := by
    rw [pointEval_Y, show AdjoinRoot.evalEval hZ' (CoordinateRing.mk W Polynomial.X) = yZ'
      from evalEval_coordY hZ']
    exact hy
  have hCgen : ∀ d : F, EvalsTo hZ
      (pointEval (constHom W) hω (CoordinateRing.mk W (Polynomial.C (Polynomial.C d))))
      (AdjoinRoot.evalEval hZ'
        (CoordinateRing.mk W (Polynomial.C (Polynomial.C d)))) := by
    intro d
    rw [pointEval_C, show AdjoinRoot.evalEval hZ' (CoordinateRing.mk W
      (Polynomial.C (Polynomial.C d))) = d from evalEval_coordC hZ' d]
    exact evalsTo_constHom hZ d
  have hpoly : ∀ r : Polynomial F, EvalsTo hZ
      (pointEval (constHom W) hω (CoordinateRing.mk W (Polynomial.C r)))
      (AdjoinRoot.evalEval hZ' (CoordinateRing.mk W (Polynomial.C r))) := by
    intro r
    induction r using Polynomial.induction_on with
    | C d => exact hCgen d
    | add f g hf hg =>
      simp only [map_add]
      exact hf.add hg
    | monomial n d _ =>
      simp only [map_mul, map_pow]
      exact (hCgen d).mul (hXgen.pow _)
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on with
  | C r => exact hpoly r
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | monomial n r _ =>
    simp only [map_mul, map_pow]
    exact (hpoly r).mul (hYgen.pow _)

/-- **Stage B substrate leaf (PROVEN): specialization of a generic
evaluation at an affine point.**  This is the primitive the whole
`WeilPairingDescent.lean` substrate is missing, and the only reason
Stage B's two evaluation leaves cannot be finished from it: that
substrate states every divisor/character identity in the FUNCTION FIELD
`K = Frac F[W]` — identities between `pointEval`s at the generic point
`taut` — while Stage B's conclusions are VALUES at named affine points
(`AdjoinRoot.evalEval`).  Nothing in the substrate lets a `K`-identity
be read at a point, because there is no ring map `K → F`: specialization
is only partially defined.

Statement.  Let `ω = Q ⊕ m•taut` be an affine point of the base-changed
curve `curveK W` — so that `pointEval (constHom W) hω.left` realizes
`z ↦ z ∘ (τ_Q ∘ [m])` — and let `Z` be an affine point of `W` whose
image `Z' = Q ⊕ m•Z` under the SAME map is again affine.  Then for every
`z ∈ F[W]` the composite `z ∘ (τ_Q ∘ [m])` is regular at `Z` with value
`z(Z')`.  Stated without a partial specialization map: it is a fraction
`n/d` of coordinate-ring elements whose denominator does not vanish at
`Z` (`d(Z) ≠ 0`, the regularity), and whose numerator satisfies
`n(Z) = z(Z')·d(Z)` (the value).

Faithfulness.  `τ_Q ∘ [m] : E → E` is a morphism of curves; `z` is
regular on `E ∖ {O}`; so `z ∘ (τ_Q ∘ [m])` is regular at every `Z` whose
image is affine, which is exactly the hypothesis `hZ'c`.  The
degenerate cases are covered: `m = 0` makes `ω` the constant point `Q`
and both sides the constant `z(Q)`; `Q = O`, `m = 1` makes the map the
identity and the statement `n = z`, `d = 1`.

Proof (PROVEN 2026-07-25; the machinery is the `EvalsTo`/`SpecPoint`
block above).  The recorded route through the division polynomials
`x(m•taut) = Φ_m/ΨSq_m` was NOT taken, because mathlib has division
polynomials (`WeierstrassCurve.Φ`, `ΨSq`) but no theorem connecting them
to `m • P` on `Point` — that link is missing machinery of its own.
Instead:

1. `pointEval` is determined by where it sends the coordinate atoms, so
   the whole statement follows (`evalsTo_pointEval`, an induction
   mirroring `coordinateRing_ringHom_ext`) from the two atomic cases —
   i.e. from "`xω`, `yω` are regular at `Z` with values `xZ'`, `yZ'`".
   The conclusion's `∃ n d` shape is packaged as the relation `EvalsTo`,
   which is closed under `+`, `*`, `−`, `/` and has a unique value.
2. That is exactly "the reduction of `ω = Q ⊕ m•taut` at `Z` is `Z'`",
   i.e. Silverman *AEC* VII.2.1 for the local ring at `Z` — a genuine
   piece of missing theory, since mathlib's `EllipticCurve/Reduction.lean`
   reduces CURVES and never touches points.  It is proven here as
   `specPoint_zsmul`, by induction on `m`, using only the part of the
   reduction homomorphism that avoids its kernel: `SpecPoint.add` needs
   the reduced sum to be AFFINE, and the induction arranges that by
   splitting the constant `Q = Q' ⊕ R` with `Q'` dodging the two bad
   values (possible since `W(F)` is infinite).  So the formal group,
   which mathlib does not have, is never needed.
3. The only real computation is that the slope specializes
   (`evalsTo_slope`): when the two points collide after reduction the
   secant slope `(y₁−y₂)/(x₁−x₂)` degenerates `0/0`, and its value is
   recovered from the cleared relation `(y₁−y₂)·A = (x₁−x₂)·B` obtained
   by subtracting the two Weierstrass equations, whose reductions are the
   denominator and numerator of the tangent slope downstairs.  `A`'s
   reduction is nonzero precisely because the reduced sum is affine.

Non-vanishing of the denominators produced this way is exactly the
affineness of `Q ⊕ m•Z`, i.e. `hZ'c`, as the original route predicted.

Both Stage-B evaluation leaves below consume this at `(Q, m) = (0, p)`
(the `[p]`-pullback `z ↦ z∘[p]`, specializing at a `p`-division point)
and at `(Q, m) = (Q₀, 1)` (a translation `z ↦ z∘τ_{Q₀}`), which is why
it is stated once, uniformly in `(Q, m)`. -/
theorem exists_pointEval_specialization (hΔ : W.Δ ≠ 0) (m : ℤ) {Q : W.Point}
    {xω yω : W.FunctionField} {hω : (curveK W).Nonsingular xω yω}
    (hpt : constPoint W Q + m • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xω yω hω)
    {xZ yZ : F} (hZ : W.Nonsingular xZ yZ)
    {xZ' yZ' : F} (hZ' : W.Nonsingular xZ' yZ')
    (hZ'c : (WeierstrassCurve.Affine.Point.some xZ' yZ' hZ' : W.Point) =
      Q + m • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point))
    (z : W.CoordinateRing) :
    ∃ n d : W.CoordinateRing,
      AdjoinRoot.evalEval hZ.left d ≠ 0 ∧
      pointEval (constHom W) hω.left z *
          algebraMap W.CoordinateRing W.FunctionField d =
        algebraMap W.CoordinateRing W.FunctionField n ∧
      AdjoinRoot.evalEval hZ.left n =
        AdjoinRoot.evalEval hZ'.left z * AdjoinRoot.evalEval hZ.left d := by
  have hQne : Q + m • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) ≠ 0 := by
    rw [← hZ'c]
    exact WeierstrassCurve.Affine.Point.some_ne_zero hZ'
  have hspec := specPoint_zsmul hΔ hZ m Q hQne
  rw [hpt, ← hZ'c] at hspec
  rcases hspec with ⟨hz, -⟩ | ⟨x, y, hk, u, v, hg, hxeq, hueq, hxe, hye⟩
  · exact absurd hz (WeierstrassCurve.Affine.Point.some_ne_zero hω)
  · rw [WeierstrassCurve.Affine.Point.some.injEq] at hxeq hueq
    obtain ⟨rfl, rfl⟩ := hxeq
    obtain ⟨rfl, rfl⟩ := hueq
    exact evalsTo_pointEval hZ.left hω.left hZ'.left hxe hye z

omit [Fact (1 < p)] in
/-- **Stage B, leaf 1, in its characteristic-free form (PROVEN 2026-07-31): a
generic `p`-division offset, over FOUR point-inequations instead of a finite
subfield.**

This is the whole mathematical content of `exists_generic_pDivision_offset`
below, which is now a wrapper over it.

### Why the restatement, and what it costs (the genericity-layer audit)

The `μ_p`-valued Weil pairing of `WeilPairing.lean` is built over `𝔽̄_q`, and the
*recorded* obstruction to running the same construction over a characteristic-zero
algebraically closed base was that this leaf and
`exists_millerRatio_eval_translationChar` below both take
`{F₁ F₂ : Subfield F}` with `(F₁ : Set F).Finite`, `(F₂ : Set F).Finite` — and a
finite subfield containing the curve's coefficients exists only in characteristic
`p`.  That reading is **wrong**, and the compiler says so: in the wrapper below
both finiteness hypotheses are `_`-bound, i.e. the proof never looks at them.

Reading the proof rather than the signature, the entire subfield apparatus — the
coefficient memberships `ha₁…ha₆`, the subgroup `exists_pointSubgroup_of_subfield`
extracts from them, `hbad`, `hxQF₁`, `hyQF₁`, `hxSF₂`, `hySF₂`, `hxRF₂` — is used
for exactly one thing: the local `hkey : ∀ t ∈ G, S ⊖ R ≠ t`.  And `hkey` is
applied at exactly FOUR values of `t`, namely `O`, `Q`, `⊖P` and `Q ⊖ P`.  So the
subfield is an **avoidance device**: "pick `R` outside a small bad set",
implemented in characteristic `p` by enumerating a large enough finite field.
Nothing else about it is used, and `G` being a subgroup buys nothing beyond
closure at those four points.

Consequently the hypothesis this leaf really needs is

    S ⊖ R ∉ {O, Q, ⊖P, Q ⊖ P},

four inequations in `W.Point`, with no field theory and no characteristic
anywhere.  **Characteristic zero is therefore EASIER here, not harder**: over an
algebraically closed base of characteristic zero `W.Point` is infinite, so the
avoidance is direct — choose `R` off four translates of `S` — whereas in
characteristic `p` it had to be manufactured out of `exists_finite_subfield_containing`.

The twelve subfield hypotheses of the wrapper collapse to these four, and the
`p`-torsion hypothesis `hPtor`, the injectivity/surjectivity/cardinality of `val`
and `a ≠ 0` drop out entirely (they were never used either).

### Proof

Unchanged from the wrapper's former body.  `p`-division points `S'`, `R'`, `P'`
exist by `exists_zsmul_eq` (`(p : F) ≠ 0`, `F` algebraically closed).  `evalEval`
at an affine point `ξ` kills `a` exactly when `ξ` lies in the divisor support
`{T'⊕κ} ∪ {⊖κ}` and kills `v = ∏_κ (X − x_κ)` exactly when `ξ = ±κ`
(`mem_of_evalEval_eq_zero` against `hspan` and `span_enumVertical`); every point of
either support is killed by `[p]` or sent to `Q` by it, so a bad `U := S' ⊖ R'`
forces `S ⊖ R ∈ {O, Q}` and a bad `V := P' ⊕ U` forces `S ⊖ R ∈ {⊖P, Q ⊖ P}` — and
the same four values are what `U = O`, `V = O` force.  Those are precisely the four
excluded configurations. -/
theorem exists_generic_pDivision_offset_of_avoid {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    {P T' : W.Point} {xQ yQ : F} (hQ : W.Nonsingular xQ yQ)
    (hT : (p : ℤ) • T' = WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    {a : W.CoordinateRing}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {xS yS : F} (hS : W.Nonsingular xS yS)
    {xR yR : F} (hR : W.Nonsingular xR yR)
    (hne0 : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
      WeierstrassCurve.Affine.Point.some xR yR hR ≠ 0)
    (hneQ : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
      WeierstrassCurve.Affine.Point.some xR yR hR ≠
        WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    (hneP : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
      WeierstrassCurve.Affine.Point.some xR yR hR ≠ -P)
    (hneQP : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
      WeierstrassCurve.Affine.Point.some xR yR hR ≠
        (WeierstrassCurve.Affine.Point.some xQ yQ hQ : W.Point) - P) :
    ∃ S' R' P' : W.Point,
      (p : ℤ) • S' = WeierstrassCurve.Affine.Point.some xS yS hS ∧
      (p : ℤ) • R' = WeierstrassCurve.Affine.Point.some xR yR hR ∧
      (p : ℤ) • P' = P ∧
      ∃ (xU yU : F) (hU : W.Nonsingular xU yU) (xV yV : F)
        (hV : W.Nonsingular xV yV),
        WeierstrassCurve.Affine.Point.some xU yU hU = S' - R' ∧
        WeierstrassCurve.Affine.Point.some xV yV hV = P' + (S' - R') ∧
        AdjoinRoot.evalEval hU.left a ≠ 0 ∧
        AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0 ∧
        AdjoinRoot.evalEval hV.left a ≠ 0 ∧
        AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0 := by
  classical
  set Sp : W.Point := WeierstrassCurve.Affine.Point.some xS yS hS with hSpdef
  set Rp : W.Point := WeierstrassCurve.Affine.Point.some xR yR hR with hRpdef
  set Qp : W.Point := WeierstrassCurve.Affine.Point.some xQ yQ hQ with hQpdef
  obtain ⟨S', hS'⟩ := exists_zsmul_eq hΔ hp Sp
  obtain ⟨R', hR'⟩ := exists_zsmul_eq hΔ hp Rp
  obtain ⟨P', hP'⟩ := exists_zsmul_eq hΔ hp P
  have hpU : (p : ℤ) • (S' - R') = Sp - Rp := by rw [smul_sub, hS', hR']
  have hpV : (p : ℤ) • (P' + (S' - R')) = P + (Sp - Rp) := by
    rw [smul_add, hP', hpU]
  -- vanishing of either factor at an affine point forces `[p]ξ ∈ {O, Q}`
  have hbadZ : ∀ (x y : F) (h : W.Nonsingular x y),
      AdjoinRoot.evalEval h.left a = 0 ∨
        AdjoinRoot.evalEval h.left (enumVertical W val) = 0 →
      (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = 0 ∨
        (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = Qp := by
    intro x y h hcase
    rcases hcase with hz | hz
    · have hmem := mem_of_evalEval_eq_zero hspan h hz
      rw [Multiset.mem_add] at hmem
      rcases hmem with hm | hm
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        exact Or.inr (by rw [← hi, smul_add, hT, hval_tor i, add_zero])
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        exact Or.inl (by rw [← hi, smul_neg, hval_tor i, neg_zero])
    · have hmem := mem_of_evalEval_eq_zero (span_enumVertical val) h hz
      rw [Multiset.mem_add] at hmem
      refine Or.inl ?_
      rcases hmem with hm | hm
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        rw [← hi]
        exact hval_tor i
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        rw [← hi, smul_neg, hval_tor i, neg_zero]
  -- `U = S' ⊖ R'` is affine
  obtain ⟨xU, yU, hU, hUeq⟩ : ∃ (xU yU : F) (hU : W.Nonsingular xU yU),
      (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) = S' - R' := by
    cases hc : (S' - R' : W.Point) with
    | zero =>
      refine absurd ?_ hne0
      rw [← hpU, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- `V = P' ⊕ U` is affine
  obtain ⟨xV, yV, hV, hVeq⟩ : ∃ (xV yV : F) (hV : W.Nonsingular xV yV),
      (WeierstrassCurve.Affine.Point.some xV yV hV : W.Point) =
        P' + (S' - R') := by
    cases hc : (P' + (S' - R') : W.Point) with
    | zero =>
      have h1 : P + (Sp - Rp) = 0 := by
        rw [← hpV, hc]
        exact smul_zero _
      refine absurd ?_ hneP
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    | some x y h => exact ⟨x, y, h, rfl⟩
  refine ⟨S', R', P', hS', hR', hP', xU, yU, hU, xV, yV, hV, hUeq, hVeq,
    ?_, ?_, ?_, ?_⟩
  · intro h0
    rcases hbadZ xU yU hU (Or.inl h0) with hz | hz
    · exact hne0 (by rw [← hpU, ← hUeq, hz])
    · exact hneQ (by rw [← hpU, ← hUeq, hz])
  · intro h0
    rcases hbadZ xU yU hU (Or.inr h0) with hz | hz
    · exact hne0 (by rw [← hpU, ← hUeq, hz])
    · exact hneQ (by rw [← hpU, ← hUeq, hz])
  · intro h0
    rcases hbadZ xV yV hV (Or.inl h0) with hz | hz
    · refine hneP ?_
      have h1 : P + (Sp - Rp) = 0 := by rw [← hpV, ← hVeq, hz]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    · refine hneQP ?_
      have h1 : P + (Sp - Rp) = Qp := by rw [← hpV, ← hVeq, hz]
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1
  · intro h0
    rcases hbadZ xV yV hV (Or.inr h0) with hz | hz
    · refine hneP ?_
      have h1 : P + (Sp - Rp) = 0 := by rw [← hpV, ← hVeq, hz]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    · refine hneQP ?_
      have h1 : P + (Sp - Rp) = Qp := by rw [← hpV, ← hVeq, hz]
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1

omit [Fact (1 < p)] in
/-- **Stage B, leaf 1 (PROVEN): a generic `p`-division offset.**
Given the Miller data (`Q = p•T'`, `a` generating
`∏_κ I_{T'⊕κ}·I_{⊖κ}`), a `p`-torsion point `P`, and the setup's
`S` (abscissa and ordinate in the big field `F₂`) and `R` (abscissa
NOT in `F₂`), there are `p`-division points `S'`, `R'`, `P'` of
`S`, `R`, `P` for which the offset `U := S' ⊖ R'` and its
`P'`-translate `V := P' ⊕ U` are affine points at which neither the
Miller generator `a` nor the vertical product
`v = ∏_κ (X − x_κ)` vanishes — i.e. `g = a/v` is defined and nonzero
at both, as the two evaluation stages require.

Proof (the recorded route, with the two hypotheses it turned out to
need — see below).  `p`-division points exist by
`TorsionCard.smul_surjective` (`exists_zsmul_eq`; `(p : F) ≠ 0`, `F`
algebraically closed).  `evalEval` at an affine point `ξ` kills `a`
exactly when `ξ` lies in the divisor support `{T'⊕κ} ∪ {⊖κ}` and kills
`v` exactly when `ξ = ±κ` for some `κ ∈ E[p]`
(`mem_of_evalEval_eq_zero` applied to `hspan` and to
`span_enumVertical`).  Every point of either support is killed by `[p]`
or sent to `Q` by it, so a bad `U` forces `S ⊖ R ∈ {O, Q}` and a bad
`V` forces `S ⊖ R ∈ {⊖P, Q ⊖ P}` — and the same four values are what
`U = O`, `V = O` force.  All four are excluded at once: `Q`, `P` and
`S` are `F₂`-rational (`P` by `hbad` with `κ = ⊖P`, `λ = O`; `Q` by
`hxQF₁`/`hyQF₁`), the `F₂`-rational points form a SUBGROUP
(`exists_pointSubgroup_of_subfield` — this is where the curve's
coefficients must lie in the subfield), so `S ⊖ R = t` with `t` in that
subgroup would put `R = S ⊖ t` in it, i.e. `xR ∈ F₂`, contradicting
`hxRF₂`.

Two hypotheses beyond the original statement are needed and are
supplied by the Stage-B caller: the curve's coefficients lie in `F₁`
(`ha₁`…`ha₆` — without them "the addition formulas stay in the
subfield" is false, since `W` need not be defined over `F₁`), and `Q`'s
coordinates lie in `F₁` (`hxQF₁`, `hyQF₁` — without them the
configuration `S ⊖ R = Q` is not excluded and the statement is FALSE,
every `U` then lying in `[p]^{-1}(Q)`, which is exactly the support of
`a`).  `hbad` does not give either: it constrains the `p²`-torsion
translates of `T'`, not `p•T' = Q`, and says nothing about the
coefficients.

**GENERICITY-LAYER AUDIT (2026-07-31).**  Everything in the paragraph
above is a way of PRODUCING four point-inequations, and nothing else.
The statement is now a thin wrapper over
`exists_generic_pDivision_offset_of_avoid` below, which carries the whole
proof and asks only for those four; see its docstring for why that matters
(it is what makes the Stage-B genericity layer characteristic-free). -/
theorem exists_generic_pDivision_offset {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (_hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (_hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (_hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} {xQ yQ : F} (hQ : W.Nonsingular xQ yQ)
    (hT : (p : ℤ) • T' = WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    (hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (_ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {F₁ F₂ : Subfield F} (_hF₁fin : (F₁ : Set F).Finite)
    (_hF₂fin : (F₂ : Set F).Finite) (hF₁₂ : F₁ ≤ F₂)
    (ha₁ : W.a₁ ∈ F₁) (ha₂ : W.a₂ ∈ F₁) (ha₃ : W.a₃ ∈ F₁)
    (ha₄ : W.a₄ ∈ F₁) (ha₆ : W.a₆ ∈ F₁)
    (hbad : ∀ κ lam : W.Point, (p : ℤ) • κ = 0 → ((p ^ 2 : ℕ) : ℤ) • lam = 0 →
      ∀ (x y : F) (h : W.Nonsingular x y),
        WeierstrassCurve.Affine.Point.some x y h = T' + κ + lam ∨
          WeierstrassCurve.Affine.Point.some x y h = -κ + lam →
        x ∈ F₁ ∧ y ∈ F₁)
    (hxQF₁ : xQ ∈ F₁) (hyQF₁ : yQ ∈ F₁)
    {xS yS : F} (hS : W.Nonsingular xS yS) (hxSF₂ : xS ∈ F₂) (hySF₂ : yS ∈ F₂)
    {xR yR : F} (hR : W.Nonsingular xR yR) (hxRF₂ : xR ∉ F₂) :
    ∃ S' R' P' : W.Point,
      (p : ℤ) • S' = WeierstrassCurve.Affine.Point.some xS yS hS ∧
      (p : ℤ) • R' = WeierstrassCurve.Affine.Point.some xR yR hR ∧
      (p : ℤ) • P' = P ∧
      ∃ (xU yU : F) (hU : W.Nonsingular xU yU) (xV yV : F)
        (hV : W.Nonsingular xV yV),
        WeierstrassCurve.Affine.Point.some xU yU hU = S' - R' ∧
        WeierstrassCurve.Affine.Point.some xV yV hV = P' + (S' - R') ∧
        AdjoinRoot.evalEval hU.left a ≠ 0 ∧
        AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0 ∧
        AdjoinRoot.evalEval hV.left a ≠ 0 ∧
        AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0 := by
  classical
  obtain ⟨G, hGin, hGout⟩ := exists_pointSubgroup_of_subfield (W := W)
    (hF₁₂ ha₁) (hF₁₂ ha₂) (hF₁₂ ha₃) (hF₁₂ ha₄) (hF₁₂ ha₆)
  have hSG : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) ∈ G :=
    hGin xS yS hS hxSF₂ hySF₂
  have hQG : (WeierstrassCurve.Affine.Point.some xQ yQ hQ : W.Point) ∈ G :=
    hGin xQ yQ hQ (hF₁₂ hxQF₁) (hF₁₂ hyQF₁)
  have hPG : P ∈ G := by
    cases hPc : P with
    | zero => exact zero_mem G
    | some x y h =>
      obtain ⟨hx, hy⟩ := hbad (-P) 0 (by rw [smul_neg, hPtor, neg_zero])
        (by rw [smul_zero]) x y h
        (Or.inr (by rw [neg_neg, add_zero]; exact hPc.symm))
      exact hGin x y h (hF₁₂ hx) (hF₁₂ hy)
  -- the contradiction engine: `S ⊖ R` cannot be `F₂`-rational
  have hkey : ∀ t : W.Point, t ∈ G →
      (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR ≠ t := by
    intro t ht hc
    have hRG : (WeierstrassCurve.Affine.Point.some xR yR hR : W.Point) ∈ G := by
      have hrw : (WeierstrassCurve.Affine.Point.some xR yR hR : W.Point) =
          (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) - t := by
        rw [← hc]; abel
      rw [hrw]
      exact sub_mem hSG ht
    exact hxRF₂ (hGout xR yR hR hRG).1
  exact exists_generic_pDivision_offset_of_avoid (val := val) hΔ hp hval_tor hQ hT
    hspan hS hR (hkey 0 (zero_mem G)) (hkey _ hQG) (hkey (-P) (neg_mem hPG))
    (hkey _ (sub_mem hQG hPG))

/-- **Stage B, leaf 2 (ONE sorried sub-leaf + proven glue): the
`[p]`-pullback evaluation of the `Q`-side Miller ratio.**  With `f_Q = aQ/(X − x_R)^p`
(`div f_Q = p(Q⊕R) − p(R)`, the span hypothesis `haQ`) and
`g = a/v` as above, the balanced evaluation of `f_Q` at
`D_P = (P⊕S) − (S)` is the `p`-th power of the `g`-ratio at the
offset pair `(U, V) = (S'⊖R', P'⊕S'⊖R')` of leaf 1:

`f_Q(P⊕S)/f_Q(S) = [g(V)/g(U)]^p`,

written out multiplicatively (no divisions) as the conclusion below.

Proof plan (HLEG-NOTES.md §4(B), stages L4-7/9).  The divisor of
`f_Q∘[p]` is `p·[p]^*((Q⊕R) − (R)) = p·Σ_κ ((T'⊕R'⊕κ) − (R'⊕κ))`,
which is `p` times the `⊖R'`-translate of `div g`; hence
`f_Q∘[p] = c'·(g∘τ_{⊖R'})^p` for a constant `c'` — the L4-7
multiplicity-one span comparison
(`span_eq_pointIdeal_mul_of_pullback` in WeilPairingDescent.lean is
the same comparison in its `[p]^*`-descent form; the pullback of a
vertical `X − x₀` is `Φ_p − x₀·Ψ_p²`, separable of degree `p²` since
`(p : F) ≠ 0`, with the `p²`-fiber as its multiplicity-one root
multiset — `hcard` enumerates the fibers — and lines pull back by the
`ω`-formula).  Now `p•(P'⊕S') = P⊕S` and `p•S' = S`, so evaluating
that identity at `P'⊕S'` and at `S'` and dividing, the unknown
constant `c'` cancels and the `τ_{⊖R'}`-shift turns the arguments into
`V = P'⊕S'⊖R'` and `U = S'⊖R'`:
`f_Q(P⊕S)/f_Q(S) = [g(V)/g(U)]^p`.  Both evaluations are legitimate:
leaf 1 places `U`, `V` off `div g`, and the setup's nonvanishing
hypotheses `hnzS`/`hnzPS` place `S`, `P⊕S` off `div f_Q`.

STAGING (2026-07-25, re-cut then closed): DECOMPOSED over TWO inputs,
both shallower than the leaf and one of them shared with leaf 3.  Only
the second is still open.

* the GENERIC identity, PROVEN inline (2026-07-25): the existence of the
  pullback constant `c'` with `f_Q∘[p] = c'·(g∘τ_{⊖R'})^p` **in the
  function field `K`**, multiplied out as
  `[p]^*(aQ)·τ_{⊖R'}^*(v)^p = c'·τ_{⊖R'}^*(a)^p·[p]^*(X − x_R)^p`.
  This is the L4-7 multiplicity-one span comparison and nothing else,
  and it never mentions a point.  It is proven by comparing the two
  sides' DIVISORS as fractional ideals and finding them equal, so the
  ratio is a unit of `F[W]` and hence a nonzero constant
  (`coordinateRing_isUnit_eq_const`).  The two divisors are computed by
  the two transport bricks of `WeilPairingDescent.lean`:
  `spanSingleton_pointEval_mul_fiberProd_pow` (the `[p]`-pullback of a
  divisor is the multiplicity-one sum of its `p²`-fibres) applied to
  `aQ` (divisor `p(Q⊕R) + p(⊖R)`) and to `X − x_R` (divisor
  `(R) + (⊖R)`), and `spanSingleton_pointEval_translate` (the `τ_Q^*`
  of a divisor is its `⊖Q`-translate) applied to `v = ∏(X − x_κ)` and
  to `a`.  Since `p•(T'⊕R') = Q⊕R` and `p•R' = R`, the `[p]`-fibres of
  `Q⊕R` and `R` are exactly the `R'`-translates of the `T'⊕κ` and `κ`
  heads of `div a` and `div v`; the `⊖κ` tails are common to both sides
  and cancel, as do the unit factors `J_O^{2p}` and `I'_{R'}^{2p³}`.
  Nonvanishing of the two `[p]`-pullbacks comes from injectivity of
  evaluation at `p•taut` (`pointEval_injective_of_forall_ne_constHom`
  over `smul_taut_xCoord_ne_constHom`).
* the SPECIALIZATION brick `exists_pointEval_specialization` above,
  applied eight times: at the two `p`-division points `S'` and `P'⊕S'`,
  for each of the four functions `[p]^*(aQ)`, `[p]^*(X − x_R)`,
  `τ_{⊖R'}^*(v)`, `τ_{⊖R'}^*(a)`.

Everything between them is PROVEN glue: `S'` and `P'⊕S'` are affine
(their `[p]`-images `S` and `P⊕S` are), their images under the two maps
are exactly `S`/`P⊕S` and `U`/`V` (the leaf-1 offsets), clearing the
eight denominators against the generic identity and cancelling them
after evaluation gives the two balanced halves, and the final
cross-multiplication cancels `c'`. -/
theorem millerRatio_eval_pow_of_pullback {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (hcard : Fintype.card ι = p ^ 2)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    {T' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {xP yP : F} (hP : W.Nonsingular xP yP)
    {xQ yQ : F} (hQ : W.Nonsingular xQ yQ)
    (hT : (p : ℤ) • T' = WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    (hPtor : (p : ℤ) • (WeierstrassCurve.Affine.Point.some xP yP hP) = 0)
    {xS yS : F} (hS : W.Nonsingular xS yS)
    {xR yR : F} (hR : W.Nonsingular xR yR)
    {xPS yPS : F} (hPS : W.Nonsingular xPS yPS)
    (hPSc : WeierstrassCurve.Affine.Point.some xPS yPS hPS =
      WeierstrassCurve.Affine.Point.some xP yP hP +
        WeierstrassCurve.Affine.Point.some xS yS hS)
    {xQR yQR : F} (hQR : W.Nonsingular xQR yQR)
    (hQRc : WeierstrassCurve.Affine.Point.some xQR yQR hQR =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
        WeierstrassCurve.Affine.Point.some xR yR hR)
    {aQ : W.CoordinateRing}
    (haQ : Ideal.span {aQ} =
      (CoordinateRing.XYIdeal W xQR (Polynomial.C yQR)) ^ p *
        (CoordinateRing.XYIdeal W xR (Polynomial.C (W.negY xR yR))) ^ p)
    (hnzS : AdjoinRoot.evalEval hS.left aQ ≠ 0)
    (hnzPS : AdjoinRoot.evalEval hPS.left aQ ≠ 0)
    {S' R' P' : W.Point}
    (hS'p : (p : ℤ) • S' = WeierstrassCurve.Affine.Point.some xS yS hS)
    (hR'p : (p : ℤ) • R' = WeierstrassCurve.Affine.Point.some xR yR hR)
    (hP'p : (p : ℤ) • P' = WeierstrassCurve.Affine.Point.some xP yP hP)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xV yV : F} (hV : W.Nonsingular xV yV)
    (hUeq : WeierstrassCurve.Affine.Point.some xU yU hU = S' - R')
    (hVeq : WeierstrassCurve.Affine.Point.some xV yV hV = P' + (S' - R'))
    (hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0)
    (hVa : AdjoinRoot.evalEval hV.left a ≠ 0)
    (hVv : AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0) :
    AdjoinRoot.evalEval hS.left ((CoordinateRing.XClass W xR) ^ p) *
        AdjoinRoot.evalEval hPS.left aQ *
        (AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval hV.left (enumVertical W val)) ^ p =
      AdjoinRoot.evalEval hS.left aQ *
        AdjoinRoot.evalEval hPS.left ((CoordinateRing.XClass W xR) ^ p) *
        (AdjoinRoot.evalEval hV.left a *
          AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ p := by
  classical
  -- ── the two generic points at which the substrate evaluates: the
  --    `[p]`-multiple `p•taut` (where `pointEval` realizes `z ↦ z∘[p]`)
  --    and the translate `(⊖R')⊕taut` (where it realizes `z ↦ z∘τ_{⊖R'}`)
  obtain ⟨xp, yp, hpn, hptaut, hxrel⟩ := exists_smul_tautPoint_eq (W := W) hΔ hp
  obtain ⟨xnr, ynr, hnr, hptnr⟩ := exists_translate_some (W := W) hΔ (-R')
  have hp0 : constPoint W (0 : W.Point) + (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn := by
    rw [show constPoint W (0 : W.Point) = 0 from rfl, zero_add]
    exact hptaut
  have hnr0 : constPoint W (-R') + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xnr ynr hnr := by
    rw [one_zsmul]
    exact hptnr
  -- ── THE ANALYTIC SUB-LEAF (PROVEN below), stated GENERICALLY — no point
  --    occurs in it: `f_Q∘[p] = c'·(g∘τ_{⊖R'})^p` in `K`, multiplied out.
  --    This is the L4-7 multiplicity-one span comparison:
  --    `div(f_Q∘[p]) = p·[p]^*((Q⊕R) − (R)) = p·τ_{⊖R'}(div g)`, so the
  --    ratio has trivial divisor and is a constant
  --    (`coordinateRing_isUnit_eq_const`).
  obtain ⟨c', hcore⟩ :
      ∃ c' : F,
        pointEval (constHom W) hpn.left aQ *
            pointEval (constHom W) hnr.left (enumVertical W val) ^ p =
          constHom W c' * pointEval (constHom W) hnr.left a ^ p *
            pointEval (constHom W) hpn.left (CoordinateRing.XClass W xR) ^ p := by
    -- `[p]^*` evaluation is injective (the `x`-coordinate of `p•taut` is
    -- transcendental over the constants), so nothing nonzero evaluates to `0`
    have hinjp : Function.Injective (pointEval (constHom W) hpn.left) :=
      pointEval_injective_of_forall_ne_constHom hpn
        (smul_taut_xCoord_ne_constHom hxrel)
    have haQ0 : aQ ≠ 0 := fun h0 => hnzS (by rw [h0, map_zero])
    have hX0 : CoordinateRing.XClass W xR ≠ 0 := CoordinateRing.XClass_ne_zero xR
    have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
    have hevaQ : pointEval (constHom W) hpn.left aQ ≠ 0 := fun h0 =>
      haQ0 (hinjp (by rw [h0, map_zero]))
    have hevX :
        pointEval (constHom W) hpn.left (CoordinateRing.XClass W xR) ≠ 0 :=
      fun h0 => hX0 (hinjp (by rw [h0, map_zero]))
    -- ── a section of `[p]` on points
    obtain ⟨sec, hsec⟩ :
        ∃ s : W.Point → W.Point, ∀ Z : W.Point, (p : ℤ) • s Z = Z := by
      choose s hs using exists_zsmul_eq (W := W) hΔ hp
      exact ⟨s, hs⟩
    -- ── the `[p]`-fiber product depends on its base point only through `[p]`
    have hfib : ∀ T₁ T₂ : W.Point, (p : ℤ) • T₁ = (p : ℤ) • T₂ →
        fiberProd W val T₁ = fiberProd W val T₂ := by
      intro T₁ T₂ h
      have hd : (p : ℤ) • (T₁ - T₂) = 0 := by rw [smul_sub, h, sub_self]
      have h1 : (Finset.univ.val.map fun i => (T₁ - T₂) + val i) =
          Finset.univ.val.map fun i => val i :=
        map_add_torsion_eq hval_inj hval_tor hval_surj hd
      have h2 := congrArg (Multiset.map (fun R : W.Point => T₂ + R)) h1
      simp only [Multiset.map_map, Function.comp_apply] at h2
      unfold fiberProd
      rw [show (Finset.univ.val.map fun i => T₁ + val i) =
        Finset.univ.val.map fun i => T₂ + (T₁ - T₂ + val i) from
          Multiset.map_congr rfl fun i _ => by abel, h2]
    -- ── the affine divisors `div aQ = p(Q⊕R) + p(⊖R)` and
    --    `div (X − x_R) = (R) + (⊖R)` feeding the pullback brick
    have hDaQ : Ideal.span {aQ} =
        ((Multiset.replicate p (WeierstrassCurve.Affine.Point.some xQR yQR hQR) +
          Multiset.replicate p
            (-(WeierstrassCurve.Affine.Point.some xR yR hR) : W.Point)).map
          (pointIdeal W)).prod := by
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.map_replicate, Multiset.prod_replicate, Multiset.prod_replicate,
        haQ, pointIdeal_some, WeierstrassCurve.Affine.Point.neg_some,
        pointIdeal_some]
    have hDaQ0 : (0 : W.Point) ∉
        Multiset.replicate p (WeierstrassCurve.Affine.Point.some xQR yQR hQR) +
          Multiset.replicate p
            (-(WeierstrassCurve.Affine.Point.some xR yR hR) : W.Point) := by
      intro h
      rcases Multiset.mem_add.mp h with h | h
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hQR
          (Multiset.eq_of_mem_replicate h).symm
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hR
          (neg_eq_zero.mp (Multiset.eq_of_mem_replicate h).symm)
    have hDX : Ideal.span {CoordinateRing.XClass W xR} =
        ((WeierstrassCurve.Affine.Point.some xR yR hR ::ₘ
          {(-(WeierstrassCurve.Affine.Point.some xR yR hR) : W.Point)}).map
          (pointIdeal W)).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton, pointIdeal_some,
        WeierstrassCurve.Affine.Point.neg_some, pointIdeal_some]
      calc Ideal.span {CoordinateRing.XClass W xR}
          = CoordinateRing.XIdeal W xR := rfl
        _ = CoordinateRing.XYIdeal W xR (Polynomial.C (W.negY xR yR)) *
            CoordinateRing.XYIdeal W xR (Polynomial.C yR) :=
          (CoordinateRing.XYIdeal_neg_mul hR).symm
        _ = CoordinateRing.XYIdeal W xR (Polynomial.C yR) *
            CoordinateRing.XYIdeal W xR (Polynomial.C (W.negY xR yR)) :=
          mul_comm _ _
    have hDX0 : (0 : W.Point) ∉ (WeierstrassCurve.Affine.Point.some xR yR hR ::ₘ
        {(-(WeierstrassCurve.Affine.Point.some xR yR hR) : W.Point)}) := by
      intro h
      rcases Multiset.mem_cons.mp h with h | h
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hR h.symm
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hR
          (neg_eq_zero.mp (Multiset.mem_singleton.mp h).symm)
    -- ── L4-7 multiplicity-one pullback: the divisors of `[p]^*aQ` and of
    --    `[p]^*(X − x_R)`, as fiber products over `E[p]`
    have hA := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
      hval_inj hval_tor hval_surj hcard hptaut hsec haQ0 hevaQ hDaQ0 hDaQ
    have hB := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
      hval_inj hval_tor hval_surj hcard hptaut hsec hX0 hevX hDX0 hDX
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate, Multiset.card_add, Multiset.card_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton, Multiset.card_cons, Multiset.card_singleton]
      at hA hB
    -- `p•(T'⊕R') = Q⊕R` and `p•R' = R`, so the two fibers are the ones the
    -- `⊖R'`-translated `div g` will produce
    rw [hfib (sec (WeierstrassCurve.Affine.Point.some xQR yQR hQR)) (T' + R')
        (by rw [hsec, smul_add, hT, hR'p]; exact hQRc)] at hA
    rw [hfib (sec (WeierstrassCurve.Affine.Point.some xR yR hR)) R'
        (by rw [hsec, hR'p])] at hB
    -- ── L4-8 translation transport: the divisors of `τ_{⊖R'}^*(v)` and
    --    `τ_{⊖R'}^*(a)`, i.e. the `R'`-translates of `div v` and `div a`
    have hC := spanSingleton_pointEval_translate (W := W) hΔ hptnr hv0
      (span_enumVertical (W := W) val)
    have hD := spanSingleton_pointEval_translate (W := W) hΔ hptnr ha hspan
    rw [neg_neg] at hC hD
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.card_add,
      Multiset.card_map, Multiset.map_map, Function.comp_apply] at hC hD
    -- the `T'⊕κ` and `κ` heads of those translates are exactly the fibers
    -- of `Q⊕R` and of `R`; the `⊖κ` tails are common to both and cancel
    have hfibR' : fiberProd W val R' =
        (Finset.univ.val.map fun i =>
          (pointIdeal' W (val i - -R') :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
      unfold fiberProd
      rw [Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
      show (pointIdeal' W (R' + val i) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        (pointIdeal' W (val i - -R') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
      rw [show R' + val i = val i - -R' from by abel]
    have hfibTR' : fiberProd W val (T' + R') =
        (Finset.univ.val.map fun i =>
          (pointIdeal' W (T' + val i - -R') :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
      unfold fiberProd
      rw [Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
      show (pointIdeal' W (T' + R' + val i) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        (pointIdeal' W (T' + val i - -R') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
      rw [show T' + R' + val i = T' + val i - -R' from by abel]
    rw [← hfibR'] at hC
    rw [← hfibTR'] at hD
    rw [show (Finset.univ : Finset ι).val.card = Fintype.card ι from rfl] at hC hD
    -- ── the two sides have the SAME divisor: cancelling the unit factors
    --    `J_O^{2p}` and `I'_{R'}^{2p³}` leaves an equality of principal
    --    fractional ideals, hence a nonzero constant ratio `c'`
    have hu : IsUnit ((fiberProd W val (sec 0)) ^ (p + p) *
        ((pointIdeal' W R' :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
            (Fintype.card ι + Fintype.card ι)) ^ p) :=
      ((isUnit_prod_coe_pointIdeal' _).pow _).mul
        (((pointIdeal' W R').isUnit.pow _).pow _)
    have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hnr.left a ^ p *
            pointEval (constHom W) hpn.left (CoordinateRing.XClass W xR) ^ p) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left aQ *
            pointEval (constHom W) hnr.left (enumVertical W val) ^ p) := by
      simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.spanSingleton_pow]
      refine hu.mul_right_cancel ?_
      calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hnr.left a) ^ p *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hpn.left (CoordinateRing.XClass W xR)) ^ p *
            ((fiberProd W val (sec 0)) ^ (p + p) *
              ((pointIdeal' W R' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                  (Fintype.card ι + Fintype.card ι)) ^ p)
          = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hnr.left a) *
              (pointIdeal' W R' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                (Fintype.card ι + Fintype.card ι)) ^ p *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left (CoordinateRing.XClass W xR)) *
              (fiberProd W val (sec 0)) ^ (1 + 1)) ^ p := by ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left aQ) *
              (fiberProd W val (sec 0)) ^ (p + p) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hnr.left (enumVertical W val)) *
              (pointIdeal' W R' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                (Fintype.card ι + Fintype.card ι)) ^ p := by
            rw [hD, ← hB, ← hA, hC]
            ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hpn.left aQ) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hnr.left (enumVertical W val)) ^ p *
            ((fiberProd W val (sec 0)) ^ (p + p) *
              ((pointIdeal' W R' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                  (Fintype.card ι + Fintype.card ι)) ^ p) := by ring
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
    obtain ⟨c, -, hcz⟩ := coordinateRing_isUnit_eq_const z.isUnit
    refine ⟨c, ?_⟩
    rw [← hz, Units.smul_def, hcz, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C c))) =
        constHom W c from rfl]
    ring
  -- ── PROVEN glue 1: reading the generic identity at a `p`-division
  --    point `Z`, whose `[p]`-image is `Zp` and whose `⊖R'`-translate is
  --    `Zr`.  Eight applications of the specialization brick clear the
  --    denominators; they cancel again after evaluation.
  have hhalf : ∀ (xZ yZ : F) (hZ : W.Nonsingular xZ yZ)
      (xZp yZp : F) (hZp : W.Nonsingular xZp yZp)
      (xZr yZr : F) (hZr : W.Nonsingular xZr yZr),
      (p : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) =
        WeierstrassCurve.Affine.Point.some xZp yZp hZp →
      (WeierstrassCurve.Affine.Point.some xZr yZr hZr : W.Point) =
        -R' + WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      AdjoinRoot.evalEval hZp.left aQ *
          AdjoinRoot.evalEval hZr.left (enumVertical W val) ^ p =
        c' * AdjoinRoot.evalEval hZr.left a ^ p *
          AdjoinRoot.evalEval hZp.left (CoordinateRing.XClass W xR) ^ p := by
    intro xZ yZ hZ xZp yZp hZp xZr yZr hZr hZpc hZrc
    have hZpc' : (WeierstrassCurve.Affine.Point.some xZp yZp hZp : W.Point) =
        (0 : W.Point) +
          (p : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [zero_add]
      exact hZpc.symm
    have hZrc' : (WeierstrassCurve.Affine.Point.some xZr yZr hZr : W.Point) =
        -R' + (1 : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [one_zsmul]
      exact hZrc
    obtain ⟨n₁, d₁, hd₁, hK₁, hv₁⟩ :=
      exists_pointEval_specialization hΔ (p : ℤ) hp0 hZ hZp hZpc' aQ
    obtain ⟨n₂, d₂, hd₂, hK₂, hv₂⟩ :=
      exists_pointEval_specialization hΔ (p : ℤ) hp0 hZ hZp hZpc'
        (CoordinateRing.XClass W xR)
    obtain ⟨n₃, d₃, hd₃, hK₃, hv₃⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hnr0 hZ hZr hZrc'
        (enumVertical W val)
    obtain ⟨n₄, d₄, hd₄, hK₄, hv₄⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hnr0 hZ hZr hZrc' a
    -- the generic identity with all eight denominators cleared: an
    -- identity of COORDINATE-RING elements, so it can be evaluated
    have hFW : n₁ * n₃ ^ p * d₄ ^ p * d₂ ^ p =
        coordC W c' * n₄ ^ p * n₂ ^ p * d₁ * d₃ ^ p := by
      refine IsFractionRing.injective W.CoordinateRing W.FunctionField ?_
      simp only [map_mul, map_pow, algebraMap_coordC]
      rw [← hK₁, ← hK₂, ← hK₃, ← hK₄]
      linear_combination (algebraMap W.CoordinateRing W.FunctionField d₁ *
        algebraMap W.CoordinateRing W.FunctionField d₃ ^ p *
        algebraMap W.CoordinateRing W.FunctionField d₄ ^ p *
        algebraMap W.CoordinateRing W.FunctionField d₂ ^ p) * hcore
    have hval := congrArg (AdjoinRoot.evalEval hZ.left) hFW
    simp only [map_mul, map_pow, evalEval_coordC] at hval
    rw [hv₁, hv₂, hv₃, hv₄] at hval
    have hden : AdjoinRoot.evalEval hZ.left d₁ * AdjoinRoot.evalEval hZ.left d₂ ^ p *
        AdjoinRoot.evalEval hZ.left d₃ ^ p *
        AdjoinRoot.evalEval hZ.left d₄ ^ p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hd₁ (pow_ne_zero _ hd₂))
        (pow_ne_zero _ hd₃)) (pow_ne_zero _ hd₄)
    refine mul_right_cancel₀ hden ?_
    linear_combination hval
  -- ── PROVEN glue 2: the two `p`-division points `S'` and `P'⊕S'` are
  --    affine, since their `[p]`-images `S` and `P⊕S` are
  obtain ⟨xS', yS', hS'n, hS'eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = S' := by
    cases hc : (S' : W.Point) with
    | zero =>
      exfalso
      refine WeierstrassCurve.Affine.Point.some_ne_zero hS ?_
      rw [← hS'p, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xW', yW', hW'n, hW'eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = P' + S' := by
    cases hc : (P' + S' : W.Point) with
    | zero =>
      exfalso
      refine WeierstrassCurve.Affine.Point.some_ne_zero hPS ?_
      rw [hPSc, ← hP'p, ← hS'p, ← smul_add, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- ── PROVEN glue 3: the two balanced halves
  have hcS := hhalf xS' yS' hS'n xS yS hS xU yU hU
    (by rw [hS'eq]; exact hS'p)
    (by rw [hUeq, hS'eq]; abel)
  have hcPS := hhalf xW' yW' hW'n xPS yPS hPS xV yV hV
    (by rw [hW'eq, smul_add, hP'p, hS'p]; exact hPSc.symm)
    (by rw [hVeq, hW'eq]; abel)
  -- ── the ratio: `c'` cancels (PROVEN glue)
  simp only [map_pow]
  rw [mul_pow, mul_pow]
  linear_combination
    (AdjoinRoot.evalEval hS.left (CoordinateRing.XClass W xR) ^ p *
      AdjoinRoot.evalEval hU.left a ^ p) * hcPS -
    (AdjoinRoot.evalEval hPS.left (CoordinateRing.XClass W xR) ^ p *
      AdjoinRoot.evalEval hV.left a ^ p) * hcS

omit [IsAlgClosed F] in
/-- **Converse of `exists_span_eq_prod_pointIdeal` (PROVEN)**: a
point-ideal product that is PRINCIPAL has zero-sum multiset.  Indeed
`Ideal.span {a}` with `a ≠ 0` is trivial in the class group
(`ClassGroup.mk_eq_one_of_coe_ideal` against `coe_prod_pointIdeal'`), and
the class of a point-ideal product is the `toClass`-sum of its points
(`mk_prod_pointIdeal'`), which is `toClass D.sum` because `toClass` is
additive; `toClass` has trivial kernel (mathlib's
`Point.toClass_eq_zero`), so `D.sum = 0`.

Together with `exists_span_eq_prod_pointIdeal` this makes "the affine
divisor `D` is principal" and "`D` sums to `O` in the group law" the SAME
condition.  Its use here is to read the torsion of a Miller generator's
head off its span: `div a = Σ_κ (T'⊕κ) + Σ_κ (⊖κ)` sums to
`(card E[p])·T' = p²·T'`, so such a generator exists exactly when
`Q = [p]T'` is `p`-torsion — which is what makes the translation
character of `g = a/v` a `p`-th root of unity, and hence what the
alternating law below is about. -/
theorem sum_eq_zero_of_span_eq_prod_pointIdeal {D : Multiset W.Point}
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} = (D.map (pointIdeal W)).prod) :
    D.sum = 0 := by
  have hmk : ClassGroup.mk W.FunctionField (D.map (pointIdeal' W)).prod = 1 :=
    (ClassGroup.mk_eq_one_of_coe_ideal (coe_prod_pointIdeal' D)).mpr
      ⟨a, ha, hspan.symm⟩
  rw [mk_prod_pointIdeal', ← map_multiset_sum] at hmk
  -- `Additive.toMul x = 1` is definitionally `x = 0`
  have h0 : WeierstrassCurve.Affine.Point.toClass D.sum = 0 := hmk
  exact (WeierstrassCurve.Affine.Point.toClass_eq_zero D.sum).mp h0

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Membership in the divisor forces vanishing** (converse of
`mem_of_evalEval_eq_zero`). -/
theorem evalEval_eq_zero_of_mem {D : Multiset W.Point} {a : W.CoordinateRing}
    (hspan : Ideal.span {a} = (D.map (pointIdeal W)).prod)
    {x y : F} (h : W.Nonsingular x y)
    (hmem : (WeierstrassCurve.Affine.Point.some x y h : W.Point) ∈ D) :
    AdjoinRoot.evalEval h.left a = 0 := by
  refine coordEval_eq_zero_of_mem h ?_
  have hdvd : pointIdeal W (.some x y h) ∣ (D.map (pointIdeal W)).prod :=
    Multiset.dvd_prod (Multiset.mem_map_of_mem _ hmem)
  have hle := Ideal.le_of_dvd hdvd
  rw [← hspan] at hle
  exact hle (Ideal.mem_span_singleton_self a)

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The hyperelliptic involution is an involution.** -/
lemma involHom_involHom (z : W.CoordinateRing) :
    involHom W (involHom W z) = z := by
  have h : (involHom W).comp (involHom W) = RingHom.id W.CoordinateRing := by
    refine coordinateRing_ringHom_ext ?_ ?_ ?_
    · intro d
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [show CoordinateRing.mk W (Polynomial.C (Polynomial.C d)) = coordC W d from rfl,
        involHom_coordC, involHom_coordC]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [show CoordinateRing.mk W (Polynomial.C Polynomial.X) = coordX W from rfl,
        involHom_coordX, involHom_coordX]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [show CoordinateRing.mk W Polynomial.X = coordY W from rfl,
        involHom_coordY, map_sub, map_sub, map_mul, map_neg, involHom_coordY,
        involHom_coordC, involHom_coordC, involHom_coordX]
      ring
  exact congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing =>
    (f : W.CoordinateRing → W.CoordinateRing) z) h

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The hyperelliptic involution kills nothing.** -/
lemma involHom_ne_zero {z : W.CoordinateRing} (hz : z ≠ 0) : involHom W z ≠ 0 := by
  intro h0
  apply hz
  rw [← involHom_involHom (W := W) z, h0, map_zero]

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Evaluation at `⊖ω` is evaluation at `ω` composed with the
hyperelliptic involution.** -/
lemma pointEval_involHom {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀)
    (h' : ((W.map φ).toAffine).Equation x₀ ((W.map φ).toAffine.negY x₀ y₀))
    (z : W.CoordinateRing) :
    pointEval φ h' (involHom W z) = pointEval φ h z := by
  have hcomp : (pointEval φ h').comp (involHom W) = pointEval φ h := by
    refine coordinateRing_ringHom_ext ?_ ?_ ?_
    · intro d
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [show CoordinateRing.mk W (Polynomial.C (Polynomial.C d)) = coordC W d from rfl,
        involHom_coordC]
      simp only [coordC, pointEval_C]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [show CoordinateRing.mk W (Polynomial.C Polynomial.X) = coordX W from rfl,
        involHom_coordX]
      simp only [coordX, pointEval_X]
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [show CoordinateRing.mk W Polynomial.X = coordY W from rfl,
        involHom_coordY, map_sub, map_sub, map_neg, map_mul]
      simp only [coordX, coordY, coordC, pointEval_X, pointEval_Y, pointEval_C]
      show -((W.map φ).toAffine.negY x₀ y₀) - φ W.a₁ * x₀ - φ W.a₃ = y₀
      rw [WeierstrassCurve.Affine.negY]
      show -(-y₀ - (W.map φ).a₁ * x₀ - (W.map φ).a₃) - φ W.a₁ * x₀ - φ W.a₃ = y₀
      simp only [WeierstrassCurve.map]
      ring
  exact congrArg (fun f : W.CoordinateRing →+* K' =>
    (f : W.CoordinateRing → K') z) hcomp

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The involution transports a point-ideal product to that of the
negated multiset.** -/
lemma map_involHom_prod_pointIdeal (D : Multiset W.Point) :
    Ideal.map (involHom W) ((D.map (pointIdeal W)).prod) =
      (((D.map fun R => -R).map (pointIdeal W)).prod) := by
  induction D using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [Ideal.one_eq_top, Ideal.map_top]
  | cons R D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Ideal.map_mul, ih,
      Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      map_involHom_pointIdeal]

omit [IsAlgClosed F] in
/-- Base change commutes with negation of points. -/
lemma constPoint_neg (Q : W.Point) : constPoint W (-Q) = -constPoint W Q := by
  rw [show constPoint W (-Q) = constPointHom W (-Q) from rfl, map_neg]
  rfl

omit [IsAlgClosed F] in
/-- **`Q ⊖ taut` is affine.** -/
theorem exists_translate_some_neg (hΔ : W.Δ ≠ 0) (Q : W.Point) :
    ∃ (xκ yκ : W.FunctionField) (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W Q + (-1 : ℤ) • tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
  obtain ⟨x, y, h, hpt⟩ := exists_translate_some hΔ (-Q)
  refine ⟨x, (curveK W).negY x y,
    (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h, ?_⟩
  have hneg : -(constPoint W (-Q) + tautPoint W hΔ) =
      constPoint W Q + (-1 : ℤ) • tautPoint W hΔ := by
    rw [neg_add, neg_one_zsmul, constPoint_neg, neg_neg]
  rw [← hneg, hpt, WeierstrassCurve.Affine.Point.neg_some]

/-- **The `m = −1` divisor transport** (companion of
`spanSingleton_pointEval_translate`, which is the `m = 1` case): if `b`
generates the point-ideal product of the affine divisor `D`, then the
evaluation `b(Q ⊖ taut)` has divisor `Σ_{R ∈ D} (Q ⊖ R) − |D|·(Q)`.

Proof: `b(Q ⊖ X) = (σ b)(⊖Q ⊕ X)` for the hyperelliptic involution `σ =
involHom`, whose comorphism identity is `pointEval_involHom` and whose
divisor bookkeeping is `map_involHom_pointIdeal`; so this is the `m = 1`
transport applied to `σ b` at `⊖Q`. -/
theorem spanSingleton_pointEval_translate_neg (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + (-1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {b : W.CoordinateRing} (hb : b ≠ 0) {D : Multiset W.Point}
    (hspan : Ideal.span {b} = (D.map (pointIdeal W)).prod) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left b) *
      (pointIdeal' W Q :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
          Multiset.card D =
    (D.map fun R => (pointIdeal' W (Q - R) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
  have hκ' : (curveK W).Nonsingular xκ ((curveK W).negY xκ yκ) :=
    (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hκ
  have hptneg : constPoint W (-Q) + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ ((curveK W).negY xκ yκ) hκ' := by
    have h1 : -(constPoint W Q + (-1 : ℤ) • tautPoint W hΔ) =
        constPoint W (-Q) + tautPoint W hΔ := by
      rw [neg_add, neg_one_zsmul, neg_neg, constPoint_neg]
    rw [← h1, hpt, WeierstrassCurve.Affine.Point.neg_some]
  have hbspan' : Ideal.span {involHom W b} =
      (((D.map fun R => -R).map (pointIdeal W)).prod) := by
    rw [← map_involHom_prod_pointIdeal, ← hspan, Ideal.map_span,
      Set.image_singleton]
  have hbrick := spanSingleton_pointEval_translate hΔ hptneg
    (involHom_ne_zero hb) hbspan'
  have heval : pointEval (constHom W) hκ'.left (involHom W b) =
      pointEval (constHom W) hκ.left b :=
    pointEval_involHom (constHom W) hκ.left hκ'.left b
  rw [neg_neg, Multiset.card_map, heval] at hbrick
  refine hbrick.trans ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun R _ => ?_)
  simp only [Function.comp_apply]
  congr 1
  abel

omit [IsAlgClosed F] [Fact (1 < p)] in
/-- **The enumeration of `E[p]` is closed under negation.** -/
lemma map_neg_eq {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z) :
    (Finset.univ.val.map fun i => -val i) =
      Finset.univ.val.map fun i => val i := by
  classical
  have hex : ∀ i : ι, ∃ j : ι, val j = -val i := fun i =>
    hval_surj _ (by rw [smul_neg, hval_tor i, neg_zero])
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : -val i = -val j := by rw [← hf i, ← hf j, hij]
    exact hval_inj (neg_injective h1)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  have h2 : (Finset.univ.val.map fun i => val (Equiv.ofBijective f hbij i)) =
      Finset.univ.val.map fun i => val i :=
    map_univ_comp_equiv (Equiv.ofBijective f hbij) val
  rw [← h2]
  exact Multiset.map_congr rfl fun i _ => (hf i).symm

omit [IsAlgClosed F] [Fact (1 < p)] in
/-- **The cross-ratio divisor cancellation (step 1 of the telescope).**
With `S(A) := Σ_{κ ∈ E[p]} (A ⊕ κ)` and `div a = S(T') − S(0)`,
`div b = S(P') − S(0)`, `div v = S(0) + S(0)` (in the cleared
point-ideal bookkeeping), the affine divisor of the numerator of
`Ξ(X) = [g_P(T' ⊖ X)·g(X)] / [g_P(⊖X)·g(P' ⊕ X)]` equals that of its
denominator.  Both sides reduce to `A_{T'−P'} + 2·A_{T'} + 3·A_0 +
2·A_{−P'}` where `A_S := Σ_κ (S ⊕ κ)`; the MIXED signs `T' ⊖ X` against
`P' ⊕ X` are what makes this cancel. -/
lemma crossRatio_divisor_eq {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (T' P' : W.Point) :
    (((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i).map fun R => T' - R) +
      ((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i) +
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map fun R => (0 : W.Point) - R) +
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - P') =
    (((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i).map fun R => (0 : W.Point) - R) +
      (((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - P') +
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map fun R => T' - R) +
      ((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i) := by
  classical
  have hn : (Finset.univ.val.map fun i => -val i) =
      Finset.univ.val.map fun i => val i :=
    map_neg_eq (p := p) hval_inj hval_tor hval_surj
  have hAm : ∀ S : W.Point, (Finset.univ.val.map fun i => S - val i) =
      Finset.univ.val.map fun i => S + val i := by
    intro S
    have h2 := congrArg (Multiset.map fun R : W.Point => S + R) hn
    simp only [Multiset.map_map, Function.comp_apply] at h2
    refine Eq.trans ?_ h2
    exact Multiset.map_congr rfl fun i _ => by abel
  have key : ∀ (S : W.Point) (f : ι → W.Point) (g : W.Point → W.Point),
      (∀ i, g (f i) = S - val i) →
      ((Finset.univ.val.map f).map g) =
        Finset.univ.val.map fun i => S + val i := by
    intro S f g h
    rw [Multiset.map_map]
    exact Eq.trans (Multiset.map_congr rfl fun i _ => h i) (hAm S)
  have key' : ∀ (S : W.Point) (f : ι → W.Point) (g : W.Point → W.Point),
      (∀ i, g (f i) = S + val i) →
      ((Finset.univ.val.map f).map g) =
        Finset.univ.val.map fun i => S + val i := by
    intro S f g h
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => h i
  have key0 : ∀ (f : ι → W.Point) (g : W.Point → W.Point),
      (∀ i, g (f i) = -val i) →
      ((Finset.univ.val.map f).map g) = Finset.univ.val.map fun i => val i := by
    intro f g h
    rw [Multiset.map_map]
    exact Eq.trans (Multiset.map_congr rfl fun i _ => h i) hn
  have key0' : ∀ (f : ι → W.Point) (g : W.Point → W.Point),
      (∀ i, g (f i) = val i) →
      ((Finset.univ.val.map f).map g) = Finset.univ.val.map fun i => val i := by
    intro f g h
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => h i
  have e1 : ((Finset.univ.val.map fun i => P' + val i).map fun R => T' - R) =
      Finset.univ.val.map fun i => (T' - P') + val i :=
    key (T' - P') _ _ fun i => by abel
  have e2 : ((Finset.univ.val.map fun i => -val i).map fun R => T' - R) =
      Finset.univ.val.map fun i => T' + val i :=
    key' T' _ _ fun i => by abel
  have e4 : ((Finset.univ.val.map fun i => val i).map
      fun R => (0 : W.Point) - R) = Finset.univ.val.map fun i => val i :=
    key0 _ _ fun i => by abel
  have e5 : ((Finset.univ.val.map fun i => -val i).map
      fun R => (0 : W.Point) - R) = Finset.univ.val.map fun i => val i :=
    key0' _ _ fun i => by abel
  have e6 : ((Finset.univ.val.map fun i => val i).map fun R => R - P') =
      Finset.univ.val.map fun i => (-P') + val i :=
    key' (-P') _ _ fun i => by abel
  have e7 : ((Finset.univ.val.map fun i => -val i).map fun R => R - P') =
      Finset.univ.val.map fun i => (-P') + val i :=
    key (-P') _ _ fun i => by abel
  have e8 : ((Finset.univ.val.map fun i => P' + val i).map
      fun R => (0 : W.Point) - R) =
      Finset.univ.val.map fun i => (-P') + val i :=
    key (-P') _ _ fun i => by abel
  have e9 : ((Finset.univ.val.map fun i => T' + val i).map fun R => R - P') =
      Finset.univ.val.map fun i => (T' - P') + val i :=
    key' (T' - P') _ _ fun i => by abel
  have e10 : ((Finset.univ.val.map fun i => val i).map fun R => T' - R) =
      Finset.univ.val.map fun i => T' + val i :=
    key T' _ _ fun i => by abel
  simp only [Multiset.map_add]
  rw [e1, e2, e4, e5, e6, e7, e8, e9, e10, hn]
  abel



omit [IsAlgClosed F] [Fact (1 < p)] in
/-- The fractional-ideal form of `crossRatio_divisor_eq`. -/
lemma crossRatio_divisor_prod_eq {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (T' P' : W.Point) :
    ((((Finset.univ.val.map fun i => P' + val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W (T' - R) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => T' + val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W ((0 : W.Point) - R) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W (R - P') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) =
    ((((Finset.univ.val.map fun i => P' + val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W ((0 : W.Point) - R) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => T' + val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W (R - P') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W (T' - R) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
      ((((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) := by
  have h := congrArg (fun M : Multiset W.Point =>
      ((M.map fun R => (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod))
    (crossRatio_divisor_eq (p := p) hval_inj hval_tor hval_surj T' P')
  simpa only [Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Function.comp_def] using h

omit [Fact (1 < p)] in
/-- **Stage B, leaf 3a-i-α (PROVEN): the CROSS-RATIO CONSTANT `γ`.**
`Ξ(X) := [g_P(T' ⊖ X)·g(X)] / [g_P(⊖X)·g(P' ⊕ X)]` has trivial divisor
(`crossRatio_divisor_eq`), hence is a constant `γ`; this is that
statement read at an arbitrary affine point `Z` whose three companions
`T' ⊖ Z`, `⊖Z`, `P' ⊕ Z` are affine, in cleared (division-free) form,
so no nonvanishing hypotheses are needed. -/
theorem exists_millerValue_crossRatio_read {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    {a b : W.CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hbspan : Ideal.span {b} =
      ((((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod) :
    ∃ γ : F, ∀ (xZ yZ : F) (hZ : W.Nonsingular xZ yZ)
      (xZ1 yZ1 : F) (hZ1 : W.Nonsingular xZ1 yZ1)
      (xZ3 yZ3 : F) (hZ3 : W.Nonsingular xZ3 yZ3)
      (xZ4 yZ4 : F) (hZ4 : W.Nonsingular xZ4 yZ4),
      (WeierstrassCurve.Affine.Point.some xZ1 yZ1 hZ1 : W.Point) =
        T' - WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      (WeierstrassCurve.Affine.Point.some xZ3 yZ3 hZ3 : W.Point) =
        -(WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) →
      (WeierstrassCurve.Affine.Point.some xZ4 yZ4 hZ4 : W.Point) =
        P' + WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      AdjoinRoot.evalEval hZ1.left b * AdjoinRoot.evalEval hZ.left a *
          AdjoinRoot.evalEval hZ3.left (enumVertical W val) *
          AdjoinRoot.evalEval hZ4.left (enumVertical W val) =
        γ * (AdjoinRoot.evalEval hZ3.left b * AdjoinRoot.evalEval hZ4.left a *
          AdjoinRoot.evalEval hZ1.left (enumVertical W val) *
          AdjoinRoot.evalEval hZ.left (enumVertical W val)) := by
  classical
  have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
  have hvspan := span_enumVertical (W := W) val
  obtain ⟨x1, y1, hk1, hpt1⟩ := exists_translate_some_neg hΔ T'
  obtain ⟨x3, y3, hk3, hpt3⟩ := exists_translate_some_neg hΔ (0 : W.Point)
  obtain ⟨x4, y4, hk4, hpt4⟩ := exists_translate_some hΔ P'
  have hb1 := spanSingleton_pointEval_translate_neg hΔ hpt1 hb hbspan
  have hv1 := spanSingleton_pointEval_translate_neg hΔ hpt1 hv0 hvspan
  have hb3 := spanSingleton_pointEval_translate_neg hΔ hpt3 hb hbspan
  have hv3 := spanSingleton_pointEval_translate_neg hΔ hpt3 hv0 hvspan
  have ha4 := spanSingleton_pointEval_translate hΔ hpt4 ha hspan
  have hv4 := spanSingleton_pointEval_translate hΔ hpt4 hv0 hvspan
  have hcda : Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
      Finset.univ.val.map fun i => -val i) =
    Multiset.card ((Finset.univ.val.map fun i => val i) +
      Finset.univ.val.map fun i => -val i) := by simp
  have hcdb : Multiset.card ((Finset.univ.val.map fun i => P' + val i) +
      Finset.univ.val.map fun i => -val i) =
    Multiset.card ((Finset.univ.val.map fun i => val i) +
      Finset.univ.val.map fun i => -val i) := by simp
  rw [hcda] at ha4
  rw [hcdb] at hb1 hb3
  set n := Multiset.card ((Finset.univ.val.map fun i => val i) +
    Finset.univ.val.map fun i => -val i) with hndef
  obtain ⟨γ, hgen⟩ : ∃ γ : F,
      pointEval (constHom W) hk1.left b *
          algebraMap W.CoordinateRing W.FunctionField a *
          pointEval (constHom W) hk3.left (enumVertical W val) *
          pointEval (constHom W) hk4.left (enumVertical W val) =
        constHom W γ * (pointEval (constHom W) hk3.left b *
          pointEval (constHom W) hk4.left a *
          pointEval (constHom W) hk1.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
    have hunit : IsUnit
        (((pointIdeal' W T' :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n *
          (pointIdeal' W (0 : W.Point) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
          (pointIdeal' W (-P') :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) :=
      (((pointIdeal' W T').isUnit.pow n).mul
        ((pointIdeal' W (0 : W.Point)).isUnit.pow n)).mul
          ((pointIdeal' W (-P')).isUnit.pow n)
    have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hk3.left b *
            pointEval (constHom W) hk4.left a *
            pointEval (constHom W) hk1.left (enumVertical W val) *
            algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hk1.left b *
            algebraMap W.CoordinateRing W.FunctionField a *
            pointEval (constHom W) hk3.left (enumVertical W val) *
            pointEval (constHom W) hk4.left (enumVertical W val)) := by
      simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton]
      refine hunit.mul_right_cancel ?_
      calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk3.left b) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk4.left a) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk1.left (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (enumVertical W val)) *
            (((pointIdeal' W T' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n *
              (pointIdeal' W (0 : W.Point) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
              (pointIdeal' W (-P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n)
          = FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk3.left b) *
              (pointIdeal' W (0 : W.Point) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk4.left a) *
              (pointIdeal' W (-P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk1.left (enumVertical W val)) *
              (pointIdeal' W T' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (enumVertical W val)) := by ring
        _ = ((((Finset.univ.val.map fun i => P' + val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W ((0 : W.Point) - R) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W (R - P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W (T' - R) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W R :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) := by
              rw [hb3, ha4, hv1, prod_coe_pointIdeal'_eq_spanSingleton hvspan]
        _ = ((((Finset.univ.val.map fun i => P' + val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W (T' - R) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W R :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W ((0 : W.Point) - R) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) *
            ((((Finset.univ.val.map fun i => val i) +
                Finset.univ.val.map fun i => -val i).map fun R =>
              (pointIdeal' W (R - P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) :=
            (crossRatio_divisor_prod_eq (p := p) hval_inj hval_tor hval_surj
              T' P').symm
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk1.left b) *
              (pointIdeal' W T' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk3.left (enumVertical W val)) *
              (pointIdeal' W (0 : W.Point) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hk4.left (enumVertical W val)) *
              (pointIdeal' W (-P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) := by
              rw [hb1, hv3, hv4, prod_coe_pointIdeal'_eq_spanSingleton hspan]
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk1.left b) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk3.left (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hk4.left (enumVertical W val)) *
            (((pointIdeal' W T' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n *
              (pointIdeal' W (0 : W.Point) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) *
              (pointIdeal' W (-P') :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) := by
              ring
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
    obtain ⟨cc, -, hcz⟩ := coordinateRing_isUnit_eq_const z.isUnit
    refine ⟨cc, ?_⟩
    rw [← hz, Units.smul_def, hcz, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C cc))) =
        constHom W cc from rfl]
  refine ⟨γ, ?_⟩
  intro xZ yZ hZ xZ1 yZ1 hZ1 xZ3 yZ3 hZ3 xZ4 yZ4 hZ4 hZ1c hZ3c hZ4c
  have e1 : (WeierstrassCurve.Affine.Point.some xZ1 yZ1 hZ1 : W.Point) =
      T' + (-1 : ℤ) •
        (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
    rw [neg_one_zsmul, ← sub_eq_add_neg]; exact hZ1c
  have e3 : (WeierstrassCurve.Affine.Point.some xZ3 yZ3 hZ3 : W.Point) =
      (0 : W.Point) + (-1 : ℤ) •
        (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
    rw [neg_one_zsmul, zero_add]; exact hZ3c
  have hpt4' : constPoint W P' + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some x4 y4 hk4 := by
    rw [one_zsmul]; exact hpt4
  have e4 : (WeierstrassCurve.Affine.Point.some xZ4 yZ4 hZ4 : W.Point) =
      P' + (1 : ℤ) •
        (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
    rw [one_zsmul]; exact hZ4c
  have hE1b : EvalsTo hZ.left (pointEval (constHom W) hk1.left b)
      (AdjoinRoot.evalEval hZ1.left b) :=
    exists_pointEval_specialization hΔ (-1 : ℤ) hpt1 hZ hZ1 e1 b
  have hE1v : EvalsTo hZ.left
      (pointEval (constHom W) hk1.left (enumVertical W val))
      (AdjoinRoot.evalEval hZ1.left (enumVertical W val)) :=
    exists_pointEval_specialization hΔ (-1 : ℤ) hpt1 hZ hZ1 e1 (enumVertical W val)
  have hE3b : EvalsTo hZ.left (pointEval (constHom W) hk3.left b)
      (AdjoinRoot.evalEval hZ3.left b) :=
    exists_pointEval_specialization hΔ (-1 : ℤ) hpt3 hZ hZ3 e3 b
  have hE3v : EvalsTo hZ.left
      (pointEval (constHom W) hk3.left (enumVertical W val))
      (AdjoinRoot.evalEval hZ3.left (enumVertical W val)) :=
    exists_pointEval_specialization hΔ (-1 : ℤ) hpt3 hZ hZ3 e3 (enumVertical W val)
  have hE4a : EvalsTo hZ.left (pointEval (constHom W) hk4.left a)
      (AdjoinRoot.evalEval hZ4.left a) :=
    exists_pointEval_specialization hΔ (1 : ℤ) hpt4' hZ hZ4 e4 a
  have hE4v : EvalsTo hZ.left
      (pointEval (constHom W) hk4.left (enumVertical W val))
      (AdjoinRoot.evalEval hZ4.left (enumVertical W val)) :=
    exists_pointEval_specialization hΔ (1 : ℤ) hpt4' hZ hZ4 e4 (enumVertical W val)
  have hL := ((hE1b.mul (evalsTo_algebraMap hZ.left a)).mul hE3v).mul hE4v
  have hR := (evalsTo_constHom hZ.left γ).mul
    (((hE3b.mul hE4a).mul hE1v).mul
      (evalsTo_algebraMap hZ.left (enumVertical W val)))
  rw [← hgen] at hR
  exact hL.unique hR

omit [Fact (1 < p)] in
/-- **Stage B, leaf 3a-ii-α (PROVEN): the TRANSLATION CHARACTER of `g`
at the `p`-torsion point `P = p•P'`, in generic form.**  With
`g = a/v` (`div g = S(T') − S(0)`), `g ∘ τ_P / g` has trivial divisor
because translation by `P ∈ E[p]` permutes the enumeration `val`
(`map_add_torsion_eq`), so `g ∘ τ_P = c·g` for a constant `c`; the
conclusion is that identity in cleared form at every affine `Z₁` with
`Z₂ = P ⊕ Z₁` affine.

This is the generic half of `millerValue_translationChar_pow` (whose
statement exposes only `c^p = 1`), extracted so that consumers can use
the POINT-INDEPENDENCE of `c` — which is what transports the constant
identity `γ^p·c = 1` from an auxiliary generic point to `U`.  The proof
is the `hgen`/`hstep` block of `millerValue_translationChar_pow`. -/
theorem exists_millerValue_translationChar {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hPtor : (p : ℤ) • ((p : ℤ) • P') = 0) :
    ∃ c : F, ∀ (x₁ y₁ : F) (h₁ : W.Nonsingular x₁ y₁) (x₂ y₂ : F)
      (h₂ : W.Nonsingular x₂ y₂),
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.Point) =
        (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ →
      AdjoinRoot.evalEval h₂.left a *
          AdjoinRoot.evalEval h₁.left (enumVertical W val) =
        c * (AdjoinRoot.evalEval h₂.left (enumVertical W val) *
          AdjoinRoot.evalEval h₁.left a) := by
  classical
  have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
  have hPt : (p : ℤ) • ((p : ℤ) • P' : W.Point) = 0 := hPtor
  -- ── multiset translation invariance under a `p`-torsion shift
  have hmap1 : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => val i - T) =
        Finset.univ.val.map fun i => val i := by
    intro T hT
    have h := map_add_torsion_eq (W := W) hval_inj hval_tor hval_surj
      (T := -T) (by rw [smul_neg, hT, neg_zero])
    rw [← h]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hmap2 : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => -val i - T) =
        Finset.univ.val.map fun i => -val i := by
    intro T hT
    have h := map_add_torsion_eq (W := W) hval_inj hval_tor hval_surj (T := T) hT
    have h2 := congrArg (Multiset.map (fun R : W.Point => -R)) h
    simp only [Multiset.map_map, Function.comp_apply] at h2
    rw [← h2]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hmap3 : ∀ (A T : W.Point), (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => A + val i - T) =
        Finset.univ.val.map fun i => A + val i := by
    intro A T hT
    have h2 := congrArg (Multiset.map (fun R : W.Point => A + R)) (hmap1 T hT)
    simp only [Multiset.map_map, Function.comp_apply] at h2
    rw [← h2]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hDv : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - T) =
      ((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i) := by
    intro T hT
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_apply]
    rw [hmap1 T hT, hmap2 T hT]
  have hDa : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - T) =
      ((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i) := by
    intro T hT
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_apply]
    rw [hmap3 T' T hT, hmap2 T hT]
  have hmapcomp : ∀ (D : Multiset W.Point) (Q : W.Point),
      (D.map fun R => (pointIdeal' W (R - Q) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) =
        ((D.map fun R => R - Q).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
    intro D Q
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun _ _ => rfl
  -- ── the GENERIC character identity `g∘τ_P = c·g`, multiplied out
  obtain ⟨xκ, yκ, hκ, hptκ⟩ := exists_translate_some (W := W) hΔ ((p : ℤ) • P')
  obtain ⟨c, hgen⟩ : ∃ c : F,
      pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        constHom W c * (pointEval (constHom W) hκ.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField a) := by
    have hCa := spanSingleton_pointEval_translate (W := W) hΔ hptκ ha hspan
    have hCv := spanSingleton_pointEval_translate (W := W) hΔ hptκ hv0
      (span_enumVertical (W := W) val)
    rw [hmapcomp _ _, hDa _ hPt, prod_coe_pointIdeal'_eq_spanSingleton hspan] at hCa
    rw [hmapcomp _ _, hDv _ hPt,
      prod_coe_pointIdeal'_eq_spanSingleton (span_enumVertical (W := W) val)] at hCv
    have hu : IsUnit ((pointIdeal' W (-((p : ℤ) • P')) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
          Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
            Finset.univ.val.map fun i => -val i)) :=
      (pointIdeal' W _).isUnit.pow _
    have hcard2 : Multiset.card ((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i) =
      Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i) := by
      simp
    rw [hcard2] at hCv
    have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hκ.left (enumVertical W val) *
            algebraMap W.CoordinateRing W.FunctionField a) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hκ.left a *
            algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
      simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton]
      refine hu.mul_right_cancel ?_
      calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) *
            (pointIdeal' W (-((p : ℤ) • P')) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
              Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i)
          = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left (enumVertical W val)) *
              (pointIdeal' W (-((p : ℤ) • P')) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                  Finset.univ.val.map fun i => -val i)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) := by ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) := by rw [hCv]
        _ = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a) *
              (pointIdeal' W (-((p : ℤ) • P')) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                  Finset.univ.val.map fun i => -val i)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
            rw [hCa]; ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
            (pointIdeal' W (-((p : ℤ) • P')) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
              Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i) := by ring
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
    obtain ⟨cc, -, hcz⟩ := coordinateRing_isUnit_eq_const z.isUnit
    refine ⟨cc, ?_⟩
    rw [← hz, Units.smul_def, hcz, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C cc))) =
        constHom W cc from rfl]
  have hptκ' : constPoint W ((p : ℤ) • P') + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
    rw [one_zsmul]; exact hptκ
  refine ⟨c, ?_⟩
  intro x₁ y₁ h₁ x₂ y₂ h₂ heq
  have heq' : (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.Point) =
      (p : ℤ) • P' + (1 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.Point) := by
    rw [one_zsmul]; exact heq
  have hEa : EvalsTo h₁.left (pointEval (constHom W) hκ.left a)
      (AdjoinRoot.evalEval h₂.left a) :=
    exists_pointEval_specialization hΔ (1 : ℤ) hptκ' h₁ h₂ heq' a
  have hEv : EvalsTo h₁.left (pointEval (constHom W) hκ.left (enumVertical W val))
      (AdjoinRoot.evalEval h₂.left (enumVertical W val)) :=
    exists_pointEval_specialization hΔ (1 : ℤ) hptκ' h₁ h₂ heq' (enumVertical W val)
  have hL := hEa.mul (evalsTo_algebraMap h₁.left (enumVertical W val))
  have hR := (evalsTo_constHom h₁.left c).mul
    (hEv.mul (evalsTo_algebraMap h₁.left a))
  rw [← hgen] at hR
  exact hL.unique hR


omit [Fact (1 < p)] in
/-- **Stage B, leaf 3a-i-β (PROVEN 2026-07-26): the cross-ratio constant
`γ` and the translation character `c` are INVERSE: `γ^p·c = 1`.**

This is steps 2–3 of the divisor telescope, the remaining content of
`exists_millerValue_crossRatio_const` once step 1 (the constancy of
`Ξ(X) := [g_P(T' ⊖ X)·g(X)]/[g_P(⊖X)·g(P' ⊕ X)]`, i.e. the hypothesis
`hγ`, PROVEN as `exists_millerValue_crossRatio_read`) is available.
Both `γ` and `c` are constants, so the identity may be proven at ANY
convenient point; the consumer transports it to `U` through `hc`.

**Proof plan (from the parent's docstring, reduced to what is left).**

2. `Θ(Y) := ∏_{j<p} g_P(Y ⊖ jP')` is CONSTANT: its divisor TELESCOPES,
   `Σ_{j<p} [S((j+1)P') − S(jP')] = S(p•P') − S(0) = 0`, the last step
   because `P = p•P' ∈ E[p]` translates the enumeration into itself
   (`map_add_torsion_eq`).  Concretely: apply
   `spanSingleton_pointEval_translate` at `Q = ⊖jP'` to `b` and to
   `v = enumVertical W val` for each `j < p`; the `I'_{jP'}^{2N}`
   correction factors cancel between numerator and denominator, and the
   multiset identity to check is
   `⋃_{j<p} (D_b ⊕ jP') = ⋃_{j<p} (D_v ⊕ jP')`, which telescopes since
   `D_b = Σ_κ (P'⊕κ) + Σ_κ (⊖κ)` and `D_v = Σ_κ (κ) + Σ_κ (⊖κ)`.
   **This is the one place the level-`p²` structure enters**, and it is
   what supplies the `p`-th root that Weil reciprocity cannot (see the
   dead-end analysis in `exists_millerValue_alternating`).
3. Pick an auxiliary point `Z₀` generic enough that the `4p` points
   `Z_j := jP' ⊕ Z₀` (`j ≤ p`), `T' ⊖ Z_j` and `⊖Z_j` (`j < p`) are all
   affine and off the supports of `div a`, `div b`, `div v` — possible
   because each support is a FINITE explicit multiset (`hspan`,
   `hbspan`, `span_enumVertical`) while `W(F)` is infinite over the
   algebraically closed `F`.  Apply `hγ` at `Z = Z_j` for `j < p` and
   multiply.  Writing `B₁ := ∏_j b(T' ⊖ Z_j)`, `V₁ := ∏_j v(T' ⊖ Z_j)`,
   `B₂ := ∏_j b(⊖Z_j)`, `V₂ := ∏_j v(⊖Z_j)`, the two `g`-products
   telescope (`P' ⊕ Z_j = Z_{j+1}`) and step 2 gives `B₁·V₂ = B₂·V₁`,
   so after cancelling the nonzero `B₁·V₂·∏_{1≤j<p} a(Z_j)·v(Z_j)` what
   is left is `v(Z_p)·a(Z_0) = γ^p·a(Z_p)·v(Z_0)`, i.e. `γ^p·c = 1`
   by `hc` at `(Z_0, Z_p = P ⊕ Z_0)`.

**PROVEN 2026-07-26 exactly along that route.**  Implementation notes,
for a reader of the proof below:

* Step 2 is done GENERICALLY, in the function field, so that no
  affineness side conditions arise: `κ_j := ⊖jP' ⊕ taut` is affine for
  every `j` (`exists_translate_some`), the `m = 1` transport
  `spanSingleton_pointEval_translate` at `Q = ⊖jP'` gives the divisor of
  `b(Y ⊕ jP'... )` for each `j`, and multiplying over `j ∈ range p`
  cancels the common pole factor `∏_j I'_{jP'}^{|D|}` (a unit), leaving
  the multiset identity `⋃_{j<p}(D_b ⊕ jP') = ⋃_{j<p}(D_v ⊕ jP')`.  With
  `A_j := Σ_κ (jP' ⊕ κ)` and `map_neg_eq`, `D_b ⊕ jP' = A_{j+1} + A_j`
  and `D_v ⊕ jP' = A_j + A_j`, so the identity is the shift
  `Σ_{j<p} A_{j+1} = Σ_{j<p} A_j`, which closes because `A_p = A_0`
  (`map_add_torsion_eq` at the `p`-torsion point `P = p•P'`).  Trivial
  span then gives a CONSTANT `θ` with `∏_{j<p} b(Y ⊖ jP') =
  θ·∏_{j<p} v(Y ⊖ jP')` generically, and reading it at the two points
  `Y = T' ⊖ Z₀` and `Y = ⊖Z₀` (`exists_pointEval_specialization` at
  `(⊖jP', 1)`, multiplied over `j` through `EvalsTo.mul`) yields
  `B₁·V₂ = θ·V₁·V₂ = B₂·V₁` with no reference to the value of `θ`.
* Step 3's auxiliary point `Z₀` is chosen by `Infinite.exists_notMem_finset`
  outside ONE explicit finite multiset `base ⊖ jP'` (`j ≤ p`), where
  `base = {O, T'} + D_a + D_v + (⊖D_b) + (T' ⊖ D_v)`; that single
  avoidance simultaneously makes `Z_j`, `T' ⊖ Z_j`, `⊖Z_j` affine and
  `a(Z_j)`, `v(Z_j)`, `b(⊖Z_j)`, `v(T' ⊖ Z_j)` nonzero, via
  `mem_of_evalEval_eq_zero`.  `W.Point` is infinite because `F` is
  (`exists_equation` gives a point over every abscissa).
* The `p`-fold multiplication is an induction on `n ≤ p` carrying
  `∏_{j<n}[b(T'⊖Z_j)v(⊖Z_j)]·a(Z_0)v(Z_n) =
   γ^n·∏_{j<n}[b(⊖Z_j)v(T'⊖Z_j)]·a(Z_n)v(Z_0)`,
  whose step cancels `a(Z_n)·v(Z_n)`; the `a`/`v` telescoping is thus
  internal to the induction and only the `b`-products survive to meet
  step 2 at `n = p`.

FAITHFULNESS AUDIT (2026-07-26, from the proof).  Two hypotheses are NOT
consumed and are marked accordingly: `[Fact (1 < p)]` is `omit`ted (the
telescope is a statement about the integer `p` alone — for `p = 0` it
degenerates correctly to `c = 1`, which `hc` already forces), and
`_ha : a ≠ 0` is underscored (only `hspan` is used, to locate the zeros
of `a`; `a ≠ 0` would be needed for a divisor computation ABOUT `a`, and
no such computation occurs — `a` appears only through readings that the
choice of `Z₀` keeps off its zero locus).  `hb` IS load-bearing: step 2
runs `spanSingleton_pointEval_translate` on `b`. -/
theorem millerValue_crossRatio_pow_mul_translationChar {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    {a b : W.CoordinateRing} (_ha : a ≠ 0) (hb : b ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hbspan : Ideal.span {b} =
      ((((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hPtor : (p : ℤ) • ((p : ℤ) • P') = 0)
    {γ : F}
    (hγ : ∀ (xZ yZ : F) (hZ : W.Nonsingular xZ yZ)
      (xZ1 yZ1 : F) (hZ1 : W.Nonsingular xZ1 yZ1)
      (xZ3 yZ3 : F) (hZ3 : W.Nonsingular xZ3 yZ3)
      (xZ4 yZ4 : F) (hZ4 : W.Nonsingular xZ4 yZ4),
      (WeierstrassCurve.Affine.Point.some xZ1 yZ1 hZ1 : W.Point) =
        T' - WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      (WeierstrassCurve.Affine.Point.some xZ3 yZ3 hZ3 : W.Point) =
        -(WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) →
      (WeierstrassCurve.Affine.Point.some xZ4 yZ4 hZ4 : W.Point) =
        P' + WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      AdjoinRoot.evalEval hZ1.left b * AdjoinRoot.evalEval hZ.left a *
          AdjoinRoot.evalEval hZ3.left (enumVertical W val) *
          AdjoinRoot.evalEval hZ4.left (enumVertical W val) =
        γ * (AdjoinRoot.evalEval hZ3.left b * AdjoinRoot.evalEval hZ4.left a *
          AdjoinRoot.evalEval hZ1.left (enumVertical W val) *
          AdjoinRoot.evalEval hZ.left (enumVertical W val)))
    {c : F}
    (hc : ∀ (x₁ y₁ : F) (h₁ : W.Nonsingular x₁ y₁) (x₂ y₂ : F)
      (h₂ : W.Nonsingular x₂ y₂),
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.Point) =
        (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ →
      AdjoinRoot.evalEval h₂.left a *
          AdjoinRoot.evalEval h₁.left (enumVertical W val) =
        c * (AdjoinRoot.evalEval h₂.left (enumVertical W val) *
          AdjoinRoot.evalEval h₁.left a)) :
    γ ^ p * c = 1 := by
  classical
  have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
  have hvspan := span_enumVertical (W := W) val
  set Da : Multiset W.Point :=
    (Finset.univ.val.map fun i => T' + val i) +
      Finset.univ.val.map fun i => -val i with hDa
  set Db : Multiset W.Point :=
    (Finset.univ.val.map fun i => P' + val i) +
      Finset.univ.val.map fun i => -val i with hDb
  set Dv : Multiset W.Point :=
    (Finset.univ.val.map fun i => val i) +
      Finset.univ.val.map fun i => -val i with hDv
  -- ── `W(F)` is infinite
  have hptx : ∀ x₀ : F, ∃ v : F, W.Nonsingular x₀ v := by
    intro x₀
    obtain ⟨v, hv⟩ := exists_equation W x₀
    exact ⟨v, (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hv⟩
  choose vv hvv using hptx
  have hinjF : Function.Injective
      (fun x₀ : F =>
        (WeierstrassCurve.Affine.Point.some x₀ (vv x₀) (hvv x₀) : W.Point)) := by
    intro s t hst
    have hst' := hst
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hst'
    exact hst'.1
  haveI : Infinite W.Point := Infinite.of_injective _ hinjF
  have haff : ∀ A : W.Point, A ≠ 0 → ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = A := by
    intro A hA
    cases A with
    | zero => exact absurd rfl hA
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- ── the finite bad locus for the auxiliary point
  set base : Multiset W.Point :=
    ({0, T'} : Multiset W.Point) + Da + Dv + (Db.map fun S => -S) +
      (Dv.map fun S => T' - S) with hbase
  set bad : Multiset W.Point :=
    (Multiset.range (p + 1)).bind fun j => base.map fun R => R - (j : ℤ) • P' with hbad
  obtain ⟨Z₀, hZ₀⟩ := Infinite.exists_notMem_finset (α := W.Point) bad.toFinset
  have hgood : ∀ j : ℕ, j ≤ p → ∀ R ∈ base, ((j : ℤ) • P' + Z₀ : W.Point) ≠ R := by
    intro j hj R hR heq
    refine hZ₀ (Multiset.mem_toFinset.mpr ?_)
    rw [hbad]
    refine Multiset.mem_bind.mpr ⟨j, Multiset.mem_range.mpr (Nat.lt_succ_of_le hj), ?_⟩
    refine Multiset.mem_map.mpr ⟨R, hR, ?_⟩
    rw [← heq]
    abel
  have hbmem : ∀ R : W.Point,
      (R ∈ ({0, T'} : Multiset W.Point) ∨ R ∈ Da ∨ R ∈ Dv ∨
        R ∈ Db.map (fun S => -S) ∨ R ∈ Dv.map (fun S => T' - S)) → R ∈ base := by
    intro R hR
    rw [hbase]
    simp only [Multiset.mem_add]
    tauto
  have hb0 : (0 : W.Point) ∈ base := hbmem _ (Or.inl (by simp))
  have hbT : T' ∈ base := hbmem _ (Or.inl (by simp))
  -- ── affineness of the telescope points
  have hZne : ∀ j : ℕ, j ≤ p → ((j : ℤ) • P' + Z₀ : W.Point) ≠ 0 :=
    fun j hj => hgood j hj 0 hb0
  have hTZne : ∀ j : ℕ, j ≤ p → (T' - ((j : ℤ) • P' + Z₀) : W.Point) ≠ 0 := by
    intro j hj h0
    rw [sub_eq_zero] at h0
    exact hgood j hj T' hbT h0.symm
  have hZex : ∀ j : ℕ, ∃ (x y : F) (h : W.Nonsingular x y),
      j ≤ p → (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        (j : ℤ) • P' + Z₀ := by
    intro j
    by_cases hj : j ≤ p
    · obtain ⟨x, y, h, hxy⟩ := haff _ (hZne j hj)
      exact ⟨x, y, h, fun _ => hxy⟩
    · exact ⟨0, vv 0, hvv 0, fun hcon => absurd hcon hj⟩
  choose zx zy zh zeq using hZex
  have hMex : ∀ j : ℕ, ∃ (x y : F) (h : W.Nonsingular x y),
      j ≤ p → (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        T' - ((j : ℤ) • P' + Z₀) := by
    intro j
    by_cases hj : j ≤ p
    · obtain ⟨x, y, h, hxy⟩ := haff _ (hTZne j hj)
      exact ⟨x, y, h, fun _ => hxy⟩
    · exact ⟨0, vv 0, hvv 0, fun hcon => absurd hcon hj⟩
  choose mx my mh meq using hMex
  have hNex : ∀ j : ℕ, ∃ (x y : F) (h : W.Nonsingular x y),
      j ≤ p → (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        -((j : ℤ) • P' + Z₀) := by
    intro j
    by_cases hj : j ≤ p
    · obtain ⟨x, y, h, hxy⟩ := haff _ (neg_ne_zero.mpr (hZne j hj))
      exact ⟨x, y, h, fun _ => hxy⟩
    · exact ⟨0, vv 0, hvv 0, fun hcon => absurd hcon hj⟩
  choose nx ny nh neq using hNex
  -- ── nonvanishing of the evaluations
  have haZ : ∀ j : ℕ, j ≤ p → AdjoinRoot.evalEval (zh j).left a ≠ 0 := by
    intro j hj h0
    have hmem : ((j : ℤ) • P' + Z₀ : W.Point) ∈ Da := by
      rw [← zeq j hj]
      exact mem_of_evalEval_eq_zero hspan (zh j) h0
    exact hgood j hj _ (hbmem _ (Or.inr (Or.inl hmem))) rfl
  have hvZ : ∀ j : ℕ, j ≤ p →
      AdjoinRoot.evalEval (zh j).left (enumVertical W val) ≠ 0 := by
    intro j hj h0
    have hmem : ((j : ℤ) • P' + Z₀ : W.Point) ∈ Dv := by
      rw [← zeq j hj]
      exact mem_of_evalEval_eq_zero hvspan (zh j) h0
    exact hgood j hj _ (hbmem _ (Or.inr (Or.inr (Or.inl hmem)))) rfl
  have hbN : ∀ j : ℕ, j ≤ p → AdjoinRoot.evalEval (nh j).left b ≠ 0 := by
    intro j hj h0
    have hmem : (-((j : ℤ) • P' + Z₀) : W.Point) ∈ Db := by
      rw [← neq j hj]
      exact mem_of_evalEval_eq_zero hbspan (nh j) h0
    have hmem2 : ((j : ℤ) • P' + Z₀ : W.Point) ∈ Db.map (fun S => -S) := by
      have h2 : (- -((j : ℤ) • P' + Z₀) : W.Point) ∈ Db.map (fun S => -S) :=
        Multiset.mem_map_of_mem _ hmem
      rwa [neg_neg] at h2
    exact hgood j hj _ (hbmem _ (Or.inr (Or.inr (Or.inr (Or.inl hmem2))))) rfl
  have hvM : ∀ j : ℕ, j ≤ p →
      AdjoinRoot.evalEval (mh j).left (enumVertical W val) ≠ 0 := by
    intro j hj h0
    have hmem : (T' - ((j : ℤ) • P' + Z₀) : W.Point) ∈ Dv := by
      rw [← meq j hj]
      exact mem_of_evalEval_eq_zero hvspan (mh j) h0
    have hmem2 : ((j : ℤ) • P' + Z₀ : W.Point) ∈ Dv.map (fun S => T' - S) := by
      have h2 : (T' - (T' - ((j : ℤ) • P' + Z₀)) : W.Point) ∈ Dv.map (fun S => T' - S) :=
        Multiset.mem_map_of_mem _ hmem
      rwa [sub_sub_cancel] at h2
    exact hgood j hj _ (hbmem _ (Or.inr (Or.inr (Or.inr (Or.inr hmem2))))) rfl
  -- ── STEP 2: `Θ(Y) = ∏_{j<p} g_P(Y ⊖ jP')` is constant
  have hκex : ∀ j : ℕ, ∃ (x y : W.FunctionField) (h : (curveK W).Nonsingular x y),
      constPoint W (-((j : ℤ) • P')) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some x y h :=
    fun j => exists_translate_some hΔ _
  choose kx ky kh kpt using hκex
  have htr : ∀ (z : W.CoordinateRing), z ≠ 0 → ∀ D : Multiset W.Point,
      Ideal.span {z} = (D.map (pointIdeal W)).prod → ∀ j : ℕ,
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) (kh j).left z) *
        (pointIdeal' W ((j : ℤ) • P') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ Multiset.card D =
      (D.map fun R => (pointIdeal' W (R + (j : ℤ) • P') :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
    intro z hz D hD j
    have h := spanSingleton_pointEval_translate hΔ (kpt j) hz hD
    rw [neg_neg] at h
    refine h.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun R _ => ?_))
    have hRe : R - -((j : ℤ) • P') = R + (j : ℤ) • P' := by abel
    rw [hRe]
  have hspanprod : ∀ (n : ℕ) (f : ℕ → W.FunctionField),
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ (∏ j ∈ Finset.range n, f j) =
        ∏ j ∈ Finset.range n,
          FractionalIdeal.spanSingleton W.CoordinateRing⁰ (f j) := by
    intro n f
    induction n with
    | zero => simp [FractionalIdeal.spanSingleton_one]
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← ih,
        FractionalIdeal.spanSingleton_mul_spanSingleton]
  have hΦ : ∀ (n : ℕ) (M : ℕ → Multiset W.Point),
      (((∑ j ∈ Finset.range n, M j).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) =
        ∏ j ∈ Finset.range n, ((M j).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
    intro n M
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ, ← ih, Multiset.map_add,
        Multiset.prod_add]
  have hconv : ∀ (D : Multiset W.Point) (j : ℕ),
      (D.map fun R => (pointIdeal' W (R + (j : ℤ) • P') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
        (((D.map fun R => R + (j : ℤ) • P').map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField))).prod := by
    intro D j
    rw [Multiset.map_map]
    rfl
  -- the multiset telescope `⋃_{j<p}(D_b ⊕ jP') = ⋃_{j<p}(D_v ⊕ jP')`
  have hn : (Finset.univ.val.map fun i => -val i) =
      Finset.univ.val.map fun i => val i :=
    map_neg_eq (p := p) hval_inj hval_tor hval_surj
  have hAm : ∀ S : W.Point, (Finset.univ.val.map fun i => S - val i) =
      Finset.univ.val.map fun i => S + val i := by
    intro S
    have h2 := congrArg (Multiset.map fun R : W.Point => S + R) hn
    simp only [Multiset.map_map, Function.comp_apply] at h2
    refine Eq.trans ?_ h2
    exact Multiset.map_congr rfl fun i _ => by abel
  have hDbtel : ∀ j : ℕ, (Db.map fun R => R + (j : ℤ) • P') =
      (Finset.univ.val.map fun i => ((j + 1 : ℕ) : ℤ) • P' + val i) +
        (Finset.univ.val.map fun i => ((j : ℕ) : ℤ) • P' + val i) := by
    intro j
    rw [hDb, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 1
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
      push_cast
      rw [add_smul, one_smul]
      abel
    · refine Eq.trans (Multiset.map_congr rfl fun i _ => ?_) (hAm ((j : ℤ) • P'))
      simp only [Function.comp_apply]
      abel
  have hDvtel : ∀ j : ℕ, (Dv.map fun R => R + (j : ℤ) • P') =
      (Finset.univ.val.map fun i => ((j : ℕ) : ℤ) • P' + val i) +
        (Finset.univ.val.map fun i => ((j : ℕ) : ℤ) • P' + val i) := by
    intro j
    rw [hDv, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 1
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp_apply]
      abel
    · refine Eq.trans (Multiset.map_congr rfl fun i _ => ?_) (hAm ((j : ℤ) • P'))
      simp only [Function.comp_apply]
      abel
  have htelsum : ∀ n : ℕ,
      (Finset.univ.val.map fun i => ((0 : ℕ) : ℤ) • P' + val i) +
          ∑ j ∈ Finset.range n,
            (Finset.univ.val.map fun i => ((j + 1 : ℕ) : ℤ) • P' + val i) =
        (∑ j ∈ Finset.range n,
            (Finset.univ.val.map fun i => ((j : ℕ) : ℤ) • P' + val i)) +
          (Finset.univ.val.map fun i => ((n : ℕ) : ℤ) • P' + val i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc, ih]
  have hA0 : (Finset.univ.val.map fun i => ((0 : ℕ) : ℤ) • P' + val i) =
      Finset.univ.val.map fun i => val i :=
    Multiset.map_congr rfl fun i _ => by simp
  have hApp : (Finset.univ.val.map fun i => ((p : ℕ) : ℤ) • P' + val i) =
      Finset.univ.val.map fun i => val i :=
    map_add_torsion_eq (p := p) hval_inj hval_tor hval_surj hPtor
  have hAp0 : (Finset.univ.val.map fun i => ((p : ℕ) : ℤ) • P' + val i) =
      (Finset.univ.val.map fun i => ((0 : ℕ) : ℤ) • P' + val i) := by
    rw [hApp, hA0]
  have hshift : (∑ j ∈ Finset.range p,
        (Finset.univ.val.map fun i => ((j + 1 : ℕ) : ℤ) • P' + val i)) =
      ∑ j ∈ Finset.range p,
        (Finset.univ.val.map fun i => ((j : ℕ) : ℤ) • P' + val i) := by
    have h := htelsum p
    rw [hAp0] at h
    exact add_left_cancel (h.trans (add_comm _ _))
  have hsumtel : (∑ j ∈ Finset.range p, Db.map fun R => R + (j : ℤ) • P') =
      ∑ j ∈ Finset.range p, Dv.map fun R => R + (j : ℤ) • P' := by
    simp only [hDbtel, hDvtel]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hshift]
  have hNcard : Multiset.card Db = Multiset.card Dv := by
    rw [hDb, hDv]; simp
  have htrb : ∀ j : ℕ,
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) (kh j).left b) *
        (pointIdeal' W ((j : ℤ) • P') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ Multiset.card Dv =
      (Db.map fun R => (pointIdeal' W (R + (j : ℤ) • P') :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
    intro j
    rw [← hNcard]
    exact htr b hb Db hbspan j
  have hunit : IsUnit (∏ j ∈ Finset.range p,
      ((pointIdeal' W ((j : ℤ) • P') :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ Multiset.card Dv)) :=
    Finset.prod_induction _ _ (fun _ _ hx hy => hx.mul hy) isUnit_one
      (fun j _ => (pointIdeal' W ((j : ℤ) • P')).isUnit.pow _)
  have hideal :
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (∏ j ∈ Finset.range p,
            pointEval (constHom W) (kh j).left (enumVertical W val)) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (∏ j ∈ Finset.range p, pointEval (constHom W) (kh j).left b) := by
    refine hunit.mul_right_cancel ?_
    calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (∏ j ∈ Finset.range p,
              pointEval (constHom W) (kh j).left (enumVertical W val)) *
          ∏ j ∈ Finset.range p,
            ((pointIdeal' W ((j : ℤ) • P') :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ Multiset.card Dv)
        = ∏ j ∈ Finset.range p, (Dv.map fun R =>
            (pointIdeal' W (R + (j : ℤ) • P') :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
          rw [hspanprod, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun j _ => htr _ hv0 Dv hvspan j
      _ = ∏ j ∈ Finset.range p, (Db.map fun R =>
            (pointIdeal' W (R + (j : ℤ) • P') :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
          simp only [hconv]
          rw [← hΦ p (fun j => Dv.map fun R => R + (j : ℤ) • P'),
            ← hΦ p (fun j => Db.map fun R => R + (j : ℤ) • P'), hsumtel]
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (∏ j ∈ Finset.range p, pointEval (constHom W) (kh j).left b) *
          ∏ j ∈ Finset.range p,
            ((pointIdeal' W ((j : ℤ) • P') :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                Multiset.card Dv) := by
          rw [hspanprod, ← Finset.prod_mul_distrib]
          exact (Finset.prod_congr rfl fun j _ => htrb j).symm
  obtain ⟨zu, hzu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hideal
  obtain ⟨θ, -, hθ⟩ := coordinateRing_isUnit_eq_const zu.isUnit
  have hgenΘ : (∏ j ∈ Finset.range p, pointEval (constHom W) (kh j).left b) =
      constHom W θ * ∏ j ∈ Finset.range p,
        pointEval (constHom W) (kh j).left (enumVertical W val) := by
    rw [← hzu, Units.smul_def, hθ, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C θ))) = constHom W θ from rfl]
  -- reading the generic `Θ` identity at a point
  have hEprod : ∀ {xX yX : F} (hX : W.Nonsingular xX yX)
      (f : ℕ → W.FunctionField) (g : ℕ → F) (n : ℕ),
      (∀ j, j < n → EvalsTo hX.left (f j) (g j)) →
      EvalsTo hX.left (∏ j ∈ Finset.range n, f j) (∏ j ∈ Finset.range n, g j) := by
    intro xX yX hX f g n
    induction n with
    | zero => intro _; simpa using evalsTo_one hX.left
    | succ n ih =>
      intro h
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact (ih fun j hj => h j (Nat.lt_succ_of_lt hj)).mul (h n (Nat.lt_succ_self n))
  have hkpt' : ∀ j : ℕ, constPoint W (-((j : ℤ) • P')) + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some (kx j) (ky j) (kh j) := by
    intro j
    rw [one_zsmul]
    exact kpt j
  have hreadΘ : ∀ {xX yX : F} (hX : W.Nonsingular xX yX)
      (fx fy : ℕ → F) (fh : ∀ j, W.Nonsingular (fx j) (fy j)),
      (∀ j, j < p → (WeierstrassCurve.Affine.Point.some (fx j) (fy j) (fh j) :
          W.Point) =
        -((j : ℤ) • P') + (WeierstrassCurve.Affine.Point.some xX yX hX : W.Point)) →
      (∏ j ∈ Finset.range p, AdjoinRoot.evalEval (fh j).left b) =
        θ * ∏ j ∈ Finset.range p,
          AdjoinRoot.evalEval (fh j).left (enumVertical W val) := by
    intro xX yX hX fx fy fh hfeq
    have hfeq' : ∀ j, j < p →
        (WeierstrassCurve.Affine.Point.some (fx j) (fy j) (fh j) : W.Point) =
          -((j : ℤ) • P') +
            (1 : ℤ) • (WeierstrassCurve.Affine.Point.some xX yX hX : W.Point) := by
      intro j hj
      rw [one_zsmul]
      exact hfeq j hj
    have hEb : EvalsTo hX.left
        (∏ j ∈ Finset.range p, pointEval (constHom W) (kh j).left b)
        (∏ j ∈ Finset.range p, AdjoinRoot.evalEval (fh j).left b) :=
      hEprod hX _ _ p fun j hj =>
        exists_pointEval_specialization hΔ (1 : ℤ) (hkpt' j) hX (fh j) (hfeq' j hj) b
    have hEv : EvalsTo hX.left
        (∏ j ∈ Finset.range p,
          pointEval (constHom W) (kh j).left (enumVertical W val))
        (∏ j ∈ Finset.range p,
          AdjoinRoot.evalEval (fh j).left (enumVertical W val)) :=
      hEprod hX _ _ p fun j hj =>
        exists_pointEval_specialization hΔ (1 : ℤ) (hkpt' j) hX (fh j) (hfeq' j hj)
          (enumVertical W val)
    have hR := (evalsTo_constHom hX.left θ).mul hEv
    rw [← hgenΘ] at hR
    exact hEb.unique hR
  -- ── STEP 3: multiply step 1 over the `p` translates `X ⊕ jP'`
  have hstepγ : ∀ n : ℕ, n < p →
      AdjoinRoot.evalEval (mh n).left b * AdjoinRoot.evalEval (zh n).left a *
          AdjoinRoot.evalEval (nh n).left (enumVertical W val) *
          AdjoinRoot.evalEval (zh (n + 1)).left (enumVertical W val) =
        γ * (AdjoinRoot.evalEval (nh n).left b *
          AdjoinRoot.evalEval (zh (n + 1)).left a *
          AdjoinRoot.evalEval (mh n).left (enumVertical W val) *
          AdjoinRoot.evalEval (zh n).left (enumVertical W val)) := by
    intro n hnp
    refine hγ (zx n) (zy n) (zh n) (mx n) (my n) (mh n) (nx n) (ny n) (nh n)
      (zx (n + 1)) (zy (n + 1)) (zh (n + 1)) ?_ ?_ ?_
    · rw [meq n hnp.le, zeq n hnp.le]
    · rw [neq n hnp.le, zeq n hnp.le]
    · rw [zeq (n + 1) hnp, zeq n hnp.le]
      push_cast
      rw [add_smul, one_smul]
      abel
  have hInv : ∀ n : ℕ, n ≤ p →
      (∏ j ∈ Finset.range n, (AdjoinRoot.evalEval (mh j).left b *
          AdjoinRoot.evalEval (nh j).left (enumVertical W val))) *
        (AdjoinRoot.evalEval (zh 0).left a *
          AdjoinRoot.evalEval (zh n).left (enumVertical W val)) =
      γ ^ n * ((∏ j ∈ Finset.range n, (AdjoinRoot.evalEval (nh j).left b *
          AdjoinRoot.evalEval (mh j).left (enumVertical W val))) *
        (AdjoinRoot.evalEval (zh n).left a *
          AdjoinRoot.evalEval (zh 0).left (enumVertical W val))) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hnp : n < p := hn
      have hE := ih hnp.le
      have hS := hstepγ n hnp
      refine mul_left_cancel₀ (mul_ne_zero (haZ n hnp.le) (hvZ n hnp.le)) ?_
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
      linear_combination
        (AdjoinRoot.evalEval (mh n).left b *
            AdjoinRoot.evalEval (nh n).left (enumVertical W val) *
            AdjoinRoot.evalEval (zh (n + 1)).left (enumVertical W val) *
            AdjoinRoot.evalEval (zh n).left a) * hE +
        (γ ^ n * (∏ j ∈ Finset.range n, (AdjoinRoot.evalEval (nh j).left b *
            AdjoinRoot.evalEval (mh j).left (enumVertical W val))) *
            AdjoinRoot.evalEval (zh n).left a *
            AdjoinRoot.evalEval (zh 0).left (enumVertical W val)) * hS
  -- ── the two `Θ` readings and the conclusion
  have hΘm : (∏ j ∈ Finset.range p, AdjoinRoot.evalEval (mh j).left b) =
      θ * ∏ j ∈ Finset.range p,
        AdjoinRoot.evalEval (mh j).left (enumVertical W val) := by
    refine hreadΘ (mh 0) mx my mh ?_
    intro j hj
    rw [meq j hj.le, meq 0 (Nat.zero_le p)]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    abel
  have hΘn : (∏ j ∈ Finset.range p, AdjoinRoot.evalEval (nh j).left b) =
      θ * ∏ j ∈ Finset.range p,
        AdjoinRoot.evalEval (nh j).left (enumVertical W val) := by
    refine hreadΘ (nh 0) nx ny nh ?_
    intro j hj
    rw [neq j hj.le, neq 0 (Nat.zero_le p)]
    simp only [Nat.cast_zero, zero_smul, zero_add]
    abel
  have hLR : (∏ j ∈ Finset.range p, (AdjoinRoot.evalEval (mh j).left b *
        AdjoinRoot.evalEval (nh j).left (enumVertical W val))) =
      ∏ j ∈ Finset.range p, (AdjoinRoot.evalEval (nh j).left b *
        AdjoinRoot.evalEval (mh j).left (enumVertical W val)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hΘm, hΘn]
    ring
  have hRpne : (∏ j ∈ Finset.range p, (AdjoinRoot.evalEval (nh j).left b *
      AdjoinRoot.evalEval (mh j).left (enumVertical W val))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      mul_ne_zero (hbN j (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (hvM j (Nat.le_of_lt (Finset.mem_range.mp hj)))
  have hfin := hInv p le_rfl
  have hcz : AdjoinRoot.evalEval (zh p).left a *
      AdjoinRoot.evalEval (zh 0).left (enumVertical W val) =
    c * (AdjoinRoot.evalEval (zh p).left (enumVertical W val) *
      AdjoinRoot.evalEval (zh 0).left a) := by
    refine hc (zx 0) (zy 0) (zh 0) (zx p) (zy p) (zh p) ?_
    rw [zeq p le_rfl, zeq 0 (Nat.zero_le p)]
    simp only [Nat.cast_zero, zero_smul, zero_add]
  rw [hcz, hLR] at hfin
  refine mul_right_cancel₀ (mul_ne_zero hRpne
    (mul_ne_zero (haZ 0 (Nat.zero_le p)) (hvZ p le_rfl))) ?_
  linear_combination -hfin

omit [Fact (1 < p)] in
/-- **Stage B, leaf 3a-i (PROVEN, sorry-free since 2026-07-26): the
CROSS-RATIO CONSTANT `γ` of the two level-`p²` Miller functions, and its
`p`-th power.**

Notation as in `exists_millerValue_alternating` below: `g = a/v`,
`g_P = b/v` with `v = enumVertical W val = ∏_κ (X − x_κ)`, so that
`div g = S(T') − S(0)` and `div g_P = S(P') − S(0)` where
`S(A) := Σ_{κ ∈ E[p]} (A ⊕ κ) = [p]^*(([p]A))`; and `M₁ = T' ⊖ U`,
`M₂ = ⊖U`, `V = P' ⊕ U`, `P⊕U = p•P' ⊕ U`.

The two conclusions are, written multiplicatively,

* `γ = [g_P(M₁)·g(U)] / [g_P(M₂)·g(V)]`  (first conjunct, denominators
  cleared), i.e. `γ` is the value at `X = U` of
  `Ξ(X) := [g_P(T' ⊖ X)·g(X)] / [g_P(⊖X)·g(P' ⊕ X)]`;
* `γ^p = c^{−1}` where `c = g(P ⊕ U)/g(U)` is the translation character
  (second conjunct, denominators cleared).

**Proof (elementary; NO Weil reciprocity — see the dead-end analysis in
the docstring of `exists_millerValue_alternating`).  PROVEN 2026-07-25
over the single leaf `millerValue_crossRatio_pow_mul_translationChar`
(steps 2–3), which was itself PROVEN 2026-07-26 — so this subtree is now
sorry-free.**

* Step 1 — `Ξ` has trivial divisor, hence IS a constant `γ` — is PROVEN
  above as `exists_millerValue_crossRatio_read`.  Its divisor
  cancellation is `crossRatio_divisor_eq` (both sides reduce to
  `A_{T'−P'} + 2·A_{T'} + 3·A_0 + 2·A_{−P'}` for `A_S := Σ_κ (S ⊕ κ)`;
  the MIXED signs `T' ⊖ X` against `P' ⊕ X` are exactly what makes it
  cancel, and are why the pairing is antisymmetric).  The two divisor
  transports it needs are `spanSingleton_pointEval_translate` (`m = 1`)
  and the new `spanSingleton_pointEval_translate_neg` (`m = −1`), the
  latter built here from the hyperelliptic involution `involHom` via
  `pointEval_involHom` and `map_involHom_pointIdeal`; the reading at a
  concrete point is `exists_pointEval_specialization` at
  `(Q, m) = (T', −1)`, `(0, −1)` and `(P', 1)`.  Read at `X = U` it IS
  the first conjunct.
* The translation character `c` in generic, POINT-INDEPENDENT form is
  PROVEN above as `exists_millerValue_translationChar` (the `hgen`/
  `hstep` half of `millerValue_translationChar_pow`).
* Steps 2–3 — `Θ(Y) := ∏_{j<p} g_P(Y ⊖ jP')` has telescoping divisor
  `S(p•P') − S(0) = 0` and is therefore constant, and multiplying step 1
  over the `p` translates `X ⊕ jP'` cancels the two `Θ`s and leaves
  `γ^p·c = 1` — are `millerValue_crossRatio_pow_mul_translationChar`
  above, PROVEN 2026-07-26; its docstring carries the plan and the
  implementation notes.  Given it, the SECOND CONJUNCT is three
  lines of field algebra against `hc` read at `(U, P ⊕ U)`: both `γ`
  and `c` are constants, so the identity transports from wherever it is
  proven to `U`.

FAITHFULNESS AUDIT (corrected 2026-07-25 by the proof).  The earlier
note here claimed that "all ten nonvanishing hypotheses are needed: the
conclusion is in cleared polynomial form, so a single vanishing factor
would falsify it".  That is BACKWARDS.  Precisely BECAUSE the conclusion
is cleared of denominators it also holds where the factors vanish, and
the proof uses NONE of `hp`, `hcard`, `hQtor` or the ten nonvanishing
hypotheses; they are underscore-prefixed below so that the redundancy is
mechanically visible, and kept only because the consumer
`exists_millerRatio_eval_translationChar` supplies them in this shape.
What IS load-bearing is that `M₁`, `M₂`, `V` and `P⊕U` be affine points
with the stated group-law descriptions — `hM1eq`, `hM2eq`, `hVeq`,
`hPUeq` — together with `hPtor` (which makes the step-2 telescope
close). -/
theorem exists_millerValue_crossRatio_const {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (_hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (_hcard : Fintype.card ι = p ^ 2)
    {a b : W.CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hbspan : Ideal.span {b} =
      ((((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (_hQtor : (p : ℤ) • ((p : ℤ) • T') = 0)
    (hPtor : (p : ℤ) • ((p : ℤ) • P') = 0)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xV yV : F} (hV : W.Nonsingular xV yV)
    {xM1 yM1 : F} (hM1 : W.Nonsingular xM1 yM1)
    {xM2 yM2 : F} (hM2 : W.Nonsingular xM2 yM2)
    {xPU yPU : F} (hPU : W.Nonsingular xPU yPU)
    (hVeq : (WeierstrassCurve.Affine.Point.some xV yV hV : W.Point) =
      P' + WeierstrassCurve.Affine.Point.some xU yU hU)
    (hM1eq : (WeierstrassCurve.Affine.Point.some xM1 yM1 hM1 : W.Point) =
      T' - WeierstrassCurve.Affine.Point.some xU yU hU)
    (hM2eq : (WeierstrassCurve.Affine.Point.some xM2 yM2 hM2 : W.Point) =
      -(WeierstrassCurve.Affine.Point.some xU yU hU : W.Point))
    (hPUeq : (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) =
      (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some xU yU hU)
    (_hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (_hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0)
    (_hVa : AdjoinRoot.evalEval hV.left a ≠ 0)
    (_hVv : AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0)
    (_hM1b : AdjoinRoot.evalEval hM1.left b ≠ 0)
    (_hM1v : AdjoinRoot.evalEval hM1.left (enumVertical W val) ≠ 0)
    (_hM2b : AdjoinRoot.evalEval hM2.left b ≠ 0)
    (_hM2v : AdjoinRoot.evalEval hM2.left (enumVertical W val) ≠ 0)
    (_hPUa : AdjoinRoot.evalEval hPU.left a ≠ 0)
    (_hPUv : AdjoinRoot.evalEval hPU.left (enumVertical W val) ≠ 0) :
    ∃ γ : F,
      AdjoinRoot.evalEval hM1.left b * AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval hM2.left (enumVertical W val) *
          AdjoinRoot.evalEval hV.left (enumVertical W val) =
        γ * (AdjoinRoot.evalEval hM2.left b * AdjoinRoot.evalEval hV.left a *
          AdjoinRoot.evalEval hM1.left (enumVertical W val) *
          AdjoinRoot.evalEval hU.left (enumVertical W val)) ∧
      γ ^ p * (AdjoinRoot.evalEval hPU.left a *
          AdjoinRoot.evalEval hU.left (enumVertical W val)) =
        AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval hPU.left (enumVertical W val) := by
  obtain ⟨γ, hγ⟩ := exists_millerValue_crossRatio_read hΔ hval_inj hval_tor
    hval_surj ha hb hspan hbspan
  obtain ⟨c, hc⟩ := exists_millerValue_translationChar hΔ hval_inj hval_tor
    hval_surj ha hspan hPtor
  refine ⟨γ, hγ xU yU hU xM1 yM1 hM1 xM2 yM2 hM2 xV yV hV hM1eq hM2eq hVeq, ?_⟩
  have hcγ : γ ^ p * c = 1 :=
    millerValue_crossRatio_pow_mul_translationChar hΔ hval_inj hval_tor
      hval_surj ha hb hspan hbspan hPtor hγ hc
  have hstep := hc xU yU hU xPU yPU hPU hPUeq
  calc γ ^ p * (AdjoinRoot.evalEval hPU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val))
      = γ ^ p * (c * (AdjoinRoot.evalEval hPU.left (enumVertical W val) *
          AdjoinRoot.evalEval hU.left a)) := by rw [hstep]
    _ = (γ ^ p * c) * (AdjoinRoot.evalEval hPU.left (enumVertical W val) *
          AdjoinRoot.evalEval hU.left a) := by ring
    _ = AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval hPU.left (enumVertical W val) := by
        rw [hcγ]; ring

omit [Fact (1 < p)] in
/-- **Stage B, leaf 3a-ii (PROVEN): the translation character of `g` at a
`p`-torsion point is a `p`-th root of unity**, in cleared form.

With `g = a/v` (`div g = S(T') − S(0)`, `S(A) := Σ_{κ ∈ E[p]}(A ⊕ κ)`)
and `P := p•P' ∈ E[p]` (`hPtor`), the statement is `c^p = 1` for
`c = g(P ⊕ U)/g(U) = [a(P⊕U)·v(U)] / [a(U)·v(P⊕U)]`, written without
division as the equality of two `p`-th powers below.

**Proof.**  `g ∘ τ_P / g` has trivial divisor:
`div = S(T' ⊖ P) − S(⊖P) − S(T') + S(0) = 0`, because translation by the
`p`-torsion point `P` permutes the enumeration `val` of `E[p]`
(`map_add_torsion_eq`), so `S(A ⊖ P) = S(A)`.  Hence `g ∘ τ_P = c·g` for
a constant `c` — this is `spanSingleton_pointEval_translate` applied to
`a` and to `v` at `constPoint P + taut`, the two `I'_{⊖P}^{2·card ι}`
factors cancelling between numerator and denominator, followed by
`coordinateRing_isUnit_eq_const`.  Reading it at the `p` points
`jP ⊕ U`, `j = 0,…,p−1` (one application of
`exists_pointEval_specialization` at `(Q, m) = (P, 1)` each) and
multiplying telescopes to `c^p·g(U) = g(p•P ⊕ U) = g(U)`.

All `p` readings are legitimate, and this needs no hypothesis beyond
`hUa`/`hUv`: `a(jP ⊕ U) = 0` iff `jP ⊕ U` lies in the support of
`div a`, which is `E[p]`-translation invariant, so iff `a(U) = 0`; same
for `v`; and `jP ⊕ U = O` would force `U ∈ E[p]`, i.e. `v(U) = 0`.
PROVEN 2026-07-25 exactly along that route. -/
theorem millerValue_translationChar_pow {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hPtor : (p : ℤ) • ((p : ℤ) • P') = 0)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xPU yPU : F} (hPU : W.Nonsingular xPU yPU)
    (hPUeq : (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) =
      (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some xU yU hU)
    (hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0) :
    (AdjoinRoot.evalEval hPU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ p =
      (AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hPU.left (enumVertical W val)) ^ p := by
  classical
  have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
  have hPt : (p : ℤ) • ((p : ℤ) • P' : W.Point) = 0 := hPtor
  -- ── multiset translation invariance under a `p`-torsion shift
  have hmap1 : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => val i - T) =
        Finset.univ.val.map fun i => val i := by
    intro T hT
    have h := map_add_torsion_eq (W := W) hval_inj hval_tor hval_surj
      (T := -T) (by rw [smul_neg, hT, neg_zero])
    rw [← h]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hmap2 : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => -val i - T) =
        Finset.univ.val.map fun i => -val i := by
    intro T hT
    have h := map_add_torsion_eq (W := W) hval_inj hval_tor hval_surj (T := T) hT
    have h2 := congrArg (Multiset.map (fun R : W.Point => -R)) h
    simp only [Multiset.map_map, Function.comp_apply] at h2
    rw [← h2]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hmap3 : ∀ (A T : W.Point), (p : ℤ) • T = 0 →
      (Finset.univ.val.map fun i => A + val i - T) =
        Finset.univ.val.map fun i => A + val i := by
    intro A T hT
    have h2 := congrArg (Multiset.map (fun R : W.Point => A + R)) (hmap1 T hT)
    simp only [Multiset.map_map, Function.comp_apply] at h2
    rw [← h2]
    exact Multiset.map_congr rfl fun i _ => by abel
  have hDv : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - T) =
      ((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i) := by
    intro T hT
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_apply]
    rw [hmap1 T hT, hmap2 T hT]
  have hDa : ∀ T : W.Point, (p : ℤ) • T = 0 →
      (((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i).map fun R => R - T) =
      ((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i) := by
    intro T hT
    simp only [Multiset.map_add, Multiset.map_map, Function.comp_apply]
    rw [hmap3 T' T hT, hmap2 T hT]
  -- ── `v` cannot vanish at a `p`-torsion translate of `U`
  have hvne : ∀ (x y : F) (h : W.Nonsingular x y) (T : W.Point), (p : ℤ) • T = 0 →
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        T + WeierstrassCurve.Affine.Point.some xU yU hU →
      AdjoinRoot.evalEval h.left (enumVertical W val) ≠ 0 := by
    intro x y h T hT heq h0
    have hmem := mem_of_evalEval_eq_zero (span_enumVertical (W := W) val) h h0
    have hmem2 : (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) ∈
        ((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i) := by
      rw [← hDv T hT]
      refine Multiset.mem_map.mpr ⟨_, hmem, ?_⟩
      rw [heq]; abel
    exact hUv (evalEval_eq_zero_of_mem (span_enumVertical (W := W) val) hU hmem2)
  -- ── `v` vanishes at every `p`-torsion point
  have hvtor : ∀ (x y : F) (h : W.Nonsingular x y),
      (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = 0 →
      AdjoinRoot.evalEval h.left (enumVertical W val) = 0 := by
    intro x y h htor
    obtain ⟨i, hi⟩ := hval_surj _ htor
    refine evalEval_eq_zero_of_mem (span_enumVertical (W := W) val) h ?_
    refine Multiset.mem_add.mpr (Or.inl ?_)
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, hi⟩
  have hmapcomp : ∀ (D : Multiset W.Point) (Q : W.Point),
      (D.map fun R => (pointIdeal' W (R - Q) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) =
        ((D.map fun R => R - Q).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
    intro D Q
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun _ _ => rfl
  -- ── the GENERIC character identity `g∘τ_P = c·g`, multiplied out
  obtain ⟨xκ, yκ, hκ, hptκ⟩ := exists_translate_some (W := W) hΔ ((p : ℤ) • P')
  obtain ⟨c, hgen⟩ : ∃ c : F,
      pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        constHom W c * (pointEval (constHom W) hκ.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField a) := by
    have hCa := spanSingleton_pointEval_translate (W := W) hΔ hptκ ha hspan
    have hCv := spanSingleton_pointEval_translate (W := W) hΔ hptκ hv0
      (span_enumVertical (W := W) val)
    rw [hmapcomp _ _, hDa _ hPt, prod_coe_pointIdeal'_eq_spanSingleton hspan] at hCa
    rw [hmapcomp _ _, hDv _ hPt,
      prod_coe_pointIdeal'_eq_spanSingleton (span_enumVertical (W := W) val)] at hCv
    have hu : IsUnit ((pointIdeal' W (-((p : ℤ) • P')) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
          Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
            Finset.univ.val.map fun i => -val i)) :=
      (pointIdeal' W _).isUnit.pow _
    have hcard2 : Multiset.card ((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i) =
      Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i) := by
      simp
    rw [hcard2] at hCv
    have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hκ.left (enumVertical W val) *
            algebraMap W.CoordinateRing W.FunctionField a) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hκ.left a *
            algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
      simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton]
      refine hu.mul_right_cancel ?_
      calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) *
            (pointIdeal' W (-((p : ℤ) • P')) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
              Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i)
          = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left (enumVertical W val)) *
              (pointIdeal' W (-((p : ℤ) • P')) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                  Finset.univ.val.map fun i => -val i)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) := by ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField a) := by rw [hCv]
        _ = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a) *
              (pointIdeal' W (-((p : ℤ) • P')) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                  Finset.univ.val.map fun i => -val i)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
            rw [hCa]; ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
            (pointIdeal' W (-((p : ℤ) • P')) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
              Multiset.card ((Finset.univ.val.map fun i => T' + val i) +
                Finset.univ.val.map fun i => -val i) := by ring
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
    obtain ⟨cc, -, hcz⟩ := coordinateRing_isUnit_eq_const z.isUnit
    refine ⟨cc, ?_⟩
    rw [← hz, Units.smul_def, hcz, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C cc))) =
        constHom W cc from rfl]
  -- ── reading the generic identity at a point and its `P`-translate
  have hptκ' : constPoint W ((p : ℤ) • P') + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
    rw [one_zsmul]; exact hptκ
  have hstep : ∀ (x₁ y₁ : F) (h₁ : W.Nonsingular x₁ y₁) (x₂ y₂ : F)
      (h₂ : W.Nonsingular x₂ y₂),
      (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.Point) =
        (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ →
      AdjoinRoot.evalEval h₂.left a *
          AdjoinRoot.evalEval h₁.left (enumVertical W val) =
        c * (AdjoinRoot.evalEval h₂.left (enumVertical W val) *
          AdjoinRoot.evalEval h₁.left a) := by
    intro x₁ y₁ h₁ x₂ y₂ h₂ heq
    have heq' : (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.Point) =
        (p : ℤ) • P' + (1 : ℤ) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.Point) := by
      rw [one_zsmul]; exact heq
    have hEa : EvalsTo h₁.left (pointEval (constHom W) hκ.left a)
        (AdjoinRoot.evalEval h₂.left a) :=
      exists_pointEval_specialization hΔ (1 : ℤ) hptκ' h₁ h₂ heq' a
    have hEv : EvalsTo h₁.left (pointEval (constHom W) hκ.left (enumVertical W val))
        (AdjoinRoot.evalEval h₂.left (enumVertical W val)) :=
      exists_pointEval_specialization hΔ (1 : ℤ) hptκ' h₁ h₂ heq' (enumVertical W val)
    have hL := hEa.mul (evalsTo_algebraMap h₁.left (enumVertical W val))
    have hR := (evalsTo_constHom h₁.left c).mul
      (hEv.mul (evalsTo_algebraMap h₁.left a))
    rw [← hgen] at hR
    exact hL.unique hR
  -- ── the telescope: `g(n•P ⊕ U)/g(U) = c^n`
  have hchain : ∀ n : ℕ, ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        (n : ℤ) • ((p : ℤ) • P' : W.Point) +
          WeierstrassCurve.Affine.Point.some xU yU hU ∧
      AdjoinRoot.evalEval h.left a *
          AdjoinRoot.evalEval hU.left (enumVertical W val) =
        c ^ n * (AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval h.left (enumVertical W val)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨xU, yU, hU, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨x, y, h, hpt, hval⟩ := ih
      have hntor : (p : ℤ) • ((n : ℤ) • ((p : ℤ) • P' : W.Point)) = 0 := by
        rw [smul_comm, hPt, smul_zero]
      have hvn : AdjoinRoot.evalEval h.left (enumVertical W val) ≠ 0 :=
        hvne x y h _ hntor hpt
      -- the next point is affine
      obtain ⟨x', y', h', hpt'⟩ : ∃ (x' y' : F) (h' : W.Nonsingular x' y'),
          (WeierstrassCurve.Affine.Point.some x' y' h' : W.Point) =
            (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some x y h := by
        cases hc : ((p : ℤ) • P' + WeierstrassCurve.Affine.Point.some x y h : W.Point) with
        | zero =>
          exfalso
          have hxtor : (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = 0 := by
            have h1 : (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
                -((p : ℤ) • P') := by
              rw [eq_neg_iff_add_eq_zero, add_comm]; exact hc
            rw [h1, smul_neg, hPt, neg_zero]
          exact hvn (hvtor x y h hxtor)
        | some x' y' h' => exact ⟨x', y', h', rfl⟩
      refine ⟨x', y', h', ?_, ?_⟩
      · rw [hpt', hpt]
        push_cast
        rw [add_smul, one_smul]
        abel
      · have hs := hstep x y h x' y' h' hpt'
        have hvn' : AdjoinRoot.evalEval h'.left (enumVertical W val) ≠ 0 := by
          refine hvne x' y' h' ((n + 1 : ℤ) • ((p : ℤ) • P' : W.Point)) ?_ ?_
          · rw [smul_comm, hPt, smul_zero]
          · rw [hpt', hpt, add_smul, one_smul]; abel
        refine mul_left_cancel₀ hvn ?_
        rw [pow_succ]
        calc AdjoinRoot.evalEval h.left (enumVertical W val) *
              (AdjoinRoot.evalEval h'.left a *
                AdjoinRoot.evalEval hU.left (enumVertical W val))
            = (AdjoinRoot.evalEval h'.left a *
                AdjoinRoot.evalEval h.left (enumVertical W val)) *
              AdjoinRoot.evalEval hU.left (enumVertical W val) := by ring
          _ = c * (AdjoinRoot.evalEval h'.left (enumVertical W val) *
                AdjoinRoot.evalEval h.left a) *
              AdjoinRoot.evalEval hU.left (enumVertical W val) := by rw [hs]
          _ = c * AdjoinRoot.evalEval h'.left (enumVertical W val) *
              (AdjoinRoot.evalEval h.left a *
                AdjoinRoot.evalEval hU.left (enumVertical W val)) := by ring
          _ = c * AdjoinRoot.evalEval h'.left (enumVertical W val) *
              (c ^ n * (AdjoinRoot.evalEval hU.left a *
                AdjoinRoot.evalEval h.left (enumVertical W val))) := by rw [hval]
          _ = AdjoinRoot.evalEval h.left (enumVertical W val) *
              (c ^ n * c * (AdjoinRoot.evalEval hU.left a *
                AdjoinRoot.evalEval h'.left (enumVertical W val))) := by ring
  -- ── `c^p = 1`
  have hcp : c ^ p = 1 := by
    obtain ⟨x, y, h, hpt, hval⟩ := hchain p
    have hUeq : (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        WeierstrassCurve.Affine.Point.some xU yU hU := by
      rw [hpt, hPt, zero_add]
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hUeq
    obtain ⟨rfl, rfl⟩ := hUeq
    have hval' : AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val) =
      c ^ p * (AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val)) := hval
    have hne : AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0 :=
      mul_ne_zero hUa hUv
    refine mul_right_cancel₀ hne ?_
    rw [one_mul]
    linear_combination -hval'
  -- ── conclusion
  have hs := hstep xU yU hU xPU yPU hPU hPUeq
  calc (AdjoinRoot.evalEval hPU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ p
      = (c * (AdjoinRoot.evalEval hPU.left (enumVertical W val) *
          AdjoinRoot.evalEval hU.left a)) ^ p := by rw [hs]
    _ = c ^ p * (AdjoinRoot.evalEval hPU.left (enumVertical W val) *
          AdjoinRoot.evalEval hU.left a) ^ p := by rw [mul_pow]
    _ = (AdjoinRoot.evalEval hU.left a *
          AdjoinRoot.evalEval hPU.left (enumVertical W val)) ^ p := by
        rw [hcp, one_mul, mul_comm]


/-- **Stage B, leaf 3a (PROVEN over two divisor-telescope leaves): the
ALTERNATING LAW of the Weil pairing,
in Miller-value form.**  This is the one genuinely reciprocal statement
of Stage B; everything else in leaf 3 is transport and glue.

Setting `v = enumVertical W val = ∏_{κ ∈ E[p]} (X − x_κ)`, the two
hypotheses `hspan`/`hbspan` say that `g := a/v` and `g_P := b/v` are the
level-`p²` Miller functions of `Q := [p]T'` and `P := [p]P'`:
`div g = [p]^*((Q) − (O))`, `div g_P = [p]^*((P) − (O))` (both `a` and
`b` have divisor `Σ_κ (·⊕κ) + Σ_κ (⊖κ)`, and `div v = Σ_κ (κ) + Σ_κ (⊖κ)`).
The hypotheses `hQtor`/`hPtor` say `Q, P ∈ E[p]`, which is what makes the
translation characters of `g` and `g_P` `p`-th roots of unity.  They are
not extra assumptions: `hspan` with `a ≠ 0` already FORCES `[p²]T' = 0`,
since a point-ideal product is principal exactly when its multiset sums
to `O` (`sum_eq_zero_of_span_eq_prod_pointIdeal` above) and
`Σ_κ (T'⊕κ) + Σ_κ (⊖κ) = p²·T'`; the consumer discharges them that way,
and they are stated here so that a prover has them without redoing the
class-group argument.

Written multiplicatively (all ten evaluations are nonzero by the
hypotheses, so the division is legitimate), the conclusion is

`[g_P(M₁)/g_P(M₂)]^p = [g(V)/g(U)]^p · [g(P⊕U)/g(U)]^e`,  `e ∈ {1, p−1}`,

for `M₂ = ⊖U`, `M₁ = T' ⊖ U`, `V = P' ⊕ U`.

**Why this is the alternating law.**  Since `g_P^p = μ·(f_P∘[p])` for a
constant `μ` and any `f_P` with `div f_P = p(P) − p(O)` (the two sides
have the same divisor), the left-hand side is
`f_P([p]M₁)/f_P([p]M₂) = f_P((Z⊕Q) − (Z))` with `Z := [p]M₂ = ⊖[p]U`;
and `[g(V)/g(U)]^p = f_Q((Wp⊕P) − (Wp))` with `Wp := [p]U`.  So with the
balanced divisors `D_Q := (Z⊕Q) − (Z) ∼ (Q) − (O)` and
`D_P := (Wp⊕P) − (Wp) ∼ (P) − (O)` the conclusion reads

`f_P(D_Q) / f_Q(D_P) = [g(P⊕U)/g(U)]^e = e_p(P,Q)^e`,

i.e. the cross-ratio definition of the Weil pairing agrees with the
translation-character definition `e_p(P,Q) = g(X⊕P)/g(X)` up to the
orientation ambiguity `e ∈ {1, p−1}` (`c` versus `c^{-1} = c^{p-1}`,
since `c^p = 1`).  Equivalently `e_p(P,Q)·e_p(Q,P) = 1`.  See Silverman
*AEC* III.8.1 and Ex. 3.16(c), and Howe, *The Weil pairing and the
Hilbert symbol*.

**The hypothesis `hM2eq : M₂ = ⊖U` is not needed for truth** — the
cross-ratio `f_P(D_Q)/f_Q(D_P)` is independent of the auxiliary points
`Z`, `Wp` — but it is the shape the consumer
`exists_millerRatio_eval_translationChar` supplies, and keeping it
avoids a needless generalisation.

**WEIL RECIPROCITY IS NOT NEEDED — and is a DEAD END here** (2026-07-25,
correcting the earlier note on this leaf, which asked a future owner to
build the tame-symbol product formula).  Every reciprocity pairing among
the functions available at this cut is *degenerate*, i.e. gives an
identity between `p`-th powers, which is exactly the information the
conclusion does not carry (`e_p(P,Q)^p = 1`, so a relation among `p`-th
powers says nothing about `e`).  Writing `S(A) := Σ_{κ ∈ E[p]} (A ⊕ κ) =
[p]^*(([p]A))` for the fibre divisor, so that `div g = S(T') − S(0)` and
`div g_P = S(P') − S(0)`, the four candidates all collapse:

* `f_P` against `g`: `∏_κ f_P(X ⊕ κ)` is CONSTANT, because
  `div ∏_κ f_P(·⊕κ) = p·(Σ_κ (P ⊖ κ) − Σ_κ (⊖κ)) = 0` (`P ∈ E[p]`, so
  `κ ↦ P ⊖ κ` permutes `E[p]`); and `g(div f_P) = c^p = 1`.  Both sides `1`.
* `g_P` against `g` (both level `p²`): the translation character makes
  `∏_κ g_P(X ⊕ κ) = (∏_κ e_p(κ,P))·g_P(X)^{p²}`, and reciprocity returns
  `[g_P(M₁)/g_P(M₂)]^{p²} = [g(V)/g(U)]^{p²}` — the `p`-th POWER of the
  goal, hence vacuous.
* `g_P` against `f_Q`, and `f_P` against `f_Q` (via tame symbols at
  `P`, `Q`, `O`): same, `p`-th powers throughout.

The content is therefore *not* reciprocal at all.  It is the following
**elementary divisor telescope**, which uses only "trivial divisor ⟹
constant" (`coordinateRing_isUnit_eq_const`) and the two transport
bricks already in `WeilPairingDescent.lean`.  Put

  `Ξ(X) := [g_P(T' ⊖ X)·g(X)] / [g_P(⊖X)·g(P' ⊕ X)]`.

1. **`Ξ` is CONSTANT.**  Its divisor is
   `[S(T'⊖P') − S(T')] + [S(T') − S(0)] − [S(⊖P') − S(0)]
      − [S(T'⊖P') − S(⊖P')] = 0`
   (using `S(A) ⊕ B = S(A⊕B)`, `⊖S(A) = S(⊖A)` — the enumeration `val`
   of `E[p]` is closed under negation).  Call the constant `γ`; read at
   `X = U` it is exactly `g_P(M₁)g(U)/(g_P(M₂)g(V))`, i.e. the
   cross-ratio whose `p`-th power the conclusion asks about.  Note the
   MIXED signs `M₁ = T' ⊖ U` against `V = P' ⊕ U`: they are what makes
   this divisor cancel, and they are why the pairing is antisymmetric.
2. **`Θ(Y) := ∏_{j<p} g_P(Y ⊖ jP')` is CONSTANT.**  Its divisor
   TELESCOPES: `Σ_{j<p} [S((j+1)P') − S(jP')] = S(p•P') − S(0) = S(P) −
   S(0) = 0`, the last step because `P = p•P' ∈ E[p]` translates the
   enumeration into itself (`map_add_torsion_eq`).  **This is the one
   place the level-`p²` structure enters**, and it is what supplies the
   missing `p`-th root.
3. **The telescope.**  Apply 1 at `X ⊕ jP'`, `j = 0,…,p−1`, and multiply:
   `Θ(T'⊖X)·∏_j g(X⊕jP') = γ^p·Θ(⊖X)·∏_j g(X⊕(j+1)P')`.
   By 2 the two `Θ`s cancel, and the two `g`-products differ exactly by
   `g(X ⊕ p•P')/g(X) = g(P ⊕ X)/g(X) = c`.  Hence `γ^p·c = 1`.
4. **`c^p = 1`** (the translation character of `g` at the `p`-torsion
   point `P`): `div(g∘τ_P / g) = S(T'⊖P) − S(⊖P) − S(T') + S(0) = 0`
   again by `map_add_torsion_eq`, so `g∘τ_P = c·g`; iterating `p` times
   at `U` (all of `U, P⊕U, …, (p−1)P⊕U` are off `div g` because the
   support is `E[p]`-translation invariant) gives `c^p = 1`.

Then `γ^p = c^{−1} = c^{p−1}`, which is the conclusion with `e = p − 1`.

STAGING (2026-07-25): DECOMPOSED over the two leaves below,
`exists_millerValue_crossRatio_const` (steps 1–3, packaged as the two
properties of `γ` read at `U`) and `millerValue_translationChar_pow`
(step 4, in cleared form — PROVEN here 2026-07-25).  Everything between
them is PROVEN glue: pure field algebra, cancelling
`β := a(P⊕U)·v(U) ≠ 0`.

STATUS UPDATE (2026-07-26): ALL FOUR STEPS ARE NOW PROVEN and this
subtree is sorry-free.  Step 1 (`Ξ` constant, the mixed-sign divisor
cancellation) is `exists_millerValue_crossRatio_read`; the generic,
point-independent translation character is
`exists_millerValue_translationChar`; step 4 is
`millerValue_translationChar_pow`; and steps 2–3 — the `Θ`-telescope
plus one generic auxiliary point, stated as the constant identity
`γ^p·c = 1` — are `millerValue_crossRatio_pow_mul_translationChar`,
closed 2026-07-26.  Nothing under this theorem is open. -/
theorem exists_millerValue_alternating {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (hcard : Fintype.card ι = p ^ 2)
    {a b : W.CoordinateRing} (ha : a ≠ 0) (hb : b ≠ 0)
    {T' P' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hbspan : Ideal.span {b} =
      ((((Finset.univ.val.map fun i => P' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (hQtor : (p : ℤ) • ((p : ℤ) • T') = 0)
    (hPtor : (p : ℤ) • ((p : ℤ) • P') = 0)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xV yV : F} (hV : W.Nonsingular xV yV)
    {xM1 yM1 : F} (hM1 : W.Nonsingular xM1 yM1)
    {xM2 yM2 : F} (hM2 : W.Nonsingular xM2 yM2)
    {xPU yPU : F} (hPU : W.Nonsingular xPU yPU)
    (hVeq : (WeierstrassCurve.Affine.Point.some xV yV hV : W.Point) =
      P' + WeierstrassCurve.Affine.Point.some xU yU hU)
    (hM1eq : (WeierstrassCurve.Affine.Point.some xM1 yM1 hM1 : W.Point) =
      T' - WeierstrassCurve.Affine.Point.some xU yU hU)
    (hM2eq : (WeierstrassCurve.Affine.Point.some xM2 yM2 hM2 : W.Point) =
      -(WeierstrassCurve.Affine.Point.some xU yU hU : W.Point))
    (hPUeq : (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) =
      (p : ℤ) • P' + WeierstrassCurve.Affine.Point.some xU yU hU)
    (hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0)
    (hVa : AdjoinRoot.evalEval hV.left a ≠ 0)
    (hVv : AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0)
    (hM1b : AdjoinRoot.evalEval hM1.left b ≠ 0)
    (hM1v : AdjoinRoot.evalEval hM1.left (enumVertical W val) ≠ 0)
    (hM2b : AdjoinRoot.evalEval hM2.left b ≠ 0)
    (hM2v : AdjoinRoot.evalEval hM2.left (enumVertical W val) ≠ 0)
    (hPUa : AdjoinRoot.evalEval hPU.left a ≠ 0)
    (hPUv : AdjoinRoot.evalEval hPU.left (enumVertical W val) ≠ 0) :
    ∃ e : ℕ, (e = 1 ∨ e = p - 1) ∧
      AdjoinRoot.evalEval hM1.left b ^ p *
          AdjoinRoot.evalEval hU.left a ^ p *
          AdjoinRoot.evalEval hM2.left (enumVertical W val) ^ p *
          AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p *
          (AdjoinRoot.evalEval hU.left a *
            AdjoinRoot.evalEval hPU.left (enumVertical W val)) ^ e =
        AdjoinRoot.evalEval hM2.left b ^ p *
          AdjoinRoot.evalEval hV.left a ^ p *
          AdjoinRoot.evalEval hM1.left (enumVertical W val) ^ p *
          AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p *
          (AdjoinRoot.evalEval hPU.left a *
            AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ e := by
  -- ── the two inputs: the cross-ratio constant `γ` (with `γ^p·c = 1`)
  --    and `c^p = 1`, both read at `U`
  obtain ⟨γ, hcross, hgamma⟩ :=
    exists_millerValue_crossRatio_const (val := val) hΔ hp hval_inj hval_tor
      hval_surj hcard ha hb hspan hbspan hQtor hPtor hU hV hM1 hM2 hPU hVeq
      hM1eq hM2eq hPUeq hUa hUv hVa hVv hM1b hM1v hM2b hM2v hPUa hPUv
  have hchar := millerValue_translationChar_pow (val := val) (P' := P') hΔ
    hval_inj hval_tor hval_surj ha hspan hPtor hU hPU hPUeq hUa hUv
  refine ⟨p - 1, Or.inr rfl, ?_⟩
  -- ── PROVEN glue: pure field algebra.  With `X := b(M₁)a(U)v(M₂)v(V)`,
  --    `Z := b(M₂)a(V)v(M₁)v(U)`, `α := a(U)v(P⊕U)`, `β := a(P⊕U)v(U)`
  --    the two inputs read `X = γ·Z`, `γ^p·β = α`, `β^p = α^p`, and the
  --    goal is `X^p·α^{p−1} = Z^p·β^{p−1}`; multiply by `β ≠ 0`.
  have hp1 : p - 1 + 1 = p :=
    Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt (Fact.out : 1 < p))
  have halg : ∀ Xv Zv αv βv γv : F, βv ≠ 0 → Xv = γv * Zv →
      γv ^ p * βv = αv → βv ^ p = αv ^ p →
      Xv ^ p * αv ^ (p - 1) = Zv ^ p * βv ^ (p - 1) := by
    intro Xv Zv αv βv γv hβ hX hγ hpow
    have e1 : βv ^ (p - 1) * βv = βv ^ p := by rw [← pow_succ, hp1]
    have e2 : αv ^ (p - 1) * αv = αv ^ p := by rw [← pow_succ, hp1]
    refine mul_right_cancel₀ hβ ?_
    calc Xv ^ p * αv ^ (p - 1) * βv
        = (γv * Zv) ^ p * αv ^ (p - 1) * βv := by rw [hX]
      _ = Zv ^ p * αv ^ (p - 1) * (γv ^ p * βv) := by ring
      _ = Zv ^ p * (αv ^ (p - 1) * αv) := by rw [hγ]; ring
      _ = Zv ^ p * αv ^ p := by rw [e2]
      _ = Zv ^ p * βv ^ p := by rw [hpow]
      _ = Zv ^ p * βv ^ (p - 1) * βv := by rw [← e1]; ring
  have hβ : AdjoinRoot.evalEval hPU.left a *
      AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0 :=
    mul_ne_zero hPUa hUv
  have hmain := halg
    (AdjoinRoot.evalEval hM1.left b * AdjoinRoot.evalEval hU.left a *
      AdjoinRoot.evalEval hM2.left (enumVertical W val) *
      AdjoinRoot.evalEval hV.left (enumVertical W val))
    (AdjoinRoot.evalEval hM2.left b * AdjoinRoot.evalEval hV.left a *
      AdjoinRoot.evalEval hM1.left (enumVertical W val) *
      AdjoinRoot.evalEval hU.left (enumVertical W val))
    (AdjoinRoot.evalEval hU.left a *
      AdjoinRoot.evalEval hPU.left (enumVertical W val))
    (AdjoinRoot.evalEval hPU.left a *
      AdjoinRoot.evalEval hU.left (enumVertical W val))
    γ hβ hcross hgamma hchar
  simp only [mul_pow] at hmain ⊢
  linear_combination hmain

/-- **Stage B, leaf 3 (PROVEN over the alternating-law leaf 3a): the mirror
side — Weil reciprocity and the level-`p²` telescope.**  With `f_P = aP/(X − x_S)^p`
(`div f_P = p(P⊕S) − p(S)`, the span hypothesis `haP`) and the
nontrivial translation character `g∘τ_P = c·g` of `g = a/v`
(the multiplied-out equation `heq` at the generic translate
`P ⊕ taut`, `c ≠ 1`, `c^p = 1`), the balanced evaluation of `f_P` at
`D_Q = (Q⊕R) − (R)` is `c^{±1}` times the SAME `g`-ratio `p`-th power
that leaf 2 produced for the `Q`-side:

`f_P(Q⊕R)/f_P(R) = c^e·[g(V)/g(U)]^p`,  `e ∈ {1, p−1}`.

Proof plan (Silverman *AEC* Ex. 3.16(c); Howe, *The Weil pairing and
the Hilbert symbol*; HLEG-NOTES.md §4(B) L4-9).  Weil reciprocity
between `f_P` and `g` — their divisors have disjoint support by the
setup's avoidances — turns the `f_P`-side into a `g`-side evaluation:
`∏_{w ∈ div g} f_P(w) = g(div f_P) = [g(P⊕S)/g(S)]^p`, and
`div g = [p]^*((Q) − (O))` rewrites the left side as
`(f_P∘[p])((Q) − (O))`, i.e. as the balanced `f_P`-evaluation at
`D_Q` up to the same `p`-th power of a `g`-ratio.  The bridge from
`g(P⊕S)/g(S)` back to `[g(V)/g(U)]^p` is the level-`p²` telescope:
with `p•P' = P`, the character equation gives
`∏_{j<p} g((j+1)P'⊕U)/g(jP'⊕U) = g(P⊕U)/g(U) = c`,
so the `p`-th power `[g(P'⊕U)/g(U)]^p = [g(V)/g(U)]^p` differs from
`g(P⊕U)/g(U) = c` exactly by the coboundary terms
`∏_j [g(P'⊕U)/g(U)] / [g((j+1)P'⊕U)/g(jP'⊕U)]`, which cancel against
the coboundaries produced on the reciprocity side (the mirror
computation), leaving the single character factor `c^e` with
`e ∈ {1, p−1}` — the ambiguity is the orientation of the pairing
(`c` versus `c^{-1} = c^{p-1}`).  All the intermediate evaluation
points are the telescope points `jP'⊕U`, `P' ∈ E[p²]`, which `hbad`
keeps off `div g`.

STAGING (2026-07-25, re-cut twice, then CLOSED down to ONE named leaf):
DECOMPOSED over the SHARED specialization brick
`exists_pointEval_specialization`, in the same balanced-halves shape as
leaf 2, plus exactly one open input — the alternating law, now a
top-level leaf of its own, `exists_millerValue_alternating` above.

The mirror side is now run through the SAME L4-7 mechanism as leaf 2,
one level down.  With `p•P' = P` the divisor `Σ_κ (P'⊕κ) + Σ_κ (⊖κ)`
sums to `p²•P' = p•P = O`, so it has a Miller generator `b` — PROVEN
here from `exists_span_eq_prod_pointIdeal` — and `g_P := b/v` has
divisor `[p]^*((P) − (O))`, the `P`-side twin of `g = a/v`.  Then:

* the GENERIC identity, PROVEN inline (2026-07-25) as `hL47`: the
  existence of the pullback constant `c₁` with
  `f_P∘[p] = c₁·(g_P∘τ_{⊖S'})^p` **in the
  function field `K`**, multiplied out as
  `[p]^*(aP)·τ_{⊖S'}^*(v)^p = c₁·τ_{⊖S'}^*(b)^p·[p]^*(X − x_S)^p`.
  This is leaf 2's own inline input verbatim with `(aQ, x_R, R', a)`
  replaced by `(aP, x_S, S', b)`, and like it, it mentions no point:
  `div(f_P∘[p]) = p·[p]^*((P⊕S) − (S)) = p·τ_{⊖S'}(div g_P)`, so the
  ratio has trivial divisor and is a constant; it is proven by the same
  two divisor-transport bricks
  (`spanSingleton_pointEval_mul_fiberProd_pow`,
  `spanSingleton_pointEval_translate`) and
  `coordinateRing_isUnit_eq_const`.
* the ANTISYMMETRY of the pairing, now the SORRIED TOP-LEVEL LEAF
  `exists_millerValue_alternating` — the one genuinely reciprocal
  statement left.  Writing `M₁ = ⊖S'⊕T'⊕R'` and
  `M₂ = ⊖S'⊕R'` for the two points at which the `⊖S'`-translate is
  read (note `M₂ = ⊖U` and `M₁ = T' ⊖ U`, which is how the leaf is
  stated), it says
  `[g_P(M₁)/g_P(M₂)]^p = [g(P⊕U)/g(U)]^e·[g(V)/g(U)]^p`,
  `e ∈ {1, p−1}`.  Its left side is `f_P(D_Q)` (that is what the two
  halves compute) and `[g(V)/g(U)]^p` is `f_Q(D_P)` (leaf 2), so it is
  exactly `f_P(D_Q) = c^e·f_Q(D_P)`, i.e. `e_p(P,Q)·e_p(Q,P) = 1` — the
  alternating law, which is what Weil reciprocity is needed FOR here.
  Plain reciprocity between `f_P` and `g` does not give it: both sides
  of `f_P(div g) = g(div f_P)` collapse (the norm `N_{[p]}(f_P)` is
  constant because `[p]_*div f_P = 0`, and the right side is `c^p = 1`),
  so the identity is vacuous and the `p`-th-root structure — the L4-7
  constants above — is what carries the content.

Everything between is PROVEN glue.  `p•(T'⊕R') = Q⊕R` and `p•R' = R`
put the two `[p]`-halves onto this leaf's own evaluation points, and
`p•M₁ = (Q⊕R) ⊖ S ≠ O`, `p•M₂ = ⊖(S ⊖ R) ≠ O` make `M₁`, `M₂` affine
and off `div g` — both nonvanishings coming from the field separation,
`x_S ∈ F₂` against `x_R, x_{Q⊕R} ∉ F₂`.  Eight applications of the
specialization brick clear the denominators of the generic identity at
those two points; the reciprocity constant of the halves is then read
off as `c'' = c₁·g_P(M₁)^p/g(V)^p`, and it cancels in the ratio.

The discrepancy between the halves is carried by the `e`-th power of
the `g`-RATIO `g(P⊕U)/g(U)` rather than by `c^e`, which is what keeps
the level-`p²` telescope out of the sorry: the telescope
`∏_{j<p} g((j+1)P'⊕U)/g(jP'⊕U) = g(P⊕U)/g(U)` is a formal
cancellation, and its value `c` is the CHARACTER equation `heq` read at
the point `U` — one application of the specialization brick, proven
below.  Unlike leaf 2 the two halves are not a comparison against
`div g` itself — `div f_P = p(P⊕S) − p(S)` pulls back to translates of
the `[p]`-fibres of `P⊕S` and `S`, i.e. to `div g_P`, not `div g` —
which is why a character factor appears between them at all.

Also proven here, from the abscissa avoidance `xS ≠ xR`: the
telescope's base point `P⊕U` is affine and off `div g`
(`p•(P⊕U) = S ⊖ R ≠ O`, so it is not `p`-torsion and the vertical
product does not vanish there), which is what lets the character
equation be read at `U` at all.

### GENERICITY-LAYER AUDIT (2026-07-31) — why this no longer mentions a subfield

Until 2026-07-31 this theorem took `{F₁ F₂ : Subfield F}` with both
`(F₁ : Set F).Finite` and `(F₂ : Set F).Finite`, plus `hbad`, `hF₁₂` and eight
membership hypotheses — and that finite-subfield requirement was the *recorded*
reason the Stage-B genericity layer was believed to be characteristic-`p`-only
(a finite subfield containing the curve's coefficients exists only in
characteristic `p`).  The compiler disagreed: `hF₁fin`, `hF₂fin`, `hF₁₂`, `hbad`,
`hySF₂`, `hxSF₁`, `hyPSF₂` and `hxPSF₁` were all flagged by the `unusedVariables`
linter, i.e. the proof never looked at any of them.

The four that were used — `hxSF₂`, `hxRF₂`, `hxPSF₂`, `hxQRF₂` — were used at
exactly four places, and each time only to separate two abscissae.  So the whole
field hierarchy was an **avoidance device**, and what the proof actually needs is
the four inequations now taken as hypotheses:

    x_S ≠ x_R,   x_{Q⊕R} ≠ x_S,   x_{Q⊕R} ≠ x_{P⊕S},   x_R ≠ x_{P⊕S},

equivalently `S ≠ R`, `Q⊕R ≠ S`, `Q⊕R ≠ P⊕S`, `R ≠ P⊕S`.  These mention no field
and no characteristic.  Over an algebraically closed base of characteristic zero
`W.Point` is infinite, so they are *easier* to arrange than in characteristic `p`,
where they had to be manufactured from `exists_finite_subfield_containing`.

`exists_millerRatio_eval_translationChar` below is the old statement, recovered as
a one-line wrapper, so no characteristic-`p` consumer changes.  The same audit
applies to leaf 1; see `exists_generic_pDivision_offset_of_avoid`. -/
theorem exists_millerRatio_eval_translationChar_of_avoid {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (hcard : Fintype.card ι = p ^ 2)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    {T' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {xP yP : F} (hP : W.Nonsingular xP yP)
    {xQ yQ : F} (hQ : W.Nonsingular xQ yQ)
    (hT : (p : ℤ) • T' = WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    {i₀ : ι} (hPval : val i₀ = WeierstrassCurve.Affine.Point.some xP yP hP)
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W (val i₀) + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {c : F} (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hτa : pointEval (constHom W) hκ.left a ≠ 0)
    (hτv : pointEval (constHom W) hκ.left (enumVertical W val) ≠ 0)
    (heq : pointEval (constHom W) hκ.left a *
        algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
      constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
        pointEval (constHom W) hκ.left (enumVertical W val))
    {xS yS : F} (hS : W.Nonsingular xS yS)
    {xR yR : F} (hR : W.Nonsingular xR yR)
    {xPS yPS : F} (hPS : W.Nonsingular xPS yPS)
    (hPSc : WeierstrassCurve.Affine.Point.some xPS yPS hPS =
      WeierstrassCurve.Affine.Point.some xP yP hP +
        WeierstrassCurve.Affine.Point.some xS yS hS)
    {xQR yQR : F} (hQR : W.Nonsingular xQR yQR)
    (hQRc : WeierstrassCurve.Affine.Point.some xQR yQR hQR =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
        WeierstrassCurve.Affine.Point.some xR yR hR)
    {aP : W.CoordinateRing}
    (haP : Ideal.span {aP} =
      (CoordinateRing.XYIdeal W xPS (Polynomial.C yPS)) ^ p *
        (CoordinateRing.XYIdeal W xS (Polynomial.C (W.negY xS yS))) ^ p)
    (hnzR : AdjoinRoot.evalEval hR.left aP ≠ 0)
    (hnzQR : AdjoinRoot.evalEval hQR.left aP ≠ 0)
    (hxSR : xS ≠ xR) (hxQRS : xQR ≠ xS)
    (hxQRPS : xQR ≠ xPS) (hxRPS : xR ≠ xPS)
    {S' R' P' : W.Point}
    (hS'p : (p : ℤ) • S' = WeierstrassCurve.Affine.Point.some xS yS hS)
    (hR'p : (p : ℤ) • R' = WeierstrassCurve.Affine.Point.some xR yR hR)
    (hP'p : (p : ℤ) • P' = WeierstrassCurve.Affine.Point.some xP yP hP)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xV yV : F} (hV : W.Nonsingular xV yV)
    (hUeq : WeierstrassCurve.Affine.Point.some xU yU hU = S' - R')
    (hVeq : WeierstrassCurve.Affine.Point.some xV yV hV = P' + (S' - R'))
    (hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0)
    (hVa : AdjoinRoot.evalEval hV.left a ≠ 0)
    (hVv : AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0) :
    ∃ e : ℕ, (e = 1 ∨ e = p - 1) ∧
      AdjoinRoot.evalEval hQR.left aP *
          AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) *
          (AdjoinRoot.evalEval hU.left a *
            AdjoinRoot.evalEval hV.left (enumVertical W val)) ^ p =
        c ^ e * (AdjoinRoot.evalEval hQR.left
              ((CoordinateRing.XClass W xS) ^ p) *
            AdjoinRoot.evalEval hR.left aP *
            (AdjoinRoot.evalEval hV.left a *
              AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ p) := by
  classical
  -- ── PROVEN: `S ≠ R`, from the abscissa avoidance `hxSR`
  have hSR : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
      WeierstrassCurve.Affine.Point.some xR yR hR ≠ 0 := by
    intro h0
    refine hxSR ?_
    have hEq : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) =
        WeierstrassCurve.Affine.Point.some xR yR hR := sub_eq_zero.mp h0
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hEq
    exact hEq.1
  -- ── PROVEN: `p•U = S ⊖ R` and `P` is `p`-torsion
  have hpU : (p : ℤ) • (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) =
      (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR := by
    rw [hUeq, smul_sub, hS'p, hR'p]
  have hPtor : (p : ℤ) •
      (WeierstrassCurve.Affine.Point.some xP yP hP : W.Point) = 0 := by
    rw [← hPval]
    exact hval_tor i₀
  -- ── PROVEN: the telescope's base point `P⊕U` is affine
  have hPU0 : (WeierstrassCurve.Affine.Point.some xP yP hP : W.Point) +
      WeierstrassCurve.Affine.Point.some xU yU hU ≠ 0 := by
    intro h0
    refine hSR ?_
    have hUP : (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) =
        -(WeierstrassCurve.Affine.Point.some xP yP hP : W.Point) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h0
    rw [← hpU, hUP, smul_neg, hPtor, neg_zero]
  obtain ⟨xPU, yPU, hPU, hPUeq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        WeierstrassCurve.Affine.Point.some xP yP hP +
          WeierstrassCurve.Affine.Point.some xU yU hU := by
    cases hc : ((WeierstrassCurve.Affine.Point.some xP yP hP : W.Point) +
        WeierstrassCurve.Affine.Point.some xU yU hU) with
    | zero => exact absurd hc hPU0
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- ── PROVEN: `P⊕U` is off `div g`: it is not `p`-torsion, since
  --    `p•(P⊕U) = S ⊖ R ≠ O`
  have hPUv : AdjoinRoot.evalEval hPU.left (enumVertical W val) ≠ 0 := by
    intro h0
    have hmem := mem_of_evalEval_eq_zero (span_enumVertical val) hPU h0
    rw [Multiset.mem_add] at hmem
    have htor : (p : ℤ) •
        (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) = 0 := by
      rcases hmem with hm | hm
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        rw [← hi]
        exact hval_tor i
      · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
        rw [← hi, smul_neg, hval_tor i, neg_zero]
    refine hSR ?_
    rw [← hpU]
    have hsplit : (p : ℤ) •
        (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) =
        (p : ℤ) • (WeierstrassCurve.Affine.Point.some xP yP hP : W.Point) +
          (p : ℤ) • (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) := by
      rw [hPUeq, smul_add]
    rw [htor, hPtor, zero_add] at hsplit
    exact hsplit.symm
  -- ── PROVEN: the character equation `heq` read at the point `U`.  This
  --    is the value of the level-`p²` telescope
  --    `∏_{j<p} g((j+1)P'⊕U)/g(jP'⊕U) = g(P⊕U)/g(U) = c`, and it is one
  --    application of the specialization brick to the translation
  --    `z ↦ z∘τ_P` at `U`, whose image is `P⊕U`.
  have hpt1 : constPoint W (val i₀) + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
    rw [one_zsmul]
    exact hpt
  have hPUc : (WeierstrassCurve.Affine.Point.some xPU yPU hPU : W.Point) =
      val i₀ + (1 : ℤ) •
        (WeierstrassCurve.Affine.Point.some xU yU hU : W.Point) := by
    rw [one_zsmul, hPval]
    exact hPUeq
  have hchar : AdjoinRoot.evalEval hPU.left a *
      AdjoinRoot.evalEval hU.left (enumVertical W val) =
      c * AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hPU.left (enumVertical W val) := by
    obtain ⟨n₄, d₄, hd₄, hK₄, hv₄⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hpt1 hU hPU hPUc a
    obtain ⟨n₅, d₅, hd₅, hK₅, hv₅⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hpt1 hU hPU hPUc
        (enumVertical W val)
    have hFW : n₄ * enumVertical W val * d₅ = coordC W c * a * n₅ * d₄ := by
      refine IsFractionRing.injective W.CoordinateRing W.FunctionField ?_
      simp only [map_mul, algebraMap_coordC]
      rw [← hK₄, ← hK₅]
      linear_combination (algebraMap W.CoordinateRing W.FunctionField d₄ *
        algebraMap W.CoordinateRing W.FunctionField d₅) * heq
    have hval := congrArg (AdjoinRoot.evalEval hU.left) hFW
    simp only [map_mul, evalEval_coordC] at hval
    rw [hv₄, hv₅] at hval
    refine mul_right_cancel₀ (mul_ne_zero hd₄ hd₅) ?_
    linear_combination hval
  -- ── the two generic points at which the substrate evaluates: the
  --    `[p]`-multiple `p•taut` (where `pointEval` realizes `z ↦ z∘[p]`)
  --    and the translate `(⊖S')⊕taut` (where it realizes `z ↦ z∘τ_{⊖S'}`)
  obtain ⟨xpm, ypm, hpn, hptaut, hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  obtain ⟨xns, yns, hns, hptns⟩ := exists_translate_some (W := W) hΔ (-S')
  have hp0 : constPoint W (0 : W.Point) + (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xpm ypm hpn := by
    rw [show constPoint W (0 : W.Point) = 0 from rfl, zero_add]
    exact hptaut
  have hns0 : constPoint W (-S') + (1 : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xns yns hns := by
    rw [one_zsmul]
    exact hptns
  -- ── THE ANALYTIC SUB-LEAF 1 (PROVEN 2026-07-25), stated GENERICALLY —
  --    no point occurs in it: the `P`-SIDE of leaf 2's L4-7 span
  --    comparison, `f_P∘[p] = c₁·(g_P∘τ_{⊖S'})^p` in `K`, multiplied out.
  --    Here `g_P = b/v` is the `P`-side twin of `g = a/v`:
  --    `div(f_P∘[p]) = p·[p]^*((P⊕S) − (S)) = p·τ_{⊖S'}(div g_P)`, so
  --    the ratio has trivial divisor and is a constant
  --    (`coordinateRing_isUnit_eq_const`).  This is leaf 2's input with
  --    `(aQ, x_R, R', a)` replaced by `(aP, x_S, S', b)`, and it is proven
  --    by the same two transport bricks of `WeilPairingDescent.lean`:
  --    `spanSingleton_pointEval_mul_fiberProd_pow` (the `[p]`-pullback of
  --    a divisor is the multiplicity-one sum of its `p²`-fibres) applied
  --    to `aP` (divisor `p(P⊕S) + p(⊖S)`) and to `X − x_S` (divisor
  --    `(S) + (⊖S)`), and `spanSingleton_pointEval_translate` (the `τ_Q^*`
  --    of a divisor is its `⊖Q`-translate) applied to `v = ∏(X − x_κ)`
  --    and to `b`.  Since `p•(P'⊕S') = P⊕S` and `p•S' = S`, the
  --    `[p]`-fibres of `P⊕S` and `S` are exactly the `S'`-translates of
  --    the `P'⊕κ` and `κ` heads of `div b` and `div v`; the `⊖κ` tails
  --    are common to both sides and cancel, as do the unit factors
  --    `J_O^{2p}` and `I'_{S'}^{2p³}`.
  have hL47 : ∀ b : W.CoordinateRing, b ≠ 0 →
      Ideal.span {b} =
        ((((Finset.univ.val.map fun i => P' + val i) +
          Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod →
      ∃ c₁ : F,
        pointEval (constHom W) hpn.left aP *
            pointEval (constHom W) hns.left (enumVertical W val) ^ p =
          constHom W c₁ * pointEval (constHom W) hns.left b ^ p *
            pointEval (constHom W) hpn.left (CoordinateRing.XClass W xS) ^ p := by
    intro b hb0 hbspan
    -- `[p]^*` evaluation is injective (the `x`-coordinate of `p•taut` is
    -- transcendental over the constants), so nothing nonzero evaluates to `0`
    have hinjp : Function.Injective (pointEval (constHom W) hpn.left) :=
      pointEval_injective_of_forall_ne_constHom hpn
        (smul_taut_xCoord_ne_constHom hxrel)
    have haP0 : aP ≠ 0 := fun h0 => hnzR (by rw [h0, map_zero])
    have hX0 : CoordinateRing.XClass W xS ≠ 0 := CoordinateRing.XClass_ne_zero xS
    have hv0 : enumVertical W val ≠ 0 := enumVertical_ne_zero W val
    have hevaP : pointEval (constHom W) hpn.left aP ≠ 0 := fun h0 =>
      haP0 (hinjp (by rw [h0, map_zero]))
    have hevX :
        pointEval (constHom W) hpn.left (CoordinateRing.XClass W xS) ≠ 0 :=
      fun h0 => hX0 (hinjp (by rw [h0, map_zero]))
    -- ── a section of `[p]` on points
    obtain ⟨sec, hsec⟩ :
        ∃ s : W.Point → W.Point, ∀ Z : W.Point, (p : ℤ) • s Z = Z := by
      choose s hs using exists_zsmul_eq (W := W) hΔ hp
      exact ⟨s, hs⟩
    -- ── the `[p]`-fiber product depends on its base point only through `[p]`
    have hfib : ∀ T₁ T₂ : W.Point, (p : ℤ) • T₁ = (p : ℤ) • T₂ →
        fiberProd W val T₁ = fiberProd W val T₂ := by
      intro T₁ T₂ h
      have hd : (p : ℤ) • (T₁ - T₂) = 0 := by rw [smul_sub, h, sub_self]
      have h1 : (Finset.univ.val.map fun i => (T₁ - T₂) + val i) =
          Finset.univ.val.map fun i => val i :=
        map_add_torsion_eq hval_inj hval_tor hval_surj hd
      have h2 := congrArg (Multiset.map (fun R : W.Point => T₂ + R)) h1
      simp only [Multiset.map_map, Function.comp_apply] at h2
      unfold fiberProd
      rw [show (Finset.univ.val.map fun i => T₁ + val i) =
        Finset.univ.val.map fun i => T₂ + (T₁ - T₂ + val i) from
          Multiset.map_congr rfl fun i _ => by abel, h2]
    -- ── the affine divisors `div aP = p(P⊕S) + p(⊖S)` and
    --    `div (X − x_S) = (S) + (⊖S)` feeding the pullback brick
    have hDaP : Ideal.span {aP} =
        ((Multiset.replicate p (WeierstrassCurve.Affine.Point.some xPS yPS hPS) +
          Multiset.replicate p
            (-(WeierstrassCurve.Affine.Point.some xS yS hS) : W.Point)).map
          (pointIdeal W)).prod := by
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.map_replicate, Multiset.prod_replicate, Multiset.prod_replicate,
        haP, pointIdeal_some, WeierstrassCurve.Affine.Point.neg_some,
        pointIdeal_some]
    have hDaP0 : (0 : W.Point) ∉
        Multiset.replicate p (WeierstrassCurve.Affine.Point.some xPS yPS hPS) +
          Multiset.replicate p
            (-(WeierstrassCurve.Affine.Point.some xS yS hS) : W.Point) := by
      intro h
      rcases Multiset.mem_add.mp h with h | h
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hPS
          (Multiset.eq_of_mem_replicate h).symm
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hS
          (neg_eq_zero.mp (Multiset.eq_of_mem_replicate h).symm)
    have hDX : Ideal.span {CoordinateRing.XClass W xS} =
        ((WeierstrassCurve.Affine.Point.some xS yS hS ::ₘ
          {(-(WeierstrassCurve.Affine.Point.some xS yS hS) : W.Point)}).map
          (pointIdeal W)).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
        Multiset.prod_singleton, pointIdeal_some,
        WeierstrassCurve.Affine.Point.neg_some, pointIdeal_some]
      calc Ideal.span {CoordinateRing.XClass W xS}
          = CoordinateRing.XIdeal W xS := rfl
        _ = CoordinateRing.XYIdeal W xS (Polynomial.C (W.negY xS yS)) *
            CoordinateRing.XYIdeal W xS (Polynomial.C yS) :=
          (CoordinateRing.XYIdeal_neg_mul hS).symm
        _ = CoordinateRing.XYIdeal W xS (Polynomial.C yS) *
            CoordinateRing.XYIdeal W xS (Polynomial.C (W.negY xS yS)) :=
          mul_comm _ _
    have hDX0 : (0 : W.Point) ∉ (WeierstrassCurve.Affine.Point.some xS yS hS ::ₘ
        {(-(WeierstrassCurve.Affine.Point.some xS yS hS) : W.Point)}) := by
      intro h
      rcases Multiset.mem_cons.mp h with h | h
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hS h.symm
      · exact WeierstrassCurve.Affine.Point.some_ne_zero hS
          (neg_eq_zero.mp (Multiset.mem_singleton.mp h).symm)
    -- ── L4-7 multiplicity-one pullback: the divisors of `[p]^*aP` and of
    --    `[p]^*(X − x_S)`, as fiber products over `E[p]`
    have hA := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
      hval_inj hval_tor hval_surj hcard hptaut hsec haP0 hevaP hDaP0 hDaP
    have hB := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
      hval_inj hval_tor hval_surj hcard hptaut hsec hX0 hevX hDX0 hDX
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.prod_replicate, Multiset.card_add, Multiset.card_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton, Multiset.card_cons, Multiset.card_singleton]
      at hA hB
    -- `p•(P'⊕S') = P⊕S` and `p•S' = S`, so the two fibers are the ones the
    -- `⊖S'`-translated `div g_P` will produce
    rw [hfib (sec (WeierstrassCurve.Affine.Point.some xPS yPS hPS)) (P' + S')
        (by rw [hsec, smul_add, hP'p, hS'p]; exact hPSc)] at hA
    rw [hfib (sec (WeierstrassCurve.Affine.Point.some xS yS hS)) S'
        (by rw [hsec, hS'p])] at hB
    -- ── L4-8 translation transport: the divisors of `τ_{⊖S'}^*(v)` and
    --    `τ_{⊖S'}^*(b)`, i.e. the `S'`-translates of `div v` and `div b`
    have hC := spanSingleton_pointEval_translate (W := W) hΔ hptns hv0
      (span_enumVertical (W := W) val)
    have hD := spanSingleton_pointEval_translate (W := W) hΔ hptns hb0 hbspan
    rw [neg_neg] at hC hD
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.card_add,
      Multiset.card_map, Multiset.map_map, Function.comp_apply] at hC hD
    -- the `P'⊕κ` and `κ` heads of those translates are exactly the fibers
    -- of `P⊕S` and of `S`; the `⊖κ` tails are common to both and cancel
    have hfibS' : fiberProd W val S' =
        (Finset.univ.val.map fun i =>
          (pointIdeal' W (val i - -S') :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
      unfold fiberProd
      rw [Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
      show (pointIdeal' W (S' + val i) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        (pointIdeal' W (val i - -S') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
      rw [show S' + val i = val i - -S' from by abel]
    have hfibPS' : fiberProd W val (P' + S') =
        (Finset.univ.val.map fun i =>
          (pointIdeal' W (P' + val i - -S') :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
      unfold fiberProd
      rw [Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
      show (pointIdeal' W (P' + S' + val i) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        (pointIdeal' W (P' + val i - -S') :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
      rw [show P' + S' + val i = P' + val i - -S' from by abel]
    rw [← hfibS'] at hC
    rw [← hfibPS'] at hD
    rw [show (Finset.univ : Finset ι).val.card = Fintype.card ι from rfl] at hC hD
    -- ── the two sides have the SAME divisor: cancelling the unit factors
    --    `J_O^{2p}` and `I'_{S'}^{2p³}` leaves an equality of principal
    --    fractional ideals, hence a nonzero constant ratio `c₁`
    have hu : IsUnit ((fiberProd W val (sec 0)) ^ (p + p) *
        ((pointIdeal' W S' :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
            (Fintype.card ι + Fintype.card ι)) ^ p) :=
      ((isUnit_prod_coe_pointIdeal' _).pow _).mul
        (((pointIdeal' W S').isUnit.pow _).pow _)
    have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hns.left b ^ p *
            pointEval (constHom W) hpn.left (CoordinateRing.XClass W xS) ^ p) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left aP *
            pointEval (constHom W) hns.left (enumVertical W val) ^ p) := by
      simp only [← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.spanSingleton_pow]
      refine hu.mul_right_cancel ?_
      calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hns.left b) ^ p *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hpn.left (CoordinateRing.XClass W xS)) ^ p *
            ((fiberProd W val (sec 0)) ^ (p + p) *
              ((pointIdeal' W S' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                  (Fintype.card ι + Fintype.card ι)) ^ p)
          = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hns.left b) *
              (pointIdeal' W S' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                (Fintype.card ι + Fintype.card ι)) ^ p *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left (CoordinateRing.XClass W xS)) *
              (fiberProd W val (sec 0)) ^ (1 + 1)) ^ p := by ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left aP) *
              (fiberProd W val (sec 0)) ^ (p + p) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hns.left (enumVertical W val)) *
              (pointIdeal' W S' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                (Fintype.card ι + Fintype.card ι)) ^ p := by
            rw [hD, ← hB, ← hA, hC]
            ring
        _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hpn.left aP) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hns.left (enumVertical W val)) ^ p *
            ((fiberProd W val (sec 0)) ^ (p + p) *
              ((pointIdeal' W S' :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                  (Fintype.card ι + Fintype.card ι)) ^ p) := by ring
    obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hfrac
    obtain ⟨cc, -, hcz⟩ := coordinateRing_isUnit_eq_const z.isUnit
    refine ⟨cc, ?_⟩
    rw [← hz, Units.smul_def, hcz, Algebra.smul_def,
      show algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C cc))) =
        constHom W cc from rfl]
    ring
  -- ── PROVEN: the `P`-side Miller generator `b` exists, because its
  --    divisor `Σ_κ (P'⊕κ) + Σ_κ (⊖κ)` sums to `p²•P' = p•P = O`
  obtain ⟨b, hb0, hbspan⟩ : ∃ b : W.CoordinateRing, b ≠ 0 ∧
      Ideal.span {b} =
        ((((Finset.univ.val.map fun i => P' + val i) +
          Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod := by
    refine exists_span_eq_prod_pointIdeal _ ?_
    rw [Multiset.sum_add]
    rw [show (Finset.univ.val.map fun i : ι => P' + val i).sum =
      ∑ i : ι, (P' + val i) from rfl]
    rw [show (Finset.univ.val.map fun i : ι => -val i).sum =
      ∑ i : ι, -val i from rfl]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_neg_distrib,
      add_assoc, add_neg_cancel, add_zero, Finset.card_univ, hcard,
      ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_pow, pow_two, mul_smul, hP'p, hPtor]
  obtain ⟨c₁, hcore⟩ := hL47 b hb0 hbspan
  -- ── PROVEN glue: reading the generic identity at a `p`-division
  --    point `Z`, whose `[p]`-image is `Zp` and whose `⊖S'`-translate is
  --    `Zr`.  Eight applications of the specialization brick clear the
  --    denominators; they cancel again after evaluation.
  have hhalf : ∀ (xZ yZ : F) (hZ : W.Nonsingular xZ yZ)
      (xZp yZp : F) (hZp : W.Nonsingular xZp yZp)
      (xZr yZr : F) (hZr : W.Nonsingular xZr yZr),
      (p : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) =
        WeierstrassCurve.Affine.Point.some xZp yZp hZp →
      (WeierstrassCurve.Affine.Point.some xZr yZr hZr : W.Point) =
        -S' + WeierstrassCurve.Affine.Point.some xZ yZ hZ →
      AdjoinRoot.evalEval hZp.left aP *
          AdjoinRoot.evalEval hZr.left (enumVertical W val) ^ p =
        c₁ * AdjoinRoot.evalEval hZr.left b ^ p *
          AdjoinRoot.evalEval hZp.left (CoordinateRing.XClass W xS) ^ p := by
    intro xZ yZ hZ xZp yZp hZp xZr yZr hZr hZpc hZrc
    have hZpc' : (WeierstrassCurve.Affine.Point.some xZp yZp hZp : W.Point) =
        (0 : W.Point) +
          (p : ℤ) • (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [zero_add]
      exact hZpc.symm
    have hZrc' : (WeierstrassCurve.Affine.Point.some xZr yZr hZr : W.Point) =
        -S' + (1 : ℤ) •
          (WeierstrassCurve.Affine.Point.some xZ yZ hZ : W.Point) := by
      rw [one_zsmul]
      exact hZrc
    obtain ⟨n₁, d₁, hd₁, hK₁, hv₁⟩ :=
      exists_pointEval_specialization hΔ (p : ℤ) hp0 hZ hZp hZpc' aP
    obtain ⟨n₂, d₂, hd₂, hK₂, hv₂⟩ :=
      exists_pointEval_specialization hΔ (p : ℤ) hp0 hZ hZp hZpc'
        (CoordinateRing.XClass W xS)
    obtain ⟨n₃, d₃, hd₃, hK₃, hv₃⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hns0 hZ hZr hZrc'
        (enumVertical W val)
    obtain ⟨n₄, d₄, hd₄, hK₄, hv₄⟩ :=
      exists_pointEval_specialization hΔ (1 : ℤ) hns0 hZ hZr hZrc' b
    have hFW : n₁ * n₃ ^ p * d₄ ^ p * d₂ ^ p =
        coordC W c₁ * n₄ ^ p * n₂ ^ p * d₁ * d₃ ^ p := by
      refine IsFractionRing.injective W.CoordinateRing W.FunctionField ?_
      simp only [map_mul, map_pow, algebraMap_coordC]
      rw [← hK₁, ← hK₂, ← hK₃, ← hK₄]
      linear_combination (algebraMap W.CoordinateRing W.FunctionField d₁ *
        algebraMap W.CoordinateRing W.FunctionField d₃ ^ p *
        algebraMap W.CoordinateRing W.FunctionField d₄ ^ p *
        algebraMap W.CoordinateRing W.FunctionField d₂ ^ p) * hcore
    have hval := congrArg (AdjoinRoot.evalEval hZ.left) hFW
    simp only [map_mul, map_pow, evalEval_coordC] at hval
    rw [hv₁, hv₂, hv₃, hv₄] at hval
    have hden : AdjoinRoot.evalEval hZ.left d₁ *
        AdjoinRoot.evalEval hZ.left d₂ ^ p *
        AdjoinRoot.evalEval hZ.left d₃ ^ p *
        AdjoinRoot.evalEval hZ.left d₄ ^ p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hd₁ (pow_ne_zero _ hd₂))
        (pow_ne_zero _ hd₃)) (pow_ne_zero _ hd₄)
    refine mul_right_cancel₀ hden ?_
    linear_combination hval
  -- ── PROVEN: `Q⊕R ≠ S`, since `F₂` separates their abscissae
  have hQRS : (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) -
      WeierstrassCurve.Affine.Point.some xS yS hS ≠ 0 := by
    intro h0
    refine hxQRS ?_
    have hEq : (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) =
        WeierstrassCurve.Affine.Point.some xS yS hS := sub_eq_zero.mp h0
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hEq
    exact hEq.1
  -- ── PROVEN: the four evaluation points of the mirror side.  The two
  --    `p`-division points `T'⊕R'` and `R'` have `[p]`-images `Q⊕R` and
  --    `R`; their `⊖S'`-translates are `M₁` and `M₂`.
  obtain ⟨xZ1, yZ1, hZ1, hZ1eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = T' + R' := by
    cases hc : (T' + R' : W.Point) with
    | zero =>
      exfalso
      refine WeierstrassCurve.Affine.Point.some_ne_zero hQR ?_
      rw [hQRc, ← hT, ← hR'p, ← smul_add, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xZ2, yZ2, hZ2, hZ2eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = R' := by
    cases hc : (R' : W.Point) with
    | zero =>
      exfalso
      refine WeierstrassCurve.Affine.Point.some_ne_zero hR ?_
      rw [← hR'p, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hpM1 : (p : ℤ) • ((-S' + (T' + R') : W.Point)) =
      (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) -
        WeierstrassCurve.Affine.Point.some xS yS hS := by
    rw [hQRc, smul_add, smul_neg, hS'p, smul_add, hT, hR'p]
    abel
  have hpM2 : (p : ℤ) • ((-S' + R' : W.Point)) =
      -((WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR) := by
    rw [smul_add, smul_neg, hS'p, hR'p]
    abel
  obtain ⟨xM1, yM1, hM1, hM1eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
        -S' + (T' + R') := by
    cases hc : ((-S' + (T' + R')) : W.Point) with
    | zero =>
      exfalso
      refine hQRS ?_
      rw [← hpM1, hc]
      exact smul_zero _
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xM2, yM2, hM2, hM2eq⟩ : ∃ (x y : F) (h : W.Nonsingular x y),
      (WeierstrassCurve.Affine.Point.some x y h : W.Point) = -S' + R' := by
    cases hc : ((-S' + R') : W.Point) with
    | zero =>
      exfalso
      refine hSR ?_
      have hz : -((WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
          WeierstrassCurve.Affine.Point.some xR yR hR) = 0 := by
        rw [← hpM2, hc]
        exact smul_zero _
      rwa [neg_eq_zero] at hz
    | some x y h => exact ⟨x, y, h, rfl⟩
  -- ── PROVEN: `M₁` and `M₂` are off `div g`, since neither is
  --    `p`-torsion (`p•M₁ = (Q⊕R) ⊖ S`, `p•M₂ = ⊖(S ⊖ R)`)
  have hMv : ∀ (x y : F) (h : W.Nonsingular x y),
      AdjoinRoot.evalEval h.left (enumVertical W val) = 0 →
      (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = 0 := by
    intro x y h h0
    have hmem := mem_of_evalEval_eq_zero (span_enumVertical val) h h0
    rw [Multiset.mem_add] at hmem
    rcases hmem with hm | hm
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
      rw [← hi]
      exact hval_tor i
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
      rw [← hi, smul_neg, hval_tor i, neg_zero]
  have hM1v : AdjoinRoot.evalEval hM1.left (enumVertical W val) ≠ 0 := by
    intro h0
    refine hQRS ?_
    rw [← hpM1, ← hM1eq]
    exact hMv _ _ _ h0
  have hM2v : AdjoinRoot.evalEval hM2.left (enumVertical W val) ≠ 0 := by
    intro h0
    refine hSR ?_
    have hz : -((WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR) = 0 := by
      rw [← hpM2, ← hM2eq]
      exact hMv _ _ _ h0
    rwa [neg_eq_zero] at hz
  -- ── PROVEN glue: the two balanced halves of the mirror side
  have hI := hhalf xZ1 yZ1 hZ1 xQR yQR hQR xM1 yM1 hM1
    (by rw [hZ1eq, smul_add, hT, hR'p, hQRc])
    (by rw [hM1eq, hZ1eq])
  have hII := hhalf xZ2 yZ2 hZ2 xR yR hR xM2 yM2 hM2
    (by rw [hZ2eq, hR'p])
    (by rw [hM2eq, hZ2eq])
  -- ── PROVEN: membership in the divisor of a level-`p²` Miller generator
  --    `z` with head `M'` forces the point to be a `[p]`-preimage of
  --    `[p]M'` or to be `p`-torsion — the only two blocks of `div z`
  have hdiv : ∀ (M' : W.Point) (z : W.CoordinateRing),
      Ideal.span {z} =
        ((((Finset.univ.val.map fun i => M' + val i) +
          Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod →
      ∀ (x y : F) (h : W.Nonsingular x y),
        AdjoinRoot.evalEval h.left z = 0 →
        (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
            (p : ℤ) • M' ∨
          (p : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.Point) = 0 := by
    intro M' z hz x y h h0
    have hmem := mem_of_evalEval_eq_zero hz h h0
    rw [Multiset.mem_add] at hmem
    rcases hmem with hm | hm
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
      exact Or.inl (by rw [← hi, smul_add, hval_tor i, add_zero])
    · obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hm
      exact Or.inr (by rw [← hi, smul_neg, hval_tor i, neg_zero])
  -- ── PROVEN: the three remaining nonvanishings, all from the field
  --    separation.  `p•(P⊕U) = S ⊖ R`, `p•M₁ = (Q⊕R) ⊖ S`,
  --    `p•M₂ = ⊖(S ⊖ R)`, and each of the two bad cases would identify
  --    two abscissae that `F₂` separates.
  have hpPU : (p : ℤ) • (WeierstrassCurve.Affine.Point.some xPU yPU hPU :
      W.Point) =
      (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR := by
    rw [hPUeq, smul_add, hPtor, hpU, zero_add]
  have hpM1' : (p : ℤ) • (WeierstrassCurve.Affine.Point.some xM1 yM1 hM1 :
      W.Point) =
      (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) -
        WeierstrassCurve.Affine.Point.some xS yS hS := by
    rw [hM1eq]; exact hpM1
  have hpM2' : (p : ℤ) • (WeierstrassCurve.Affine.Point.some xM2 yM2 hM2 :
      W.Point) =
      -((WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
        WeierstrassCurve.Affine.Point.some xR yR hR) := by
    rw [hM2eq]; exact hpM2
  have hPUa : AdjoinRoot.evalEval hPU.left a ≠ 0 := by
    intro h0
    rcases hdiv T' a hspan xPU yPU hPU h0 with hm | hm
    · -- `S ⊖ R = Q` would force `S = Q⊕R`, but `x_S ∈ F₂` and `x_{Q⊕R} ∉ F₂`
      have hSQ : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
          WeierstrassCurve.Affine.Point.some xR yR hR =
          WeierstrassCurve.Affine.Point.some xQ yQ hQ := by
        rw [← hpPU, hm, hT]
      have hSeq : (WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) =
          WeierstrassCurve.Affine.Point.some xQR yQR hQR := by
        rw [hQRc, ← hSQ]; abel
      rw [WeierstrassCurve.Affine.Point.some.injEq] at hSeq
      exact hxQRS hSeq.1.symm
    · exact hSR (by rw [← hpPU]; exact hm)
  have hM1b : AdjoinRoot.evalEval hM1.left b ≠ 0 := by
    intro h0
    rcases hdiv P' b hbspan xM1 yM1 hM1 h0 with hm | hm
    · -- `(Q⊕R) ⊖ S = P` would force `Q⊕R = P⊕S`, but `x_{P⊕S} ∈ F₂`
      have hQS : (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) -
          WeierstrassCurve.Affine.Point.some xS yS hS =
          WeierstrassCurve.Affine.Point.some xP yP hP := by
        rw [← hpM1', hm, hP'p]
      have hQeq : (WeierstrassCurve.Affine.Point.some xQR yQR hQR : W.Point) =
          WeierstrassCurve.Affine.Point.some xPS yPS hPS := by
        rw [hPSc, ← hQS]; abel
      rw [WeierstrassCurve.Affine.Point.some.injEq] at hQeq
      exact hxQRPS hQeq.1
    · exact hQRS (by rw [← hpM1']; exact hm)
  have hM2b : AdjoinRoot.evalEval hM2.left b ≠ 0 := by
    intro h0
    rcases hdiv P' b hbspan xM2 yM2 hM2 h0 with hm | hm
    · -- `R ⊖ S = P` would force `R = P⊕S`, but `x_R ∉ F₂` and `x_{P⊕S} ∈ F₂`
      have hRS : (WeierstrassCurve.Affine.Point.some xR yR hR : W.Point) -
          WeierstrassCurve.Affine.Point.some xS yS hS =
          WeierstrassCurve.Affine.Point.some xP yP hP := by
        rw [← neg_sub, ← hpM2', hm]; exact hP'p
      have hReq : (WeierstrassCurve.Affine.Point.some xR yR hR : W.Point) =
          WeierstrassCurve.Affine.Point.some xPS yPS hPS := by
        rw [hPSc, ← hRS]; abel
      rw [WeierstrassCurve.Affine.Point.some.injEq] at hReq
      exact hxRPS hReq.1
    · refine hSR ?_
      have hz : -((WeierstrassCurve.Affine.Point.some xS yS hS : W.Point) -
          WeierstrassCurve.Affine.Point.some xR yR hR) = 0 := by
        rw [← hpM2']; exact hm
      rwa [neg_eq_zero] at hz
  -- ── THE ANALYTIC SUB-LEAF 2: the ANTISYMMETRY of the pairing, in
  --    Miller-value form — the one genuinely reciprocal statement left,
  --    now the named top-level leaf `exists_millerValue_alternating`.
  --    Divided out it reads
  --    `[g_P(M₁)/g_P(M₂)]^p = [g(P⊕U)/g(U)]^e·[g(V)/g(U)]^p`,
  --    `e ∈ {1, p−1}`; since the left side is `f_P(D_Q)` (by `hI`/`hII`)
  --    and `[g(V)/g(U)]^p` is `f_Q(D_P)` (leaf 2), that is
  --    `f_P(D_Q) = c^e·f_Q(D_P)`, i.e. `e_p(P,Q)·e_p(Q,P) = 1` — the
  --    alternating law, the content Weil reciprocity supplies.  The
  --    `e`-ambiguity is the orientation of the pairing.
  -- ── PROVEN: `Q = [p]T'` and `P = [p]P'` are `p`-torsion.  For `P` that
  --    is `hPtor` transported along `hP'p`; for `Q` it is read off the
  --    span of `a`, whose divisor sums to `(card E[p])·T' = p²·T'`.
  have hQtor : (p : ℤ) • ((p : ℤ) • T') = 0 := by
    have hsum := sum_eq_zero_of_span_eq_prod_pointIdeal ha hspan
    rw [Multiset.sum_add,
      show (Finset.univ.val.map fun i : ι => T' + val i).sum =
        ∑ i : ι, (T' + val i) from rfl,
      show (Finset.univ.val.map fun i : ι => -val i).sum =
        ∑ i : ι, -val i from rfl,
      Finset.sum_add_distrib, Finset.sum_const, Finset.sum_neg_distrib,
      add_assoc, add_neg_cancel, add_zero, Finset.card_univ, hcard,
      ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_pow, pow_two, mul_smul] at hsum
    exact hsum
  have hP'tor : (p : ℤ) • ((p : ℤ) • P') = 0 := by
    rw [hP'p]; exact hPtor
  obtain ⟨e, hecase, hanti⟩ :=
    exists_millerValue_alternating (val := val) hΔ hp hval_inj hval_tor
      hval_surj hcard ha hb0 hspan hbspan hQtor hP'tor hU hV hM1 hM2 hPU
      (by rw [hVeq, hUeq]) (by rw [hM1eq, hUeq]; abel)
      (by rw [hM2eq, hUeq]; abel) (by rw [hPUeq, hP'p])
      hUa hUv hVa hVv hM1b hM1v hM2b hM2v hPUa hPUv
  -- ── PROVEN glue: the reciprocity constant of the two halves is
  --    `c'' = c₁·g_P(M₁)^p/g(V)^p`, and against it the halves hold
  have hden : AdjoinRoot.evalEval hV.left a ^ p *
      AdjoinRoot.evalEval hM1.left (enumVertical W val) ^ p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hVa) (pow_ne_zero _ hM1v)
  obtain ⟨c'', hcQR, hcR⟩ :
      ∃ c'' : F,
        AdjoinRoot.evalEval hQR.left aP *
            AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p =
          c'' * AdjoinRoot.evalEval hV.left a ^ p *
            AdjoinRoot.evalEval hQR.left ((CoordinateRing.XClass W xS) ^ p) ∧
        AdjoinRoot.evalEval hR.left aP *
            AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p *
            (AdjoinRoot.evalEval hPU.left a *
              AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ e =
          c'' * AdjoinRoot.evalEval hU.left a ^ p *
            AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) *
            (AdjoinRoot.evalEval hU.left a *
              AdjoinRoot.evalEval hPU.left (enumVertical W val)) ^ e := by
    refine ⟨
      c₁ * AdjoinRoot.evalEval hM1.left b ^ p *
        AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p /
        (AdjoinRoot.evalEval hV.left a ^ p *
          AdjoinRoot.evalEval hM1.left (enumVertical W val) ^ p), ?_, ?_⟩
    · simp only [map_pow]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hden]
      linear_combination (AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p *
        AdjoinRoot.evalEval hV.left a ^ p) * hI
    · simp only [map_pow]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
        eq_div_iff hden]
      refine mul_right_cancel₀ (pow_ne_zero p hM2v) ?_
      linear_combination (AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p *
          (AdjoinRoot.evalEval hPU.left a *
            AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ e *
          AdjoinRoot.evalEval hV.left a ^ p *
          AdjoinRoot.evalEval hM1.left (enumVertical W val) ^ p) * hII -
        (c₁ * AdjoinRoot.evalEval hR.left
          (CoordinateRing.XClass W xS) ^ p) * hanti
  -- ── PROVEN glue: the telescope factor IS `c^e` (the character
  --    equation at `U`, raised to the `e`-th power), and it cancels
  refine ⟨e, hecase, ?_⟩
  have hpow : (AdjoinRoot.evalEval hPU.left a *
        AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ e =
      c ^ e * (AdjoinRoot.evalEval hU.left a *
        AdjoinRoot.evalEval hPU.left (enumVertical W val)) ^ e := by
    rw [hchar, mul_assoc, mul_pow]
  rw [hpow] at hcR
  have hcR' : AdjoinRoot.evalEval hR.left aP *
        AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p * c ^ e =
      c'' * AdjoinRoot.evalEval hU.left a ^ p *
        AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) := by
    refine mul_right_cancel₀
      (pow_ne_zero e (mul_ne_zero hUa hPUv)) ?_
    linear_combination hcR
  -- ── the ratio: `c''` cancels and leaves `c^e` (PROVEN glue)
  rw [mul_pow, mul_pow]
  linear_combination
    (AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) *
      AdjoinRoot.evalEval hU.left a ^ p) * hcQR -
    (AdjoinRoot.evalEval hQR.left ((CoordinateRing.XClass W xS) ^ p) *
      AdjoinRoot.evalEval hV.left a ^ p) * hcR'

/-- **Stage B, leaf 3, in the shape its characteristic-`p` caller supplies
(PROVEN).**  The old statement of `exists_millerRatio_eval_translationChar`,
recovered verbatim as a wrapper over
`exists_millerRatio_eval_translationChar_of_avoid` above.

The field hierarchy `F₁ ≤ F₂` enters only through the four abscissa separations
`x_S ∈ F₂`, `x_R ∉ F₂`, `x_{P⊕S} ∈ F₂`, `x_{Q⊕R} ∉ F₂`, which is exactly what the
four lines of proof below produce; `hF₁fin`, `hF₂fin`, `hF₁₂`, `hbad`, `hySF₂`,
`hxSF₁`, `hyPSF₂`, `hxPSF₁` were unused already and are kept only so that
`WeilPairing.translationChar_setup_value` does not have to change.  See the audit
in the docstring above. -/
theorem exists_millerRatio_eval_translationChar {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (hcard : Fintype.card ι = p ^ 2)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    {T' : W.Point}
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {xP yP : F} (hP : W.Nonsingular xP yP)
    {xQ yQ : F} (hQ : W.Nonsingular xQ yQ)
    (hT : (p : ℤ) • T' = WeierstrassCurve.Affine.Point.some xQ yQ hQ)
    {i₀ : ι} (hPval : val i₀ = WeierstrassCurve.Affine.Point.some xP yP hP)
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W (val i₀) + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {c : F} (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hτa : pointEval (constHom W) hκ.left a ≠ 0)
    (hτv : pointEval (constHom W) hκ.left (enumVertical W val) ≠ 0)
    (heq : pointEval (constHom W) hκ.left a *
        algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
      constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
        pointEval (constHom W) hκ.left (enumVertical W val))
    {xS yS : F} (hS : W.Nonsingular xS yS)
    {xR yR : F} (hR : W.Nonsingular xR yR)
    {xPS yPS : F} (hPS : W.Nonsingular xPS yPS)
    (hPSc : WeierstrassCurve.Affine.Point.some xPS yPS hPS =
      WeierstrassCurve.Affine.Point.some xP yP hP +
        WeierstrassCurve.Affine.Point.some xS yS hS)
    {xQR yQR : F} (hQR : W.Nonsingular xQR yQR)
    (hQRc : WeierstrassCurve.Affine.Point.some xQR yQR hQR =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
        WeierstrassCurve.Affine.Point.some xR yR hR)
    {aP : W.CoordinateRing}
    (haP : Ideal.span {aP} =
      (CoordinateRing.XYIdeal W xPS (Polynomial.C yPS)) ^ p *
        (CoordinateRing.XYIdeal W xS (Polynomial.C (W.negY xS yS))) ^ p)
    (hnzR : AdjoinRoot.evalEval hR.left aP ≠ 0)
    (hnzQR : AdjoinRoot.evalEval hQR.left aP ≠ 0)
    {F₁ F₂ : Subfield F} (_hF₁fin : (F₁ : Set F).Finite)
    (_hF₂fin : (F₂ : Set F).Finite) (_hF₁₂ : F₁ ≤ F₂)
    (_hbad : ∀ κ lam : W.Point, (p : ℤ) • κ = 0 → ((p ^ 2 : ℕ) : ℤ) • lam = 0 →
      ∀ (x y : F) (h : W.Nonsingular x y),
        WeierstrassCurve.Affine.Point.some x y h = T' + κ + lam ∨
          WeierstrassCurve.Affine.Point.some x y h = -κ + lam →
        x ∈ F₁ ∧ y ∈ F₁)
    (hxSF₂ : xS ∈ F₂) (_hySF₂ : yS ∈ F₂) (_hxSF₁ : xS ∉ F₁)
    (hxRF₂ : xR ∉ F₂) (hxPSF₂ : xPS ∈ F₂) (_hyPSF₂ : yPS ∈ F₂)
    (_hxPSF₁ : xPS ∉ F₁) (hxQRF₂ : xQR ∉ F₂)
    {S' R' P' : W.Point}
    (hS'p : (p : ℤ) • S' = WeierstrassCurve.Affine.Point.some xS yS hS)
    (hR'p : (p : ℤ) • R' = WeierstrassCurve.Affine.Point.some xR yR hR)
    (hP'p : (p : ℤ) • P' = WeierstrassCurve.Affine.Point.some xP yP hP)
    {xU yU : F} (hU : W.Nonsingular xU yU)
    {xV yV : F} (hV : W.Nonsingular xV yV)
    (hUeq : WeierstrassCurve.Affine.Point.some xU yU hU = S' - R')
    (hVeq : WeierstrassCurve.Affine.Point.some xV yV hV = P' + (S' - R'))
    (hUa : AdjoinRoot.evalEval hU.left a ≠ 0)
    (hUv : AdjoinRoot.evalEval hU.left (enumVertical W val) ≠ 0)
    (hVa : AdjoinRoot.evalEval hV.left a ≠ 0)
    (hVv : AdjoinRoot.evalEval hV.left (enumVertical W val) ≠ 0) :
    ∃ e : ℕ, (e = 1 ∨ e = p - 1) ∧
      AdjoinRoot.evalEval hQR.left aP *
          AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) *
          (AdjoinRoot.evalEval hU.left a *
            AdjoinRoot.evalEval hV.left (enumVertical W val)) ^ p =
        c ^ e * (AdjoinRoot.evalEval hQR.left
              ((CoordinateRing.XClass W xS) ^ p) *
            AdjoinRoot.evalEval hR.left aP *
            (AdjoinRoot.evalEval hV.left a *
              AdjoinRoot.evalEval hU.left (enumVertical W val)) ^ p) :=
  exists_millerRatio_eval_translationChar_of_avoid hΔ hp hval_inj hval_tor
    hval_surj hcard ha hspan hP hQ hT hPval hpt hc1 hcp hτa hτv heq hS hR hPS
    hPSc hQR hQRc haP hnzR hnzQR
    (fun h => hxRF₂ (by rw [← h]; exact hxSF₂))
    (fun h => hxQRF₂ (by rw [h]; exact hxSF₂))
    (fun h => hxQRF₂ (by rw [h]; exact hxPSF₂))
    (fun h => hxRF₂ (by rw [h]; exact hxPSF₂))
    hS'p hR'p hP'p hU hV hUeq hVeq hUa hUv hVa hVv

end WeilPairing
