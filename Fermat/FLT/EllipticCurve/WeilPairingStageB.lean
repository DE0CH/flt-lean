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
  {W : WeierstrassCurve.Affine F} {p : ℕ} [Fact p.Prime]

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

omit [Fact p.Prime] in
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
coefficients. -/
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
  set Sp : W.Point := WeierstrassCurve.Affine.Point.some xS yS hS with hSpdef
  set Rp : W.Point := WeierstrassCurve.Affine.Point.some xR yR hR with hRpdef
  set Qp : W.Point := WeierstrassCurve.Affine.Point.some xQ yQ hQ with hQpdef
  have hSG : Sp ∈ G := hGin xS yS hS hxSF₂ hySF₂
  have hQG : Qp ∈ G := hGin xQ yQ hQ (hF₁₂ hxQF₁) (hF₁₂ hyQF₁)
  have hPG : P ∈ G := by
    cases hPc : P with
    | zero => exact zero_mem G
    | some x y h =>
      obtain ⟨hx, hy⟩ := hbad (-P) 0 (by rw [smul_neg, hPtor, neg_zero])
        (by rw [smul_zero]) x y h
        (Or.inr (by rw [neg_neg, add_zero]; exact hPc.symm))
      exact hGin x y h (hF₁₂ hx) (hF₁₂ hy)
  -- the contradiction engine: `S ⊖ R` cannot be `F₂`-rational
  have hkey : ∀ t : W.Point, t ∈ G → Sp - Rp ≠ t := by
    intro t ht hc
    have hRG : Rp ∈ G := by
      have hrw : Rp = Sp - t := by rw [← hc]; abel
      rw [hrw]
      exact sub_mem hSG ht
    exact hxRF₂ (hGout xR yR hR hRG).1
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
      refine absurd ?_ (hkey 0 (zero_mem G))
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
      refine absurd ?_ (hkey (-P) (neg_mem hPG))
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    | some x y h => exact ⟨x, y, h, rfl⟩
  refine ⟨S', R', P', hS', hR', hP', xU, yU, hU, xV, yV, hV, hUeq, hVeq,
    ?_, ?_, ?_, ?_⟩
  · intro h0
    rcases hbadZ xU yU hU (Or.inl h0) with hz | hz
    · exact hkey 0 (zero_mem G) (by rw [← hpU, ← hUeq, hz])
    · exact hkey Qp hQG (by rw [← hpU, ← hUeq, hz])
  · intro h0
    rcases hbadZ xU yU hU (Or.inr h0) with hz | hz
    · exact hkey 0 (zero_mem G) (by rw [← hpU, ← hUeq, hz])
    · exact hkey Qp hQG (by rw [← hpU, ← hUeq, hz])
  · intro h0
    rcases hbadZ xV yV hV (Or.inl h0) with hz | hz
    · refine hkey (-P) (neg_mem hPG) ?_
      have h1 : P + (Sp - Rp) = 0 := by rw [← hpV, ← hVeq, hz]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    · refine hkey (Qp - P) (sub_mem hQG hPG) ?_
      have h1 : P + (Sp - Rp) = Qp := by rw [← hpV, ← hVeq, hz]
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1
  · intro h0
    rcases hbadZ xV yV hV (Or.inr h0) with hz | hz
    · refine hkey (-P) (neg_mem hPG) ?_
      have h1 : P + (Sp - Rp) = 0 := by rw [← hpV, ← hVeq, hz]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h1
    · refine hkey (Qp - P) (sub_mem hQG hPG) ?_
      have h1 : P + (Sp - Rp) = Qp := by rw [← hpV, ← hVeq, hz]
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1

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

STAGING (2026-07-25): DECOMPOSED.  What is left sorried is exactly the
analytic content — the existence of the pullback constant `c'` together
with the two BALANCED HALVES it satisfies, i.e. `f_Q∘[p] = c'·(g∘τ_{⊖R'})^p`
read at `P'⊕S'` and at `S'` and cleared of denominators.  The
cross-multiplication that cancels `c'` and produces the conclusion above
is proven glue (`linear_combination`).  Note `ha`, `hΔ`, `hp`, `hcard`,
`hval_*`, `hT`, `hPtor` and the `S'`/`R'`/`P'` data are the inputs of
that sub-leaf, not of the glue. -/
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
  -- ── THE ANALYTIC SUB-LEAF (sorry): the two balanced halves of the
  --    `[p]`-pullback evaluation, against their COMMON constant `c'`.
  --    `f_Q∘[p] = c'·(g∘τ_{⊖R'})^p` (the L4-7 multiplicity-one span
  --    comparison), evaluated at `P'⊕S'` and at `S'` — whose `[p]`-images
  --    are `P⊕S` and `S` and whose `τ_{⊖R'}`-shifts are `V` and `U`.
  --    Cleared of denominators, that is exactly the pair below; the
  --    unknown `c'` cancels in the ratio, which is the glue after it.
  obtain ⟨c', hcPS, hcS⟩ :
      ∃ c' : F,
        AdjoinRoot.evalEval hPS.left aQ *
            AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p =
          c' * AdjoinRoot.evalEval hV.left a ^ p *
            AdjoinRoot.evalEval hPS.left ((CoordinateRing.XClass W xR) ^ p) ∧
        AdjoinRoot.evalEval hS.left aQ *
            AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p =
          c' * AdjoinRoot.evalEval hU.left a ^ p *
            AdjoinRoot.evalEval hS.left ((CoordinateRing.XClass W xR) ^ p) := by
    sorry
  -- ── the ratio: `c'` cancels (PROVEN glue)
  rw [mul_pow, mul_pow]
  linear_combination
    (AdjoinRoot.evalEval hS.left ((CoordinateRing.XClass W xR) ^ p) *
      AdjoinRoot.evalEval hU.left a ^ p) * hcPS -
    (AdjoinRoot.evalEval hPS.left ((CoordinateRing.XClass W xR) ^ p) *
      AdjoinRoot.evalEval hV.left a ^ p) * hcS

/-- **Stage B, leaf 3 (ONE sorried sub-leaf + proven glue): the mirror
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

STAGING (2026-07-25): DECOMPOSED, in the same balanced-halves shape as
leaf 2.  What is left sorried is the existence of the reciprocity
constant `c''` and of the exponent `e ∈ {1, p−1}` such that the two
half-evaluations of `f_P` — at `Q⊕R` and at `R` — hold against that one
constant, the whole discrepancy between them being the single character
factor `c^e`.  That IS the output of the reciprocity-plus-telescope
computation; the cross-multiplication cancelling `c''` and leaving
`c^e` is proven glue (`linear_combination`).  Unlike leaf 2 the two
halves are NOT a pullback comparison — `div f_P = p(P⊕S) − p(S)` pulls
back to translates of the `[p]`-fibres of `P⊕S` and `S`, not to a
translate of `div g` — which is exactly why a character factor appears
between them. -/
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
    {F₁ F₂ : Subfield F} (hF₁fin : (F₁ : Set F).Finite)
    (hF₂fin : (F₂ : Set F).Finite) (hF₁₂ : F₁ ≤ F₂)
    (hbad : ∀ κ lam : W.Point, (p : ℤ) • κ = 0 → ((p ^ 2 : ℕ) : ℤ) • lam = 0 →
      ∀ (x y : F) (h : W.Nonsingular x y),
        WeierstrassCurve.Affine.Point.some x y h = T' + κ + lam ∨
          WeierstrassCurve.Affine.Point.some x y h = -κ + lam →
        x ∈ F₁ ∧ y ∈ F₁)
    (hxSF₂ : xS ∈ F₂) (hySF₂ : yS ∈ F₂) (hxSF₁ : xS ∉ F₁)
    (hxRF₂ : xR ∉ F₂) (hxPSF₂ : xPS ∈ F₂) (hyPSF₂ : yPS ∈ F₂)
    (hxPSF₁ : xPS ∉ F₁) (hxQRF₂ : xQR ∉ F₂)
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
  -- ── THE ANALYTIC SUB-LEAF (sorry): the mirror side, in the same
  --    balanced-halves form as leaf 2.  Weil reciprocity between `f_P`
  --    and `g` plus the level-`p²` telescope produce the two evaluations
  --    of `f_P` at `Q⊕R` and at `R` against ONE common constant `c''` —
  --    the reciprocity constant — with the whole discrepancy between the
  --    halves carried by the single character factor `c^e`, `e ∈ {1, p−1}`
  --    (the orientation ambiguity of the pairing).  Cleared of
  --    denominators that is exactly the pair below; `c''` cancels in the
  --    ratio, leaving `c^e`, which is the glue after it.
  obtain ⟨e, hecase, c'', hcQR, hcR⟩ :
      ∃ (e : ℕ), (e = 1 ∨ e = p - 1) ∧ ∃ c'' : F,
        AdjoinRoot.evalEval hQR.left aP *
            AdjoinRoot.evalEval hV.left (enumVertical W val) ^ p =
          c'' * AdjoinRoot.evalEval hV.left a ^ p *
            AdjoinRoot.evalEval hQR.left ((CoordinateRing.XClass W xS) ^ p) ∧
        AdjoinRoot.evalEval hR.left aP *
            AdjoinRoot.evalEval hU.left (enumVertical W val) ^ p * c ^ e =
          c'' * AdjoinRoot.evalEval hU.left a ^ p *
            AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) := by
    sorry
  -- ── the ratio: `c''` cancels and leaves `c^e` (PROVEN glue)
  refine ⟨e, hecase, ?_⟩
  rw [mul_pow, mul_pow]
  linear_combination
    (AdjoinRoot.evalEval hR.left ((CoordinateRing.XClass W xS) ^ p) *
      AdjoinRoot.evalEval hU.left a ^ p) * hcQR -
    (AdjoinRoot.evalEval hQR.left ((CoordinateRing.XClass W xS) ^ p) *
      AdjoinRoot.evalEval hV.left a ^ p) * hcR

end WeilPairing
