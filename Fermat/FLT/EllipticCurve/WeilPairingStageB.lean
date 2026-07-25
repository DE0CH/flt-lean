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

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Constants evaluate to themselves** (PROVEN): `coordEval_coordC` in
the `AdjoinRoot.evalEval` spelling the Stage-B statements use
(`coordEval W h` is by definition `AdjoinRoot.evalEval h`). -/
lemma evalEval_coordC {x y : F} (h : W.Equation x y) (d : F) :
    AdjoinRoot.evalEval h (coordC W d) = d :=
  coordEval_coordC (W := W) h d

/-- **Stage B substrate leaf (SORRY): specialization of a generic
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

Proof route.  `pointEval` is determined by where it sends the two
coordinate atoms (`coordinateRing_ringHom_ext`), so it suffices to
produce `n`, `d` for `z = coordX` and `z = coordY` and close the family
under the ring operations (a common denominator is a product of the
individual ones).  For those two atoms `n/d` is read off the group-law
formulas: `x(Q ⊕ m•taut)` and `y(Q ⊕ m•taut)` are the `addX`/`addY`
expressions in `x(m•taut) = Φ_m/ΨSq_m`, `y(m•taut)`, `x(Q)`, `y(Q)` and
the slope, all of which are fractions of coordinate-ring elements; the
denominators are powers of `ΨSq_m(coordX)` and of the vertical
`coordX − x(Q)` (resp. the tangent normalisation when `Z = ±Q`, the case
already isolated by `vertNumerator_self_tangent` /
`vertNumerator_self_vertical` in `WeilPairingDescent.lean`).  Their
non-vanishing at `Z` is exactly the affineness of `Q ⊕ m•Z`, i.e.
`hZ'c`, and the value identity `n(Z) = z(Z')·d(Z)` is the statement that
the group law commutes with evaluation — the same
`Point.some`-coordinate computation that `endoMap_add` performs one
level up.

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
  sorry

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

STAGING (2026-07-25, re-cut): DECOMPOSED, in the same balanced-halves
shape as leaf 2, over the sorried reciprocity output plus the SHARED
specialization brick `exists_pointEval_specialization`.

What is left sorried is the existence of the reciprocity constant `c''`
and of the exponent `e ∈ {1, p−1}` such that the two half-evaluations of
`f_P` — at `Q⊕R` and at `R` — hold against that one constant, the whole
discrepancy between them being the `e`-th power of the `g`-RATIO
`g(P⊕U)/g(U)`.  Writing the discrepancy that way rather than as `c^e` is
what makes the telescope proven glue rather than part of the sorry: the
level-`p²` telescope
`∏_{j<p} g((j+1)P'⊕U)/g(jP'⊕U) = g(P⊕U)/g(U)` is a formal cancellation,
and its value `c` is the CHARACTER equation `heq` read at the point `U`
— which is exactly one application of the specialization brick, proven
below.  Unlike leaf 2 the two halves are NOT a pullback comparison —
`div f_P = p(P⊕S) − p(S)` pulls back to translates of the `[p]`-fibres
of `P⊕S` and `S`, not to a translate of `div g` — which is why a
character factor appears between them at all.

Also proven here, from the field separation `xS ∈ F₂`, `xR ∉ F₂`: the
telescope's base point `P⊕U` is affine and off `div g`
(`p•(P⊕U) = S ⊖ R ≠ O`, so it is not `p`-torsion and the vertical
product does not vanish there), which is what lets the character
equation be read at `U` at all. -/
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
  -- ── PROVEN: `S ≠ R`, since `F₂` separates their abscissae
  have hxSR : xS ≠ xR := fun h => hxRF₂ (h ▸ hxSF₂)
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
  -- ── THE ANALYTIC SUB-LEAF (sorry): the mirror side, in the same
  --    balanced-halves form as leaf 2.  Weil reciprocity between `f_P`
  --    and `g` produces the two evaluations of `f_P` at `Q⊕R` and at `R`
  --    against ONE common constant `c''` — the reciprocity constant —
  --    with the whole discrepancy between the halves carried by the
  --    `e`-th power of the `g`-ratio `g(P⊕U)/g(U)`, `e ∈ {1, p−1}` (the
  --    orientation ambiguity of the pairing).  Cleared of denominators
  --    that is exactly the pair below; `hchar` identifies that ratio with
  --    the character value `c`, and `c''` cancels in the ratio, leaving
  --    `c^e` — both of which are the glue after it.
  obtain ⟨e, hecase, c'', hcQR, hcR⟩ :
      ∃ (e : ℕ), (e = 1 ∨ e = p - 1) ∧ ∃ c'' : F,
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
    sorry
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

end WeilPairing
