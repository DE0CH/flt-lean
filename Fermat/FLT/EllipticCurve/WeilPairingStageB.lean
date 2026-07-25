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

/-- **Stage B, leaf 1 (sorry node): a generic `p`-division offset.**
Given the Miller data (`Q = p•T'`, `a` generating
`∏_κ I_{T'⊕κ}·I_{⊖κ}`), a `p`-torsion point `P`, and the setup's
`S` (abscissa and ordinate in the big field `F₂`) and `R` (abscissa
NOT in `F₂`), there are `p`-division points `S'`, `R'`, `P'` of
`S`, `R`, `P` for which the offset `U := S' ⊖ R'` and its
`P'`-translate `V := P' ⊕ U` are affine points at which neither the
Miller generator `a` nor the vertical product
`v = ∏_κ (X − x_κ)` vanishes — i.e. `g = a/v` is defined and nonzero
at both, as the two evaluation stages require.

Proof plan.  `p`-division points exist by
`TorsionCard.smul_surjective` (`(p : F) ≠ 0`, `F` separably closed).
For the genericity, note `evalEval` at an affine point `ξ` kills `a`
exactly when `ξ` lies in the divisor support
`{T'⊕κ} ∪ {⊖κ}` (the point ideal at `ξ` divides `span {a}` —
`hspan` — and point ideals are the maximal ideals of the coordinate
ring), and kills `v` exactly when `ξ = ±κ` for some `κ ∈ E[p]`.  So
suppose `U` (resp. `V`) is bad, i.e. `U = w` (resp. `P' ⊕ U = w`) for
one of the finitely many `w` in that support.  Applying `[p]`:
`S ⊖ R = p•w` (resp. `S ⊖ R = p•w ⊖ P`), so
`S = R ⊕ (p•w)` (resp. `S = R ⊕ (p•w ⊖ P)`) with the translating
point's coordinates in `F₁ ≤ F₂` by `hbad` (`λ = O`, and `P = ⊖(⊖P)`
is `p`-torsion, so its coordinates are covered as well) — hence
`R = S ⊖ (that point)` would have both coordinates in the subfield
`F₂` by the addition formulas, contradicting `xR ∉ F₂`.  The same
argument excludes `U = O` (`S = R`) and `V = O` (`S = R ⊖ P`). -/
theorem exists_generic_pDivision_offset {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Z : W.Point, (p : ℤ) • Z = 0 → ∃ i, val i = Z)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' Q : W.Point} (hT : (p : ℤ) • T' = Q) (hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {F₁ F₂ : Subfield F} (hF₁fin : (F₁ : Set F).Finite)
    (hF₂fin : (F₂ : Set F).Finite) (hF₁₂ : F₁ ≤ F₂)
    (hbad : ∀ κ lam : W.Point, (p : ℤ) • κ = 0 → ((p ^ 2 : ℕ) : ℤ) • lam = 0 →
      ∀ (x y : F) (h : W.Nonsingular x y),
        WeierstrassCurve.Affine.Point.some x y h = T' + κ + lam ∨
          WeierstrassCurve.Affine.Point.some x y h = -κ + lam →
        x ∈ F₁ ∧ y ∈ F₁)
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
  sorry

/-- **Stage B, leaf 2 (sorry node): the `[p]`-pullback evaluation of
the `Q`-side Miller ratio.**  With `f_Q = aQ/(X − x_R)^p`
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
hypotheses `hnzS`/`hnzPS` place `S`, `P⊕S` off `div f_Q`. -/
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
  sorry

/-- **Stage B, leaf 3 (sorry node): the mirror side — Weil reciprocity
and the level-`p²` telescope.**  With `f_P = aP/(X − x_S)^p`
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
keeps off `div g`. -/
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
  sorry

end WeilPairing
