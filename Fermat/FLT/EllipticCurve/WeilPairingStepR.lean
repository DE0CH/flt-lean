/-
WeilPairingStepR.lean — the R-side telescoping step of the Weil-pairing
reciprocity argument (`WeilPairing.stepR`), extracted verbatim from the
proof of `exists_weilPairing_mu` (WeilPairing.lean) so that this very
heavy block (two machine-generated mega `linear_combination`s) elaborates
once in its own module. The engine facts it consumes — proved inside the
μ-theorem's body — are taken as hypotheses; the μ-theorem instantiates
them with its local `have`s.

The lemma is stated over an ARBITRARY subfield `F'` with exactly the
membership/avoidance facts the proof uses (no finiteness, no `F ≤ F'`),
so that the mirrored S-side step can be obtained from the same lemma by
the σ-transposition P↔Q, (S₁,PS₁,S₃,PS₃)↔(R₃,QR₃,S-family) at a
different field — see the hstepS notes in HANDOFF-SESSION.md.
-/
module

public import Fermat.FLT.EllipticCurve.Torsion
public import Fermat.FLT.GaloisRepresentation.Chebotarev
public import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

@[expose] public section

namespace WeilPairing

open WeierstrassCurve

/-- A classical decidable-equality instance on the algebraic closure of
`𝔽_q` (needed for the group law on points). Declared here (the deepest
module of the Weil-pairing development) and re-exported up the chain. -/
noncomputable instance instDecEqAlgClosureZMod (q : ℕ) [Fact q.Prime] :
    DecidableEq (AlgebraicClosure (ZMod q)) := Classical.typeDecidableEq _

set_option maxHeartbeats 16000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem stepR (q p : ℕ) [Fact q.Prime]
    (Wb : WeierstrassCurve (AlgebraicClosure (ZMod q)))
    (yfib : AlgebraicClosure (ZMod q) → AlgebraicClosure (ZMod q))
    (hyfib : ∀ c : AlgebraicClosure (ZMod q), Wb.toAffine.Equation c (yfib c))

    (hCunits : ∀ u : Wb.toAffine.CoordinateRing, IsUnit u →
        ∃ c : (AlgebraicClosure (ZMod q)), c ≠ 0 ∧ u = AdjoinRoot.of Wb.toAffine.polynomial
          (Polynomial.C c))
    (hline : ∀ (x₁ y₁ x₂ y₂ : (AlgebraicClosure (ZMod q)))
        (h₁ : Wb.toAffine.Nonsingular x₁ y₁)
        (h₂ : Wb.toAffine.Nonsingular x₂ y₂)
        (hxy : ¬(x₁ = x₂ ∧ y₁ = Wb.toAffine.negY x₂ y₂)),
        WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial x₁ y₁
            (Wb.toAffine.slope x₁ x₂ y₁ y₂)) =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₁
          (Polynomial.C y₁) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine x₂
          (Polynomial.C y₂) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
          (Polynomial.C (Wb.toAffine.negY
            (Wb.toAffine.addX x₁ x₂ (Wb.toAffine.slope x₁ x₂ y₁ y₂))
            (Wb.toAffine.addY x₁ x₂ y₁ (Wb.toAffine.slope x₁ x₂ y₁ y₂)))))
    (hoffdiv : ∀ (f : Wb.toAffine.CoordinateRing),
        ∀ D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))),
        (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
        Ideal.span {f} =
          (D.map (fun P => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2))).prod →
        ∀ (x₂ y₂ : (AlgebraicClosure (ZMod q))) (hE₂ : Wb.toAffine.Equation x₂ y₂), (x₂, y₂) ∉ D →
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE₂ f ≠ 0)
    (hevvert : ∀ (c x y : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x y),
        AdjoinRoot.evalEval (p := Wb.toAffine.polynomial) hE
          (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine c) =
        x - c)
    (hnegYF : ∀ (F : Subfield (AlgebraicClosure (ZMod q)))
        (x y : (AlgebraicClosure (ZMod q))), x ∈ F → y ∈ F →
        Wb.toAffine.negY x y ∈ F)
    (hgenfac : ∀ (n : ℕ) (f : Wb.toAffine.CoordinateRing)
        (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (F : Subfield (AlgebraicClosure (ZMod q))), D.card ≤ n →
        (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
        (∀ P ∈ D, P.1 ∈ F ∧ P.2 ∈ F) →
        Ideal.span {f} = (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2))).prod →
        ∃ (Ln Ld : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) (Vn Vd : Multiset (AlgebraicClosure (ZMod q)))
          (u : (AlgebraicClosure (ZMod q))), u ≠ 0 ∧
          (∀ P ∈ Ln + Ld, P.1 ∈ F ∧ P.2 ∈ F) ∧
          (∀ c ∈ Vn + Vd, c ∈ F) ∧
          (∀ ln ∈ Ln + Ld, ∀ x ∈ ((Polynomial.X ^ 3
          + Polynomial.C (Wb.toAffine.a₂ - (ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))).1 ^ 2 - Wb.toAffine.a₁ * ln.1)
            * Polynomial.X ^ 2
          + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
              - Wb.toAffine.a₃ * ln.1) * Polynomial.X
          + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots, x ∈ F) ∧
          f * (Ld.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vd.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod =
          AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C u) *
            (Ln.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vn.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod)
    (hww : ∀ (L₁ L₂ : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (V₁ V₂ : Multiset (AlgebraicClosure (ZMod q))),
        (((L₂.bind (fun ln => ((Polynomial.X ^ 3
          + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
            * Polynomial.X ^ 2
          + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
              - Wb.toAffine.a₃ * ln.1) * Polynomial.X
          + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
            (fun x => (x, ln.1 * x + ln.2)))) +
          (V₂.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
            (c', yfib c')}))).map
              (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                (L₁.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  T.2 - (ab.1 * T.1 + ab.2))).prod *
                (V₁.map (fun cv => T.1 - cv)).prod)).prod =
        (-1) ^ (Multiset.card L₁ * Multiset.card L₂) *
          (((L₁.bind (fun ab => ((Polynomial.X ^ 3
          + Polynomial.C (Wb.toAffine.a₂ - ab.1 ^ 2 - Wb.toAffine.a₁ * ab.1)
            * Polynomial.X ^ 2
          + Polynomial.C (Wb.toAffine.a₄ - 2 * ab.1 * ab.2 - Wb.toAffine.a₁ * ab.2
              - Wb.toAffine.a₃ * ab.1) * Polynomial.X
          + Polynomial.C (Wb.toAffine.a₆ - ab.2 ^ 2 - Wb.toAffine.a₃ * ab.2))).roots.map
            (fun x => (x, ab.1 * x + ab.2)))) +
          (V₁.bind (fun cv => {(cv, Wb.toAffine.negY cv (yfib cv)),
            (cv, yfib cv)}))).map
              (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                (L₂.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  T.2 - (ln.1 * T.1 + ln.2))).prod *
                (V₂.map (fun c' => T.1 - c')).prod)).prod)
    (hbaldiv : ∀ (f : Wb.toAffine.CoordinateRing)
        (D : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (Ln Ld : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (Vn Vd : Multiset (AlgebraicClosure (ZMod q)))
        (u : (AlgebraicClosure (ZMod q))), u ≠ 0 →
        (∀ P ∈ D, Wb.toAffine.Equation P.1 P.2) →
        Ideal.span {f} = (D.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => WeierstrassCurve.Affine.CoordinateRing.XYIdeal
            Wb.toAffine P.1 (Polynomial.C P.2))).prod →
        f * (Ld.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vd.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod =
          AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C u) *
            (Ln.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vn.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod →
        D + ((Ld.bind (fun ln => ((Polynomial.X ^ 3
          + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
            * Polynomial.X ^ 2
          + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
              - Wb.toAffine.a₃ * ln.1) * Polynomial.X
          + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
            (fun x => (x, ln.1 * x + ln.2)))) +
          (Vd.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
            (c', yfib c')}))) =
        ((Ln.bind (fun ln => ((Polynomial.X ^ 3
          + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1)
            * Polynomial.X ^ 2
          + Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2
              - Wb.toAffine.a₃ * ln.1) * Polynomial.X
          + Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2))).roots.map
            (fun x => (x, ln.1 * x + ln.2)))) +
          (Vn.bind (fun c' => {(c', Wb.toAffine.negY c' (yfib c')),
            (c', yfib c')}))))
    (hevconst : ∀ (u : (AlgebraicClosure (ZMod q)))
        (x y : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x y),
        AdjoinRoot.evalEval hE (AdjoinRoot.of Wb.toAffine.polynomial
          (Polynomial.C u)) = u)
    (hevid : ∀ (f : Wb.toAffine.CoordinateRing)
        (Ln Ld : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        (Vn Vd : Multiset (AlgebraicClosure (ZMod q)))
        (u : (AlgebraicClosure (ZMod q))),
        f * (Ld.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vd.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod =
          AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C u) *
            (Ln.map (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => AdjoinRoot.mk Wb.toAffine.polynomial
          (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
            Polynomial.C P.2)))).prod * (Vn.map (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod →
        ∀ (x y : (AlgebraicClosure (ZMod q))) (hE : Wb.toAffine.Equation x y),
        AdjoinRoot.evalEval hE f *
          ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => y - (ln.1 * x + ln.2))).prod *
           (Vd.map (fun c => x - c)).prod) =
        u * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => y - (ln.1 * x + ln.2))).prod *
           (Vn.map (fun c => x - c)).prod))
    (hfib2 : ∀ (c y : (AlgebraicClosure (ZMod q))),
        Wb.toAffine.Equation c y →
        y = yfib c ∨ y = Wb.toAffine.negY c (yfib c))
    (F' : Subfield (AlgebraicClosure (ZMod q)))
    (xQ yQ : AlgebraicClosure (ZMod q))
    (hQ : Wb.toAffine.Nonsingular xQ yQ)
    (xS₁ yS₁ : AlgebraicClosure (ZMod q))
    (hS₁ : Wb.toAffine.Nonsingular xS₁ yS₁)
    (hxS₁F' : xS₁ ∈ F') (hyS₁F' : yS₁ ∈ F')
    (xR₁ yR₁ : AlgebraicClosure (ZMod q))
    (hR₁ : Wb.toAffine.Nonsingular xR₁ yR₁)
    (hxR₁ : xR₁ ∉ F')
    (xPS₁ yPS₁ : AlgebraicClosure (ZMod q))
    (hPS₁ : Wb.toAffine.Nonsingular xPS₁ yPS₁)
    (hxPS₁F' : xPS₁ ∈ F') (hyPS₁F' : yPS₁ ∈ F')
    (xQR₁ yQR₁ : AlgebraicClosure (ZMod q))
    (hQR₁ : Wb.toAffine.Nonsingular xQR₁ yQR₁)
    (hQRc₁ : WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
      WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁)
    (hxQR₁nS : xQR₁ ≠ xS₁) (hxQR₁F' : xQR₁ ∉ F')
    (aP₁ aQ₁ : Wb.toAffine.CoordinateRing)
    (haP₁ : Ideal.span {aP₁} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xPS₁ (Polynomial.C yPS₁)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xS₁ (Polynomial.C (Wb.toAffine.negY xS₁ yS₁))) ^ p)
    (haQ₁ : Ideal.span {aQ₁} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xQR₁ (Polynomial.C yQR₁)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁))) ^ p)
    (xR₃ yR₃ : AlgebraicClosure (ZMod q))
    (hR₃ : Wb.toAffine.Nonsingular xR₃ yR₃)
    (hxR₃ : xR₃ ∉ F')
    (xQR₃ yQR₃ : AlgebraicClosure (ZMod q))
    (hQR₃ : Wb.toAffine.Nonsingular xQR₃ yQR₃)
    (hxQR₃ : xQR₃ ∉ F')
    (hQRc₃ : WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
      WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃)
    (aQ₃ : Wb.toAffine.CoordinateRing)
    (haQ₃ : Ideal.span {aQ₃} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xQR₃ (Polynomial.C yQR₃)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xR₃ (Polynomial.C (Wb.toAffine.negY xR₃ yR₃))) ^ p)
    (xM yM : AlgebraicClosure (ZMod q))
    (hM : Wb.toAffine.Nonsingular xM yM)
    (hMc : WeierstrassCurve.Affine.Point.some xM yM hM =
      WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ +
      WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃)
    (hxMF' : xM ∉ F') :
    (AdjoinRoot.evalEval hQR₁.left aP₁ *
      AdjoinRoot.evalEval hR₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₁ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p)) *
    (AdjoinRoot.evalEval hQR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hR₃.left aP₁ *
      AdjoinRoot.evalEval hS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
      AdjoinRoot.evalEval hPS₁.left aQ₃) =
    (AdjoinRoot.evalEval hQR₃.left aP₁ *
      AdjoinRoot.evalEval hR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₃ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) *
    (AdjoinRoot.evalEval hQR₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hR₁.left aP₁ *
      AdjoinRoot.evalEval hS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p) *
      AdjoinRoot.evalEval hPS₁.left aQ₁) := by
  -- the σ-companion points
  have hR₁neg : Wb.toAffine.Nonsingular xR₁ (Wb.toAffine.negY xR₁ yR₁) :=
    (WeierstrassCurve.Affine.nonsingular_neg xR₁ yR₁).mpr hR₁
  have hQR₃neg : Wb.toAffine.Nonsingular xQR₃
      (Wb.toAffine.negY xQR₃ yQR₃) :=
    (WeierstrassCurve.Affine.nonsingular_neg xQR₃ yQR₃).mpr hQR₃
  have hS₁neg : Wb.toAffine.Nonsingular xS₁ (Wb.toAffine.negY xS₁ yS₁) :=
    (WeierstrassCurve.Affine.nonsingular_neg xS₁ yS₁).mpr hS₁
  -- the zero-sum comparison element: (Q⊕R₁) ⊖ R₁ ⊕ R₃ ⊖ (Q⊕R₃) = 0,
  -- so the four-point ideal product is principal (multiplicity one)
  have htex : ∃ t : Wb.toAffine.CoordinateRing,
      Ideal.span {t} =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₁ (Polynomial.C yQR₁) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C yR₃) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C (Wb.toAffine.negY xQR₃ yQR₃)) := by
    -- the four points sum to zero
    have h1 : (WeierstrassCurve.Affine.Point.some xR₁
        (Wb.toAffine.negY xR₁ yR₁) hR₁neg : Wb.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁) :=
      (WeierstrassCurve.Affine.Point.neg_some hR₁).symm
    have h2 : (WeierstrassCurve.Affine.Point.some xQR₃
        (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg : Wb.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃) :=
      (WeierstrassCurve.Affine.Point.neg_some hQR₃).symm
    have hsum : (WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ +
        WeierstrassCurve.Affine.Point.some xR₁
          (Wb.toAffine.negY xR₁ yR₁) hR₁neg +
        WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃ +
        WeierstrassCurve.Affine.Point.some xQR₃
          (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg :
        Wb.toAffine.Point) = 0 := by
      rw [h1, h2, hQRc₁, hQRc₃]
      abel
    -- the class of the four-fold product is trivial
    have hcl := congrArg WeierstrassCurve.Affine.Point.toClass hsum
    rw [map_zero, map_add, map_add, map_add,
      WeierstrassCurve.Affine.Point.toClass_some,
      WeierstrassCurve.Affine.Point.toClass_some,
      WeierstrassCurve.Affine.Point.toClass_some,
      WeierstrassCurve.Affine.Point.toClass_some] at hcl
    have hmk : ClassGroup.mk Wb.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₁ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₁neg *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₃ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₃neg) = 1 := by
      rw [map_mul, map_mul, map_mul]
      exact hcl
    rw [ClassGroup.mk_eq_one_iff] at hmk
    obtain ⟨tK, htK⟩ := hmk.principal
    have hUt : (((WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₁ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₁neg *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₃ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₃neg :
        (FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)ˣ) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)) =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors Wb.toAffine.CoordinateRing) tK :=
      FractionalIdeal.coeToSubmodule_injective (by
        beta_reduce
        rw [FractionalIdeal.coe_spanSingleton]
        exact htK)
    have hUcoe : (((WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₁ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₁neg *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hR₃ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' hQR₃neg :
        (FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)ˣ) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)) =
        ((WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₁ (Polynomial.C yQR₁) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C yR₃) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C (Wb.toAffine.negY xQR₃ yQR₃)) :
          Ideal Wb.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul,
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq,
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq,
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq,
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq,
        ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
        ← FractionalIdeal.coeIdeal_mul]
    have hmem : tK ∈ ((( WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine xQR₁ (Polynomial.C yQR₁) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C yR₃) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C (Wb.toAffine.negY xQR₃ yQR₃)) :
          Ideal Wb.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)) := by
      rw [← hUcoe, hUt]
      exact FractionalIdeal.mem_spanSingleton_self _ _
    obtain ⟨t, htI, htmap⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
    refine ⟨t, ?_⟩
    have hspan : ((Ideal.span {t} : Ideal Wb.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField) =
        ((( WeierstrassCurve.Affine.CoordinateRing.XYIdeal
          Wb.toAffine xQR₁ (Polynomial.C yQR₁) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C yR₃) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C (Wb.toAffine.negY xQR₃ yQR₃)) :
          Ideal Wb.toAffine.CoordinateRing) :
        FractionalIdeal (nonZeroDivisors Wb.toAffine.CoordinateRing)
          Wb.toAffine.FunctionField)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, htmap, ← hUcoe, hUt]
    exact FractionalIdeal.coeIdeal_injective hspan
  obtain ⟨t, ht⟩ := htex
  -- the function comparison: aQ₁ and aQ₃ differ by the p-th power of
  -- the comparison element and verticals, up to a constant
  have hcomp : ∃ c : (AlgebraicClosure (ZMod q)), c ≠ 0 ∧
      aQ₁ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xQR₃) ^ p *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xR₃) ^ p =
      AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C c) *
        (aQ₃ * t ^ p) := by
    have hvQR₃ : Ideal.span {(WeierstrassCurve.Affine.CoordinateRing.XClass
        Wb.toAffine xQR₃ : Wb.toAffine.CoordinateRing)} =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C (Wb.toAffine.negY xQR₃ yQR₃)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xQR₃ (Polynomial.C yQR₃) :=
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
        (W := Wb.toAffine) hQR₃).symm
    have hvR₃ : Ideal.span {(WeierstrassCurve.Affine.CoordinateRing.XClass
        Wb.toAffine xR₃ : Wb.toAffine.CoordinateRing)} =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C (Wb.toAffine.negY xR₃ yR₃)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xR₃ (Polynomial.C yR₃) :=
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
        (W := Wb.toAffine) hR₃).symm
    have hspaneq : Ideal.span {aQ₁ *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xQR₃) ^ p *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xR₃) ^ p} = Ideal.span {aQ₃ * t ^ p} := by
      rw [← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_mul_span_singleton (r := aQ₃),
        ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow,
        ← Ideal.span_singleton_pow, haQ₁, haQ₃, ht, hvQR₃, hvR₃]
      ring
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspaneq
    obtain ⟨c, hc0, hcu⟩ := hCunits (↑u⁻¹) (Units.isUnit _)
    refine ⟨c, hc0, ?_⟩
    rw [← hcu]
    calc aQ₁ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xQR₃) ^ p *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xR₃) ^ p
        = aQ₁ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xQR₃) ^ p *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xR₃) ^ p * (↑u * ↑u⁻¹) := by
          rw [Units.mul_inv, mul_one]
      _ = (aQ₁ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xQR₃) ^ p *
        (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
          xR₃) ^ p * ↑u) * ↑u⁻¹ := by
          ring
      _ = (aQ₃ * t ^ p) * ↑u⁻¹ := by
          rw [hu]
      _ = ↑u⁻¹ * (aQ₃ * t ^ p) := by
          ring
  obtain ⟨c, hc0, hceq⟩ := hcomp
  -- the FULL-DIVISOR reciprocity instance (unconditional): the pair
  -- (aP₁, XS₁^p) against the pair (t, XR₁·XQR₃), with every σ-point
  -- included so that support collisions zero both sides symmetrically
  have hstarinst :
      (AdjoinRoot.evalEval hQR₁.left aP₁ *
        AdjoinRoot.evalEval hR₁neg.left aP₁ *
        AdjoinRoot.evalEval hR₃.left aP₁ *
        AdjoinRoot.evalEval hQR₃neg.left aP₁) *
      (AdjoinRoot.evalEval hR₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₁neg.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hQR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hQR₃neg.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
      ((AdjoinRoot.evalEval hS₁.left t *
        AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
      ((AdjoinRoot.evalEval hPS₁.left
          (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
            WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
        AdjoinRoot.evalEval hS₁neg.left
          (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
            WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) =
      (AdjoinRoot.evalEval hR₁.left aP₁ *
        AdjoinRoot.evalEval hR₁neg.left aP₁ *
        AdjoinRoot.evalEval hQR₃.left aP₁ *
        AdjoinRoot.evalEval hQR₃neg.left aP₁) *
      (AdjoinRoot.evalEval hQR₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₁neg.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hQR₃neg.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
      ((AdjoinRoot.evalEval hPS₁.left t *
        AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
      ((AdjoinRoot.evalEval hS₁.left
          (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
            WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
        AdjoinRoot.evalEval hS₁neg.left
          (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
            WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) := by
    -- the divisor data of the two non-word functions, as words
    have hDPw : Ideal.span {aP₁} =
        ((Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
          Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
          (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
              P.1 (Polynomial.C P.2))).prod := by
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.map_replicate, Multiset.prod_replicate,
        Multiset.prod_replicate, haP₁]
    have hDPweq : ∀ T ∈ (Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
        Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
        Wb.toAffine.Equation T.1 T.2 := by
      intro T hT
      rcases Multiset.mem_add.mp hT with h | h
      · rw [Multiset.eq_of_mem_replicate h]
        exact hPS₁.left
      · rw [Multiset.eq_of_mem_replicate h]
        exact (WeierstrassCurve.Affine.equation_neg
          (W' := Wb.toAffine) _ _).mpr hS₁.left
    have hDtw : Ideal.span {t} =
        ((((xQR₁, yQR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          ((xR₁, Wb.toAffine.negY xR₁ yR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          ((xR₃, yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          {((xQR₃, Wb.toAffine.negY xQR₃ yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))}).map
          (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
              P.1 (Polynomial.C P.2))).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
        Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_singleton, Multiset.prod_singleton, ht]
      ring
    have hDtweq : ∀ T ∈ (((xQR₁, yQR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        ((xR₁, Wb.toAffine.negY xR₁ yR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        ((xR₃, yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        {((xQR₃, Wb.toAffine.negY xQR₃ yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))}),
        Wb.toAffine.Equation T.1 T.2 := by
      intro T hT
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hQR₁.left
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hR₁neg.left
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hR₃.left
      · rw [Multiset.mem_singleton.mp hT]; exact hQR₃neg.left
    -- the Miller words of aP₁ over F' (F-rational, roots in F')
    obtain ⟨Ln, Ld, Vn, Vd, uf, huf0, hLnF, hVnF, hRtF, hwordP⟩ :=
      hgenfac (2 * p) aP₁ _ F'
        (by rw [Multiset.card_add, Multiset.card_replicate,
              Multiset.card_replicate]
            omega)
        hDPweq
        (by intro T hT
            rcases Multiset.mem_add.mp hT with h | h
            · rw [Multiset.eq_of_mem_replicate h]
              exact ⟨hxPS₁F', hyPS₁F'⟩
            · rw [Multiset.eq_of_mem_replicate h]
              exact ⟨hxS₁F', hnegYF F' xS₁ yS₁ hxS₁F' hyS₁F'⟩)
        hDPw
    have hbalP := hbaldiv aP₁ _ Ln Ld Vn Vd uf huf0 hDPweq hDPw hwordP
    -- canonical fiber pair = actual σ-pair, for any curve point
    have hfibpair : ∀ (c y : (AlgebraicClosure (ZMod q))),
        Wb.toAffine.Equation c y →
        ({(c, Wb.toAffine.negY c (yfib c)), (c, yfib c)} :
          Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) =
        {(c, Wb.toAffine.negY c y), (c, y)} := by
      intro c y hE
      rcases hfib2 c y hE with h | h
      · rw [h]
      · rw [h, WeierstrassCurve.Affine.negY_negY]
        exact Multiset.cons_swap _ _ _
    -- the pointwise evaluation identities of the two word identities
    -- at the six aP₁-relevant and three t-relevant points
    have heP₁ := hevid aP₁ Ln Ld Vn Vd uf hwordP xQR₁ yQR₁ hQR₁.left
    have heP₂ := hevid aP₁ Ln Ld Vn Vd uf hwordP xR₁
      (Wb.toAffine.negY xR₁ yR₁) hR₁neg.left
    have heP₃ := hevid aP₁ Ln Ld Vn Vd uf hwordP xR₃ yR₃ hR₃.left
    have heP₄ := hevid aP₁ Ln Ld Vn Vd uf hwordP xQR₃
      (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg.left
    have heP₅ := hevid aP₁ Ln Ld Vn Vd uf hwordP xR₁ yR₁ hR₁.left
    have heP₆ := hevid aP₁ Ln Ld Vn Vd uf hwordP xQR₃ yQR₃ hQR₃.left
    -- the word-vs-word reciprocity instances between the two words
    -- and against the two vertical words
    have hwv₇ := hww Ln 0 Vn ({xR₁, xQR₃} :
      Multiset (AlgebraicClosure (ZMod q)))
    have hwv₈ := hww Ld 0 Vd ({xR₁, xQR₃} :
      Multiset (AlgebraicClosure (ZMod q)))
    -- the divisor-bookkeeping conversions, as product equations
    -- (type inferred from hbalP; normalized at use time)
    have hcvP := fun φ : ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) → (AlgebraicClosure (ZMod q)) =>
      congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
        (A.map φ).prod) hbalP
    -- THE EXPLICIT FACTORIZATION OF t: the four points of div t pair
    -- into the chord through (Q⊕R₁), R₃ (third point ⊖M) and the
    -- chord through ⊖R₁, ⊖(Q⊕R₃) (third point M), where
    -- M = Q⊕R₁⊕R₃ has abscissa OUTSIDE F'; so t·(X - xM) is a
    -- constant times the product of the two line classes
    have hMpt0 : (WeierstrassCurve.Affine.Point.some xM yM hM :
        Wb.toAffine.Point) ≠ 0 := by
      simp [WeierstrassCurve.Affine.Point.zero_def]
    have hMnegpt : Wb.toAffine.Nonsingular xM (Wb.toAffine.negY xM yM) :=
      (WeierstrassCurve.Affine.nonsingular_neg xM yM).mpr hM
    have hcaseA : ¬(xQR₁ = xR₃ ∧ yQR₁ = Wb.toAffine.negY xR₃ yR₃) := by
      rintro ⟨hx, hy⟩
      apply hMpt0
      rw [hMc]
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy
    -- the σ-companion negation links
    have hnegR₁pt : (WeierstrassCurve.Affine.Point.some xR₁
        (Wb.toAffine.negY xR₁ yR₁) hR₁neg : Wb.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁) :=
      (WeierstrassCurve.Affine.Point.neg_some hR₁).symm
    have hnegQR₃pt : (WeierstrassCurve.Affine.Point.some xQR₃
        (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg : Wb.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃) :=
      (WeierstrassCurve.Affine.Point.neg_some hQR₃).symm
    have hcaseB : ¬(xR₁ = xQR₃ ∧ Wb.toAffine.negY xR₁ yR₁ =
        Wb.toAffine.negY xQR₃ (Wb.toAffine.negY xQR₃ yQR₃)) := by
      rw [WeierstrassCurve.Affine.negY_negY]
      rintro ⟨hx, hy⟩
      apply hMpt0
      have hpteq : (WeierstrassCurve.Affine.Point.some xR₁
          (Wb.toAffine.negY xR₁ yR₁) hR₁neg : Wb.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃ := by
        cases hx; cases hy; rfl
      have hneg : -(WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁ :
          Wb.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃ :=
        hnegR₁pt.symm.trans hpteq
      have h2 : (WeierstrassCurve.Affine.Point.some xQ yQ hQ +
          WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃ :
          Wb.toAffine.Point) =
          -(WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁) := by
        rw [hneg]
        exact hQRc₃.symm
      rw [hMc, hQRc₁]
      calc (WeierstrassCurve.Affine.Point.some xQ yQ hQ +
          WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁ +
          WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃ :
          Wb.toAffine.Point)
          = (WeierstrassCurve.Affine.Point.some xQ yQ hQ +
            WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃) +
            WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁ := by abel
        _ = -(WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁) +
            WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁ := by rw [h2]
        _ = 0 := neg_add_cancel _
    -- the chord sums, at the point level
    have hsumA : (WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ +
        WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃ :
        Wb.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some xM yM hM := hMc.symm
    have hsumB : (WeierstrassCurve.Affine.Point.some xR₁
        (Wb.toAffine.negY xR₁ yR₁) hR₁neg +
        WeierstrassCurve.Affine.Point.some xQR₃
          (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg : Wb.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some xM
          (Wb.toAffine.negY xM yM) hMnegpt := by
      rw [hnegR₁pt, hnegQR₃pt, ← neg_add_rev]
      have hQR3R1 : (WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃ +
          WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁ :
          Wb.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some xM yM hM := by
        rw [hQRc₃, hMc, hQRc₁]
        abel
      rw [hQR3R1]
      exact WeierstrassCurve.Affine.Point.neg_some hM
    -- the addition-formula links: the chords' third points are ⊖M, M
    have hlinkA := WeierstrassCurve.Affine.Point.add_some
      hcaseA (h₁ := hQR₁) (h₂ := hR₃)
    have hlinkB := WeierstrassCurve.Affine.Point.add_some
      hcaseB (h₁ := hR₁neg) (h₂ := hQR₃neg)
    obtain ⟨hXA, hYA⟩ : Wb.toAffine.addX xQR₁ xR₃
          (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) = xM ∧
        Wb.toAffine.addY xQR₁ xR₃ yQR₁
          (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) = yM := by
      have h := hlinkA.symm.trans hsumA
      injection h with e1 e2
      exact ⟨e1, e2⟩
    obtain ⟨hXB, hYB⟩ : Wb.toAffine.addX xR₁ xQR₃
          (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.negY xQR₃ yQR₃)) = xM ∧
        Wb.toAffine.addY xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
          (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.negY xQR₃ yQR₃)) =
          Wb.toAffine.negY xM yM := by
      have h := hlinkB.symm.trans hsumB
      injection h with e1 e2
      exact ⟨e1, e2⟩
    -- the two chord line identities, with third factor rewritten to ∓M
    have hlineA := hline xQR₁ yQR₁ xR₃ yR₃ hQR₁ hR₃ hcaseA
    have hlineB := hline xR₁ (Wb.toAffine.negY xR₁ yR₁) xQR₃
      (Wb.toAffine.negY xQR₃ yQR₃) hR₁neg hQR₃neg hcaseB
    rw [hXA, hYA] at hlineA
    rw [hXB, hYB, WeierstrassCurve.Affine.negY_negY] at hlineB
    -- the vertical at xM
    have hvM : Ideal.span {(WeierstrassCurve.Affine.CoordinateRing.XClass
        Wb.toAffine xM : Wb.toAffine.CoordinateRing)} =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xM (Polynomial.C (Wb.toAffine.negY xM yM)) *
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
          xM (Polynomial.C yM) :=
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul
        (W := Wb.toAffine) hM).symm
    -- the span-level factorization of t·(X - xM)
    have hspanfac : Ideal.span
        {t * WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xM} =
        Ideal.span {WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
            (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) *
          WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xR₁
            (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.negY xQR₃ yQR₃)))} := by
      rw [← Ideal.span_singleton_mul_span_singleton,
        ← Ideal.span_singleton_mul_span_singleton, ht, hvM]
      have hYA' : (Ideal.span {WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
            (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃))} :
          Ideal Wb.toAffine.CoordinateRing) =
          WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
            (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
              (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) := rfl
      have hYB' : (Ideal.span {WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xR₁
            (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.negY xQR₃ yQR₃)))} :
          Ideal Wb.toAffine.CoordinateRing) =
          WeierstrassCurve.Affine.CoordinateRing.YIdeal Wb.toAffine
            (WeierstrassCurve.Affine.linePolynomial xR₁
              (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
          (Wb.toAffine.negY xQR₃ yQR₃))) := rfl
      rw [hYA', hYB', hlineA, hlineB]
      ring
    -- the element-level factorization, up to a nonzero constant
    have hlfac : ∃ c : (AlgebraicClosure (ZMod q)), c ≠ 0 ∧
        t * WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xM =
        AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C c) *
          (WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
            (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) *
          WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xR₁
            (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.negY xQR₃ yQR₃)))) := by
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspanfac
      obtain ⟨c, hc0, hcu⟩ := hCunits (↑u⁻¹) (Units.isUnit _)
      refine ⟨c, hc0, ?_⟩
      rw [← hcu]
      calc t * WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xM
          = t * WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
            xM * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
        _ = (t * WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine
            xM * ↑u) * ↑u⁻¹ := by ring
        _ = (WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
            (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) *
          WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xR₁
            (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.negY xQR₃ yQR₃)))) * ↑u⁻¹ := by rw [hu]
        _ = ↑u⁻¹ * (WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
            (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) *
          WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
          (WeierstrassCurve.Affine.linePolynomial xR₁
            (Wb.toAffine.negY xR₁ yR₁)
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
              (Wb.toAffine.negY xQR₃ yQR₃)))) := by ring
    -- THE GRAND WORD-LEVEL ASSEMBLY: evaluate the two word identities
    -- over all eight points, convert word-divisor evaluations through
    -- the hbaldiv bookkeeping, swap with hww, and cancel the balanced
    -- u-powers and paired hww signs
    have hgrand :
        (AdjoinRoot.evalEval hQR₁.left aP₁ *
          AdjoinRoot.evalEval hR₁neg.left aP₁ *
          AdjoinRoot.evalEval hR₃.left aP₁ *
          AdjoinRoot.evalEval hQR₃neg.left aP₁) *
        (AdjoinRoot.evalEval hR₁.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hR₁neg.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hQR₃.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hQR₃neg.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
        ((AdjoinRoot.evalEval hS₁.left t *
          AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
        ((AdjoinRoot.evalEval hPS₁.left
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
              WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
          AdjoinRoot.evalEval hS₁neg.left
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
              WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) =
        (AdjoinRoot.evalEval hR₁.left aP₁ *
          AdjoinRoot.evalEval hR₁neg.left aP₁ *
          AdjoinRoot.evalEval hQR₃.left aP₁ *
          AdjoinRoot.evalEval hQR₃neg.left aP₁) *
        (AdjoinRoot.evalEval hQR₁.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hR₁neg.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hR₃.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
          AdjoinRoot.evalEval hQR₃neg.left
            ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
        ((AdjoinRoot.evalEval hPS₁.left t *
          AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
        ((AdjoinRoot.evalEval hS₁.left
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
              WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
          AdjoinRoot.evalEval hS₁neg.left
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
              WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) := by
      -- t's explicit word in the hbaldiv/hevid format: numerator
      -- lines = the two chords, denominator vertical = xM
      obtain ⟨c, hc0, htfac⟩ := hlfac
      have htword : t *
          ((0 : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
            (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              AdjoinRoot.mk Wb.toAffine.polynomial
                (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
                  Polynomial.C P.2)))).prod *
          (({xM} : Multiset (AlgebraicClosure (ZMod q))).map
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod =
          AdjoinRoot.of Wb.toAffine.polynomial (Polynomial.C c) *
          (({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
              yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
             (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃),
              Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
            (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
              AdjoinRoot.mk Wb.toAffine.polynomial
                (Polynomial.X - Polynomial.C (Polynomial.C P.1 * Polynomial.X +
                  Polynomial.C P.2)))).prod *
          ((0 : Multiset (AlgebraicClosure (ZMod q))).map
            (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine)).prod := by
        simp only [Multiset.map_zero, Multiset.prod_zero, mul_one,
          Multiset.map_singleton, Multiset.prod_singleton,
          Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons]
        have hclA : AdjoinRoot.mk Wb.toAffine.polynomial
            (Polynomial.X - Polynomial.C (Polynomial.C
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) *
              Polynomial.X + Polynomial.C (yQR₁ -
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) =
            WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
              (WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃)) := by
          have harg : (Polynomial.C
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) *
              Polynomial.X + Polynomial.C (yQR₁ -
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁) :
              Polynomial (AlgebraicClosure (ZMod q))) =
              WeierstrassCurve.Affine.linePolynomial xQR₁ yQR₁
                (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) := by
            simp only [WeierstrassCurve.Affine.linePolynomial,
              Polynomial.C_sub, Polynomial.C_mul]
            ring
          exact congrArg (AdjoinRoot.mk Wb.toAffine.polynomial)
            (by rw [harg])
        have hclB : AdjoinRoot.mk Wb.toAffine.polynomial
            (Polynomial.X - Polynomial.C (Polynomial.C
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) *
              Polynomial.X + Polynomial.C (Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))) =
            WeierstrassCurve.Affine.CoordinateRing.YClass Wb.toAffine
              (WeierstrassCurve.Affine.linePolynomial xR₁
                (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃))) := by
          have harg : (Polynomial.C
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) *
              Polynomial.X + Polynomial.C (Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁) :
              Polynomial (AlgebraicClosure (ZMod q))) =
              WeierstrassCurve.Affine.linePolynomial xR₁
                (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) := by
            simp only [WeierstrassCurve.Affine.linePolynomial,
              Polynomial.C_sub, Polynomial.C_mul]
            ring
          exact congrArg (AdjoinRoot.mk Wb.toAffine.polynomial)
            (by rw [harg])
        rw [hclA, hclB]
        exact htfac
      -- t's divisor balance: D_t + fiber pair over xM = the two
      -- chord-cubic root divisors
      have hbalt := hbaldiv t
        ({(xQR₁, yQR₁), (xR₁, Wb.toAffine.negY xR₁ yR₁), (xR₃, yR₃),
             (xQR₃, Wb.toAffine.negY xQR₃ yQR₃)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
              yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
             (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃),
              Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        0 0 ({xM} : Multiset (AlgebraicClosure (ZMod q))) c hc0
        (by intro T hT
            simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
              Multiset.mem_singleton] at hT
            rcases hT with h | h | h | h
            · rw [h]; exact hQR₁.left
            · rw [h]; exact hR₁neg.left
            · rw [h]; exact hR₃.left
            · rw [h]; exact hQR₃neg.left)
        (by simp only [Multiset.insert_eq_cons, Multiset.map_cons,
              Multiset.map_singleton, Multiset.prod_cons,
              Multiset.prod_singleton]
            rw [ht]; ring)
        htword
      -- pointwise evaluations of t's word identity at S₁, ⊖S₁, PS₁
      have het₁ := hevid t
        ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
              yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
             (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃),
              Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        0 0 ({xM} : Multiset (AlgebraicClosure (ZMod q))) c htword xS₁ yS₁ hS₁.left
      have het₂ := hevid t
        ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
              yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
             (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃),
              Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        0 0 ({xM} : Multiset (AlgebraicClosure (ZMod q))) c htword xS₁
        (Wb.toAffine.negY xS₁ yS₁) hS₁neg.left
      have het₃ := hevid t
        ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
              yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
             (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃),
              Wb.toAffine.negY xR₁ yR₁ -
                (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁)
                (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
            Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
        0 0 ({xM} : Multiset (AlgebraicClosure (ZMod q))) c htword xPS₁ yPS₁ hPS₁.left
      -- the product-projection of the t-side balance
      have hcvt := fun φ : ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) → (AlgebraicClosure (ZMod q)) =>
        congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
          (A.map φ).prod) hbalt
      -- the residual stitch: pure balanced-product arithmetic over the
      -- two explicit words (hww swaps + the projections above)
      have hstitch :
          (AdjoinRoot.evalEval hQR₁.left aP₁ *
            AdjoinRoot.evalEval hR₁neg.left aP₁ *
            AdjoinRoot.evalEval hR₃.left aP₁ *
            AdjoinRoot.evalEval hQR₃neg.left aP₁) *
          (AdjoinRoot.evalEval hR₁.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hR₁neg.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hQR₃.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hQR₃neg.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
          ((AdjoinRoot.evalEval hS₁.left t *
            AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
          ((AdjoinRoot.evalEval hPS₁.left
              (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
                WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
            AdjoinRoot.evalEval hS₁neg.left
              (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
                WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) =
          (AdjoinRoot.evalEval hR₁.left aP₁ *
            AdjoinRoot.evalEval hR₁neg.left aP₁ *
            AdjoinRoot.evalEval hQR₃.left aP₁ *
            AdjoinRoot.evalEval hQR₃neg.left aP₁) *
          (AdjoinRoot.evalEval hQR₁.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hR₁neg.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hR₃.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
            AdjoinRoot.evalEval hQR₃neg.left
              ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p)) *
          ((AdjoinRoot.evalEval hPS₁.left t *
            AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
          ((AdjoinRoot.evalEval hS₁.left
              (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
                WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃) *
            AdjoinRoot.evalEval hS₁neg.left
              (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁ *
                WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xQR₃)) ^ p) := by
        -- reduce to the fully scalar form: all vertical evaluations
        -- are explicit abscissa differences
        have hscalar :
            (AdjoinRoot.evalEval hQR₁.left aP₁ *
              AdjoinRoot.evalEval hR₁neg.left aP₁ *
              AdjoinRoot.evalEval hR₃.left aP₁ *
              AdjoinRoot.evalEval hQR₃neg.left aP₁) *
            ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p *
              (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
            ((AdjoinRoot.evalEval hS₁.left t *
              AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
            (((xPS₁ - xR₁) * (xPS₁ - xQR₃) *
              ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) =
            (AdjoinRoot.evalEval hR₁.left aP₁ *
              AdjoinRoot.evalEval hR₁neg.left aP₁ *
              AdjoinRoot.evalEval hQR₃.left aP₁ *
              AdjoinRoot.evalEval hQR₃neg.left aP₁) *
            ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p *
              (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
            ((AdjoinRoot.evalEval hPS₁.left t *
              AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
            (((xS₁ - xR₁) * (xS₁ - xQR₃) *
              ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) := by
          -- the junk factors are nonzero: xM avoids F', S₁/PS₁ data in F'
          have hZ1 : (xS₁ - xM) ≠ 0 :=
            sub_ne_zero.mpr fun h => hxMF' (h ▸ hxS₁F')
          have hZ2 : (xPS₁ - xM) ≠ 0 :=
            sub_ne_zero.mpr fun h => hxMF' (h ▸ hxPS₁F')
          have hZne : ((xS₁ - xM) * (xS₁ - xM) *
              ((xPS₁ - xM) * (xS₁ - xM))) ^ p ≠ 0 :=
            pow_ne_zero p (mul_ne_zero (mul_ne_zero hZ1 hZ1)
              (mul_ne_zero hZ2 hZ1))
          -- the multiplied-through form, ready for the t-elimination
          have hword0 :
              (AdjoinRoot.evalEval hQR₁.left aP₁ *
                AdjoinRoot.evalEval hR₁neg.left aP₁ *
                AdjoinRoot.evalEval hR₃.left aP₁ *
                AdjoinRoot.evalEval hQR₃neg.left aP₁) *
              ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p *
                (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
              ((AdjoinRoot.evalEval hS₁.left t *
                AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
              (((xPS₁ - xR₁) * (xPS₁ - xQR₃) *
                ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
            (((xS₁ - xM) * (xS₁ - xM) * ((xPS₁ - xM) * (xS₁ - xM))) ^ p) =
              (AdjoinRoot.evalEval hR₁.left aP₁ *
                AdjoinRoot.evalEval hR₁neg.left aP₁ *
                AdjoinRoot.evalEval hQR₃.left aP₁ *
                AdjoinRoot.evalEval hQR₃neg.left aP₁) *
              ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p *
                (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
              ((AdjoinRoot.evalEval hPS₁.left t *
                AdjoinRoot.evalEval hS₁neg.left t) ^ p) *
              (((xS₁ - xR₁) * (xS₁ - xQR₃) *
                ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
            (((xS₁ - xM) * (xS₁ - xM) * ((xPS₁ - xM) * (xS₁ - xM))) ^ p) := by
            -- normalize the pointwise t-word identities to scalars
            simp only [Multiset.map_zero, Multiset.prod_zero, one_mul,
              mul_one, Multiset.insert_eq_cons, Multiset.map_cons,
              Multiset.map_singleton, Multiset.prod_cons,
              Multiset.prod_singleton] at het₁ het₂ het₃
            -- the paired (σ-completed) t-eliminations
            have heL : (AdjoinRoot.evalEval hS₁.left t * (xS₁ - xM)) * (AdjoinRoot.evalEval hS₁neg.left t * (xS₁ - xM)) =
                (c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) := by
              linear_combination (AdjoinRoot.evalEval hS₁neg.left t * (xS₁ - xM)) * het₁ +
                (c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * het₂
            have heR : (AdjoinRoot.evalEval hPS₁.left t * (xPS₁ - xM)) * (AdjoinRoot.evalEval hS₁neg.left t * (xS₁ - xM)) =
                (c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) := by
              linear_combination (AdjoinRoot.evalEval hS₁neg.left t * (xS₁ - xM)) * het₃ +
                (c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * het₂
            have heLp := congrArg (· ^ p) heL
            have heRp := congrArg (· ^ p) heR
            -- the t-free reciprocity over the explicit chord-line values
            have hword1 :
                (AdjoinRoot.evalEval hQR₁.left aP₁ * AdjoinRoot.evalEval hR₁neg.left aP₁ * AdjoinRoot.evalEval hR₃.left aP₁ * AdjoinRoot.evalEval hQR₃neg.left aP₁) *
                ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
                ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p *
                (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                ((xPS₁ - xM) * (xS₁ - xM)) ^ p =
                (AdjoinRoot.evalEval hR₁.left aP₁ * AdjoinRoot.evalEval hR₁neg.left aP₁ * AdjoinRoot.evalEval hQR₃.left aP₁ * AdjoinRoot.evalEval hQR₃neg.left aP₁) *
                ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
                ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p *
                (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                ((xS₁ - xM) * (xS₁ - xM)) ^ p := by
              -- aP₁-elimination: cancel the word-denominator values
              -- at the six points (all nonzero by the avoidances)
              have hDne : ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) ≠ 0 := by
                have hrootmem : ∀ (l n x y : (AlgebraicClosure (ZMod q))),
                    Wb.toAffine.Equation x y → y - (l * x + n) = 0 →
                    x ∈ ((Polynomial.X ^ 3
                      + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
                        * Polynomial.X ^ 2
                      + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
                          - Wb.toAffine.a₃ * l) * Polynomial.X
                      + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots := by
                  intro l n x y hE hy
                  have hcne : ((Polynomial.X ^ 3
                      + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
                        * Polynomial.X ^ 2
                      + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
                          - Wb.toAffine.a₃ * l) * Polynomial.X
                      + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))) ≠ 0 := fun h => by
                    have h3 := congrArg (fun q : Polynomial (AlgebraicClosure (ZMod q)) =>
                      Polynomial.coeff q 3) h
                    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
                      Polynomial.coeff_C_mul, Polynomial.coeff_C,
                      Polynomial.coeff_X, Polynomial.coeff_zero, reduceIte,
                      mul_zero, add_zero, zero_add] at h3
                    norm_num at h3
                  rw [Polynomial.mem_roots hcne]
                  have hE' := (WeierstrassCurve.Affine.equation_iff
                    (W := Wb.toAffine) x y).mp hE
                  have hyv : y = l * x + n := sub_eq_zero.mp hy
                  subst hyv
                  simp only [Polynomial.IsRoot, Polynomial.eval_add,
                    Polynomial.eval_mul, Polynomial.eval_pow,
                    Polynomial.eval_C, Polynomial.eval_X]
                  linear_combination -hE'
                refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
                  (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₁F' (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xQR₁ (hrootmem ln.1 ln.2 xQR₁ (yQR₁) hQR₁.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₁F' (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₁ (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xR₁ (hrootmem ln.1 ln.2 xR₁ (Wb.toAffine.negY xR₁ yR₁) hR₁neg.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₁ (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₃ (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xR₃ (hrootmem ln.1 ln.2 xR₃ (yR₃) hR₃.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₃ (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₃ (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xQR₃ (hrootmem ln.1 ln.2 xQR₃ (Wb.toAffine.negY xQR₃ yQR₃) hQR₃neg.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₃ (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₁ (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xR₁ (hrootmem ln.1 ln.2 xR₁ (yR₁) hR₁.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxR₁ (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
                · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                    (Multiset.prod_ne_zero fun h0 => ?_)
                  · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₃ (hRtF ln (Multiset.mem_add.mpr (Or.inr hln))
                      xQR₃ (hrootmem ln.1 ln.2 xQR₃ (yQR₃) hQR₃.left hval))
                  · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                    exact hxQR₃ (sub_eq_zero.mp hval ▸
                      hVnF cc (Multiset.mem_add.mpr (Or.inr hcc)))
              refine mul_right_cancel₀ hDne ?_
              have hword2 :
                  (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vn.map (fun c => xQR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vn.map (fun c => xR₃ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vn.map (fun c => xQR₃ - c)).prod)) * ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) =
                  (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vn.map (fun c => xQR₃ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vn.map (fun c => xQR₃ - c)).prod)) * ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) := by
                -- the projection cycle: hww swaps (all signs even),
                -- balance projections, fiber-junk cancellation
                have hwwN := hww Ln ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
                    yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
                   (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃),
                    Wb.toAffine.negY xR₁ yR₁ -
                      (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
                  Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) Vn (0 : Multiset (AlgebraicClosure (ZMod q)))
                have hwwNM := hww Ln (0 : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) Vn
                  ({xM} : Multiset (AlgebraicClosure (ZMod q)))
                have hwwD := hww Ld ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
                    yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
                   (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃),
                    Wb.toAffine.negY xR₁ yR₁ -
                      (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
                  Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) Vd (0 : Multiset (AlgebraicClosure (ZMod q)))
                have hwwDM := hww Ld (0 : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) Vd
                  ({xM} : Multiset (AlgebraicClosure (ZMod q)))
                have hcvtN := hcvt (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  (Ln.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    T.2 - (ab.1 * T.1 + ab.2))).prod *
                  (Vn.map (fun cv => T.1 - cv)).prod)
                have hcvtD := hcvt (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  (Ld.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    T.2 - (ab.1 * T.1 + ab.2))).prod *
                  (Vd.map (fun cv => T.1 - cv)).prod)
                have hpjA := hcvP (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  T.2 - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * T.1 + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁)))
                have hpjB := hcvP (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                  T.2 - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * T.1 + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))
                have hpjM := hcvP (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - xM)
                have hwvS := hww
                  ({(Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃,
                    yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁),
                   (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃),
                    Wb.toAffine.negY xR₁ yR₁ -
                      (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)} :
                  Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))))
                  (0 : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))) (0 : Multiset (AlgebraicClosure (ZMod q)))
                  ({xS₁} : Multiset (AlgebraicClosure (ZMod q)))
                have hcvtS := hcvt (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - xS₁)
                have hpjR := hcvP (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - xR₁)
                have hpjQ := hcvP (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => T.1 - xQR₃)
                -- normalize: expand literal multisets, replicates, and
                -- product-of-product maps; kill the even hww signs
                simp only [Multiset.map_add, Multiset.prod_add,
                  Multiset.map_replicate, Multiset.prod_replicate,
                  Multiset.insert_eq_cons, Multiset.map_cons,
                  Multiset.map_singleton, Multiset.prod_cons,
                  Multiset.prod_singleton, Multiset.map_zero,
                  Multiset.prod_zero, Multiset.bind_cons,
                  Multiset.bind_singleton, Multiset.bind_zero,
                  Multiset.zero_bind, Multiset.singleton_bind,
                  Multiset.cons_bind, Multiset.card_cons,
                  Multiset.card_singleton, Multiset.card_zero,
                  Multiset.prod_map_mul, Multiset.map_map,
                  Function.comp_apply, Nat.mul_zero, pow_zero,
                  mul_one, one_mul]
                  at hwwN hwwNM hwwD hwwDM hcvtN hcvtD hpjA hpjB hpjM
                    hpjR hpjQ hwv₇ hwv₈ hwvS
                    hcvtS
                rw [Even.neg_one_pow ⟨Multiset.card Ln, by ring⟩,
                  one_mul] at hwwN
                rw [Even.neg_one_pow ⟨Multiset.card Ld, by ring⟩,
                  one_mul] at hwwD
                have hnormhelpS :
                    (((yfib xS₁) - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) *
                      ((yfib xS₁) - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))) *
                    ((Wb.toAffine.negY xS₁ (yfib xS₁) - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) *
                      (Wb.toAffine.negY xS₁ (yfib xS₁) - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))) =
                    (xQR₁ - xS₁) * (xR₁ - xS₁) * (xR₃ - xS₁) *
                      (xQR₃ - xS₁) * ((xM - xS₁) * (xM - xS₁)) := by
                  linear_combination hwvS - hcvtS
                have hnormS' :
                    ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) *
                      (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))) *
                    ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) *
                      (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))) =
                    (xQR₁ - xS₁) * (xR₁ - xS₁) * (xR₃ - xS₁) *
                      (xQR₃ - xS₁) * ((xM - xS₁) * (xM - xS₁)) := by
                  have htr := congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
                    (A.map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    (T.2 - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * T.1 + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) *
                    (T.2 - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * T.1 + (Wb.toAffine.negY xR₁ yR₁ -
                      (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))).prod)
                    (hfibpair xS₁ yS₁ hS₁.left)
                  set_option maxRecDepth 16384 in
                  simp only [Multiset.insert_eq_cons, Multiset.map_cons,
                    Multiset.map_singleton, Multiset.prod_cons,
                    Multiset.prod_singleton] at htr
                  linear_combination hnormhelpS - htr
                have htrRN := congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
                  (A.map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    (Ln.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                      T.2 - (ab.1 * T.1 + ab.2))).prod *
                    (Vn.map (fun cv => T.1 - cv)).prod)).prod)
                  (hfibpair xR₁ yR₁ hR₁.left)
                have htrQN := congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
                  (A.map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    (Ln.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                      T.2 - (ab.1 * T.1 + ab.2))).prod *
                    (Vn.map (fun cv => T.1 - cv)).prod)).prod)
                  (hfibpair xQR₃ yQR₃ hQR₃.left)
                have htrRD := congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
                  (A.map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    (Ld.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                      T.2 - (ab.1 * T.1 + ab.2))).prod *
                    (Vd.map (fun cv => T.1 - cv)).prod)).prod)
                  (hfibpair xR₁ yR₁ hR₁.left)
                have htrQD := congrArg (fun A : Multiset ((AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) =>
                  (A.map (fun T : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                    (Ld.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
                      T.2 - (ab.1 * T.1 + ab.2))).prod *
                    (Vd.map (fun cv => T.1 - cv)).prod)).prod)
                  (hfibpair xQR₃ yQR₃ hQR₃.left)
                set_option maxRecDepth 16384 in
                simp only [Multiset.insert_eq_cons, Multiset.map_cons,
                  Multiset.map_singleton, Multiset.prod_cons,
                  Multiset.prod_singleton] at htrRN htrQN htrRD htrQD
                have hN := hcvtN.trans hwwN
                have hD := hcvtD.trans hwwD
                -- the numerator-word M-fiber values are nonzero
                have hmfneN : ((Ln.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xM (yfib xM) - (ab.1 * xM + ab.2))).prod * (Vn.map (fun cv => xM - cv)).prod) *
                    ((Ln.map (fun ab : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yfib xM - (ab.1 * xM + ab.2))).prod * (Vn.map (fun cv => xM - cv)).prod) ≠ 0 := by
                  have hrootmem' : ∀ (l n x y : (AlgebraicClosure (ZMod q))),
                      Wb.toAffine.Equation x y → y - (l * x + n) = 0 →
                      x ∈ ((Polynomial.X ^ 3
                        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
                          * Polynomial.X ^ 2
                        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
                            - Wb.toAffine.a₃ * l) * Polynomial.X
                        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))).roots := by
                    intro l n x y hE hy
                    have hcne : ((Polynomial.X ^ 3
                        + Polynomial.C (Wb.toAffine.a₂ - l ^ 2 - Wb.toAffine.a₁ * l)
                          * Polynomial.X ^ 2
                        + Polynomial.C (Wb.toAffine.a₄ - 2 * l * n - Wb.toAffine.a₁ * n
                            - Wb.toAffine.a₃ * l) * Polynomial.X
                        + Polynomial.C (Wb.toAffine.a₆ - n ^ 2 - Wb.toAffine.a₃ * n))) ≠ 0 := fun h => by
                      have h3 := congrArg (fun q : Polynomial (AlgebraicClosure (ZMod q)) =>
                        Polynomial.coeff q 3) h
                      simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
                        Polynomial.coeff_C_mul, Polynomial.coeff_C,
                        Polynomial.coeff_X, Polynomial.coeff_zero, reduceIte,
                        mul_zero, add_zero, zero_add] at h3
                      norm_num at h3
                    rw [Polynomial.mem_roots hcne]
                    have hE' := (WeierstrassCurve.Affine.equation_iff
                      (W := Wb.toAffine) x y).mp hE
                    have hyv : y = l * x + n := sub_eq_zero.mp hy
                    subst hyv
                    simp only [Polynomial.IsRoot, Polynomial.eval_add,
                      Polynomial.eval_mul, Polynomial.eval_pow,
                      Polynomial.eval_C, Polynomial.eval_X]
                    linear_combination -hE'
                  have hEneg : Wb.toAffine.Equation xM
                      (Wb.toAffine.negY xM (yfib xM)) :=
                    (WeierstrassCurve.Affine.equation_neg
                      (W' := Wb.toAffine) _ _).mpr (hyfib xM)
                  refine mul_ne_zero ?_ ?_
                  · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                      (Multiset.prod_ne_zero fun h0 => ?_)
                    · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                      exact hxMF' (hRtF ln (Multiset.mem_add.mpr (Or.inl hln))
                        xM (hrootmem' ln.1 ln.2 xM (Wb.toAffine.negY xM (yfib xM)) hEneg hval))
                    · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                      exact hxMF' (sub_eq_zero.mp hval ▸
                        hVnF cc (Multiset.mem_add.mpr (Or.inl hcc)))
                  · refine mul_ne_zero (Multiset.prod_ne_zero fun h0 => ?_)
                      (Multiset.prod_ne_zero fun h0 => ?_)
                    · obtain ⟨ln, hln, hval⟩ := Multiset.mem_map.mp h0
                      exact hxMF' (hRtF ln (Multiset.mem_add.mpr (Or.inl hln))
                        xM (hrootmem' ln.1 ln.2 xM (yfib xM) (hyfib xM) hval))
                    · obtain ⟨cc, hcc, hval⟩ := Multiset.mem_map.mp h0
                      exact hxMF' (sub_eq_zero.mp hval ▸
                        hVnF cc (Multiset.mem_add.mpr (Or.inl hcc)))
                -- the final telescope: cancel the nonzero junk and
                -- chain all substitutions; the residue is hres
                have hres :
                    (((xPS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Wb.toAffine.negY xS₁ yS₁ -
        (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^
      p) *
                    ((Wb.toAffine.negY xS₁ yS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p) *
                    ((c *
                ((yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                    ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p) =
                    (((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xM) ^ p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xM) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) := by
                  have hnSp := congrArg (· ^ p) hnormS'
                  have hsw1 := congrArg (· ^ p)
                    (show (xR₁ - xS₁) * (xR₁ - xS₁) =
                      (xS₁ - xR₁) * (xS₁ - xR₁) by ring)
                  have hsw2 := congrArg (· ^ p)
                    (show (xQR₃ - xS₁) * (xQR₃ - xS₁) =
                      (xS₁ - xQR₃) * (xS₁ - xQR₃) by ring)
                  have hsw3 := congrArg (· ^ p)
                    (show (xM - xS₁) * (xM - xS₁) =
                      (xS₁ - xM) * (xS₁ - xM) by ring)
                  simp only [mul_pow] at hnSp hsw1 hsw2 hsw3 ⊢
                  linear_combination
                    (((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁))) ^ p) *
                      ((c) ^ p) *
                      ((c) ^ p) *
                      ((xPS₁ - xM) ^ p) *
                      ((xPS₁ - xQR₃) ^ p) *
                      ((xPS₁ - xR₁) ^ p) *
                      ((xQR₃ - xS₁) ^ p) *
                      ((xR₁ - xS₁) ^ p) *
                      ((xS₁ - xM) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p)) * hnSp +
                    (((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁))) ^ p) *
                      ((c) ^ p) *
                      ((c) ^ p) *
                      ((xM - xS₁) ^ p) *
                      ((xM - xS₁) ^ p) *
                      ((xPS₁ - xM) ^ p) *
                      ((xPS₁ - xQR₃) ^ p) *
                      ((xPS₁ - xR₁) ^ p) *
                      ((xQR₁ - xS₁) ^ p) *
                      ((xQR₃ - xS₁) ^ p) *
                      ((xQR₃ - xS₁) ^ p) *
                      ((xR₃ - xS₁) ^ p) *
                      ((xS₁ - xM) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p)) * hsw1 +
                    (((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁))) ^ p) *
                      ((c) ^ p) *
                      ((c) ^ p) *
                      ((xM - xS₁) ^ p) *
                      ((xM - xS₁) ^ p) *
                      ((xPS₁ - xM) ^ p) *
                      ((xPS₁ - xQR₃) ^ p) *
                      ((xPS₁ - xR₁) ^ p) *
                      ((xQR₁ - xS₁) ^ p) *
                      ((xR₃ - xS₁) ^ p) *
                      ((xS₁ - xM) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p)) * hsw2 +
                    (((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁))) ^ p) *
                      ((c) ^ p) *
                      ((c) ^ p) *
                      ((xPS₁ - xM) ^ p) *
                      ((xPS₁ - xQR₃) ^ p) *
                      ((xPS₁ - xR₁) ^ p) *
                      ((xQR₁ - xS₁) ^ p) *
                      ((xR₃ - xS₁) ^ p) *
                      ((xS₁ - xM) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xQR₃) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((xS₁ - xR₁) ^ p) *
                      ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                      ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p)) * hsw3
                refine mul_right_cancel₀ (mul_ne_zero hDne hmfneN) ?_
                linear_combination
                  ((((xPS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((c *
                ((yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hN -
                  ((((xPS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map
        (fun i =>
          i.2 -
            (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * i.1 +
              (Wb.toAffine.negY xR₁ yR₁ -
                Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))
        (Ln.bind fun ln =>
          Multiset.map (fun x => (x, ln.1 * x + ln.2))
            (Polynomial.X ^ 3 + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1) * Polynomial.X ^ 2 +
                  Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2 - Wb.toAffine.a₃ * ln.1) *
                    Polynomial.X +
                Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2)).roots)).prod) *
                    ((Multiset.map
          (fun i =>
            Wb.toAffine.negY i (yfib i) -
              (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * i +
                (Wb.toAffine.negY xR₁ yR₁ -
                  Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))
          Vn).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map
          (fun i =>
            yfib i -
              (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * i +
                (Wb.toAffine.negY xR₁ yR₁ -
                  Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))
          Vn).prod) *
                    ((c *
                ((yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hpjA -
                  ((((xPS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map
        (fun i =>
          i.2 - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * i.1 + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁)))
        (Ld.bind fun ln =>
          Multiset.map (fun x => (x, ln.1 * x + ln.2))
            (Polynomial.X ^ 3 + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1) * Polynomial.X ^ 2 +
                  Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2 - Wb.toAffine.a₃ * ln.1) *
                    Polynomial.X +
                Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2)).roots)).prod) *
                    ((Multiset.map
          (fun i =>
            Wb.toAffine.negY i (yfib i) -
              (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * i + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁)))
          Vd).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map
          (fun i =>
            yfib i - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * i + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁)))
          Vd).prod) *
                    ((Wb.toAffine.negY xS₁ yS₁ -
        (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^
      p) *
                    ((c *
                ((yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hpjB -
                  ((((xPS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Wb.toAffine.negY xS₁ yS₁ -
        (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^
      p) *
                    ((Wb.toAffine.negY xS₁ yS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p) *
                    ((c *
                ((yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) ^ p) *
                    ((yPS₁ -
        (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
          (Wb.toAffine.negY xR₁ yR₁ -
            Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁))) ^
      p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hD +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vn).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₃ - (x.1 * xQR₃ + x.2)) Ln).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * htrRN +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ (yfib xR₁) - (x.1 * xR₁ + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vn).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vn).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => yfib xR₁ - (x.1 * xR₁ + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * htrQN -
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hwv₇ +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => x - xQR₃) Vn).prod) *
                    ((Multiset.map (fun x => x - xQR₃) Vn).prod) *
                    ((Multiset.map (fun x => x.1 - xQR₃)
      (Ln.bind fun ln =>
        Multiset.map (fun x => (x, ln.1 * x + ln.2))
          (Polynomial.X ^ 3 + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1) * Polynomial.X ^ 2 +
                Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2 - Wb.toAffine.a₃ * ln.1) *
                  Polynomial.X +
              Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2)).roots)).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hpjR +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => x - xR₁) Vd).prod) *
                    ((Multiset.map (fun x => x - xR₁) Vd).prod) *
                    ((Multiset.map (fun x => x.1 - xR₁)
        (Ld.bind fun ln =>
          Multiset.map (fun x => (x, ln.1 * x + ln.2))
            (Polynomial.X ^ 3 + Polynomial.C (Wb.toAffine.a₂ - ln.1 ^ 2 - Wb.toAffine.a₁ * ln.1) * Polynomial.X ^ 2 +
                  Polynomial.C (Wb.toAffine.a₄ - 2 * ln.1 * ln.2 - Wb.toAffine.a₁ * ln.2 - Wb.toAffine.a₃ * ln.1) *
                    Polynomial.X +
                Polynomial.C (Wb.toAffine.a₆ - ln.2 ^ 2 - Wb.toAffine.a₃ * ln.2)).roots)).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hpjQ +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hwv₈ -
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ (yfib xQR₃) - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => yfib xQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * htrRD -
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xM - x) Vn).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * htrQD -
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hwwNM +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hpjM +
                  ((((xS₁ - xM) * (xS₁ - xM)) ^ p) *
                    (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((c *
                ((yPS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (yPS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xR₁)))) *
              (c *
                ((Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ +
                      (yQR₁ - Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xQR₁))) *
                  (Wb.toAffine.negY xS₁ yS₁ -
                    (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ +
                      (Wb.toAffine.negY xR₁ yR₁ -
                        Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) *
                          xR₁)))))) ^
            p) *
                    ((xPS₁ - xM) ^ p) *
                    ((xPS₁ - xQR₃) ^ p) *
                    ((xPS₁ - xR₁) ^ p) *
                    ((xQR₁ - xS₁) ^ p) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    ((xR₃ - xS₁) ^ p) *
                    ((xS₁ - xM) ^ p) *
                    ((xS₁ - xQR₃) ^ p) *
                    ((xS₁ - xR₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hwwDM +
                  (((Multiset.map (fun x => Wb.toAffine.negY xM (yfib xM) - (x.1 * xM + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => Wb.toAffine.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => xM - x) Vd).prod) *
                    ((Multiset.map (fun x => xM - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xQR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₁ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => xR₃ - x) Vd).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod) *
                    ((Multiset.map (fun x => yfib xM - (x.1 * xM + x.2)) Ld).prod) *
                    ((xQR₃ - xS₁) ^ p) *
                    ((xR₁ - xS₁) ^ p) *
                    (uf) *
                    (uf) *
                    (uf) *
                    (uf)) * hres
              linear_combination
                (((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) * (AdjoinRoot.evalEval hR₁neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod)) * (AdjoinRoot.evalEval hR₃.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₁ +
                (((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vn.map (fun c => xQR₁ - c)).prod)) * (AdjoinRoot.evalEval hR₃.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₂ +
                (((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vn.map (fun c => xQR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₃ +
                (((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vn.map (fun c => xQR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vn.map (fun c => xR₃ - c)).prod))) * heP₄ -
                ((((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) * (AdjoinRoot.evalEval hR₁neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vd.map (fun c => xR₁ - c)).prod)) * (AdjoinRoot.evalEval hQR₃.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₅) -
                ((((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (AdjoinRoot.evalEval hQR₃.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₂) -
                ((((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (AdjoinRoot.evalEval hQR₃neg.left aP₁ * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vd.map (fun c => xQR₃ - c)).prod))) * heP₆) -
                ((((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((c * ((yPS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xPS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (yPS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xPS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁))))) * (c * ((Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃ * xS₁ + (yQR₁ - (Wb.toAffine.slope xQR₁ xR₃ yQR₁ yR₃) * xQR₁))) * (Wb.toAffine.negY xS₁ yS₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃) * xS₁ + (Wb.toAffine.negY xR₁ yR₁ - (Wb.toAffine.slope xR₁ xQR₃ (Wb.toAffine.negY xR₁ yR₁) (Wb.toAffine.negY xQR₃ yQR₃)) * xR₁)))))) ^ p * (((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p) * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₁ - (ln.1 * xQR₁ + ln.2))).prod * (Vd.map (fun c => xQR₁ - c)).prod) * ((Ld.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₃ - (ln.1 * xR₃ + ln.2))).prod * (Vd.map (fun c => xR₃ - c)).prod) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => Wb.toAffine.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2))).prod * (Vn.map (fun c => xR₁ - c)).prod)) * (uf * ((Ln.map (fun ln : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) => yQR₃ - (ln.1 * xQR₃ + ln.2))).prod * (Vn.map (fun c => xQR₃ - c)).prod))) * heP₄) + hword2
            simp only [mul_pow] at heLp heRp hword1 ⊢
            linear_combination
              ((AdjoinRoot.evalEval hQR₁.left aP₁ * AdjoinRoot.evalEval hR₁neg.left aP₁ * AdjoinRoot.evalEval hR₃.left aP₁ * AdjoinRoot.evalEval hQR₃neg.left aP₁) * ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((xPS₁ - xR₁) ^ p * (xPS₁ - xQR₃) ^ p * ((xS₁ - xR₁) ^ p * (xS₁ - xQR₃) ^ p)) *
                ((xPS₁ - xM) ^ p * (xS₁ - xM) ^ p)) * heLp -
              ((AdjoinRoot.evalEval hR₁.left aP₁ * AdjoinRoot.evalEval hR₁neg.left aP₁ * AdjoinRoot.evalEval hQR₃.left aP₁ * AdjoinRoot.evalEval hQR₃neg.left aP₁) * ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * ((xS₁ - xR₁) ^ p * (xS₁ - xQR₃) ^ p * ((xS₁ - xR₁) ^ p * (xS₁ - xQR₃) ^ p)) *
                ((xS₁ - xM) ^ p * (xS₁ - xM) ^ p)) * heRp + hword1
          exact mul_right_cancel₀ hZne hword0
        simp only [map_pow, map_mul, hevvert]
        linear_combination hscalar
      exact hstitch
    exact hgrand
  -- the final assembly: substitute hcomp at S₁ and PS₁, strip the
  -- σ-companion common factors (all nonzero by the avoidances), and
  -- close with the stripped reciprocity
  have hfin :
      (AdjoinRoot.evalEval hQR₁.left aP₁ *
        AdjoinRoot.evalEval hR₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hS₁.left aQ₁ *
        AdjoinRoot.evalEval hPS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p)) *
      (AdjoinRoot.evalEval hQR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₃.left aP₁ *
        AdjoinRoot.evalEval hS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
        AdjoinRoot.evalEval hPS₁.left aQ₃) =
      (AdjoinRoot.evalEval hQR₃.left aP₁ *
        AdjoinRoot.evalEval hR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hS₁.left aQ₃ *
        AdjoinRoot.evalEval hPS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) *
      (AdjoinRoot.evalEval hQR₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₁.left aP₁ *
        AdjoinRoot.evalEval hS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p) *
        AdjoinRoot.evalEval hPS₁.left aQ₁) := by
    -- explicit divisor facts for aP₁ and t
    have hDP : Ideal.span {aP₁} =
        ((Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
          Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
          (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
              P.1 (Polynomial.C P.2))).prod := by
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
        Multiset.map_replicate, Multiset.prod_replicate,
        Multiset.prod_replicate, haP₁]
    have hDPeq : ∀ T ∈ (Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
        Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
        Wb.toAffine.Equation T.1 T.2 := by
      intro T hT
      rcases Multiset.mem_add.mp hT with h | h
      · rw [Multiset.eq_of_mem_replicate h]
        exact hPS₁.left
      · rw [Multiset.eq_of_mem_replicate h]
        exact (WeierstrassCurve.Affine.equation_neg
          (W' := Wb.toAffine) _ _).mpr hS₁.left
    have hDt : Ideal.span {t} =
        ((((xQR₁, yQR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          ((xR₁, Wb.toAffine.negY xR₁ yR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          ((xR₃, yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
          {((xQR₃, Wb.toAffine.negY xQR₃ yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))}).map
          (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
              P.1 (Polynomial.C P.2))).prod := by
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
        Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_singleton, Multiset.prod_singleton, ht]
      ring
    have hDteq : ∀ T ∈ (((xQR₁, yQR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        ((xR₁, Wb.toAffine.negY xR₁ yR₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        ((xR₃, yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) ::ₘ
        {((xQR₃, Wb.toAffine.negY xQR₃ yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))}),
        Wb.toAffine.Equation T.1 T.2 := by
      intro T hT
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hQR₁.left
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hR₁neg.left
      rcases Multiset.mem_cons.mp hT with h | hT
      · rw [h]; exact hR₃.left
      · rw [Multiset.mem_singleton.mp hT]; exact hQR₃neg.left
    -- σ-companion nonvanishing
    have hb1 : AdjoinRoot.evalEval hR₁neg.left aP₁ ≠ 0 := by
      refine hoffdiv aP₁ _ hDPeq hDP xR₁ (Wb.toAffine.negY xR₁ yR₁)
        hR₁neg.left ?_
      intro hmem
      rcases Multiset.mem_add.mp hmem with h | h
      · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
        exact hxR₁ (by rw [show xR₁ = xPS₁ from h1]; exact hxPS₁F')
      · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
        exact hxR₁ (by rw [show xR₁ = xS₁ from h1]; exact hxS₁F')
    have hb2 : AdjoinRoot.evalEval hQR₃neg.left aP₁ ≠ 0 := by
      refine hoffdiv aP₁ _ hDPeq hDP xQR₃ (Wb.toAffine.negY xQR₃ yQR₃)
        hQR₃neg.left ?_
      intro hmem
      rcases Multiset.mem_add.mp hmem with h | h
      · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
        exact hxQR₃ (by rw [show xQR₃ = xPS₁ from h1]; exact hxPS₁F')
      · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
        exact hxQR₃ (by rw [show xQR₃ = xS₁ from h1]; exact hxS₁F')
    have hb3 : AdjoinRoot.evalEval hS₁neg.left t ≠ 0 := by
      refine hoffdiv t _ hDteq hDt xS₁ (Wb.toAffine.negY xS₁ yS₁)
        hS₁neg.left ?_
      intro hmem
      rcases Multiset.mem_cons.mp hmem with h | hmem
      · exact hxQR₁nS (congrArg Prod.fst h).symm
      rcases Multiset.mem_cons.mp hmem with h | hmem
      · exact hxR₁ (by
          rw [← show xS₁ = xR₁ from congrArg Prod.fst h]
          exact hxS₁F')
      rcases Multiset.mem_cons.mp hmem with h | hmem
      · exact hxR₃ (by
          rw [← show xS₁ = xR₃ from congrArg Prod.fst h]
          exact hxS₁F')
      · exact hxQR₃ (by
          rw [← show xS₁ = xQR₃ from congrArg Prod.fst
            (Multiset.mem_singleton.mp hmem)]
          exact hxS₁F')
    -- normalize every vertical and constant evaluation
    simp only [map_pow, map_mul, mul_pow, hevvert, hevconst] at hstarinst ⊢
    have hdS := congrArg (AdjoinRoot.evalEval hS₁.left) hceq
    have hdP := congrArg (AdjoinRoot.evalEval hPS₁.left) hceq
    simp only [map_pow, map_mul, mul_pow, hevvert, hevconst] at hdS hdP
    -- the recurring nonzero abscissa differences
    have hne1 : xR₁ - xS₁ ≠ 0 := sub_ne_zero.mpr
      (fun h => hxR₁ (by rw [h]; exact hxS₁F'))
    have hne2 : xQR₃ - xS₁ ≠ 0 := sub_ne_zero.mpr
      (fun h => hxQR₃ (by rw [h]; exact hxS₁F'))
    have hne3 : xS₁ - xR₁ ≠ 0 := sub_ne_zero.mpr
      (fun h => hxR₁ (by rw [← h]; exact hxS₁F'))
    have hne4 : xS₁ - xQR₃ ≠ 0 := sub_ne_zero.mpr
      (fun h => hxQR₃ (by rw [← h]; exact hxS₁F'))
    have hne5 : xPS₁ - xQR₃ ≠ 0 := sub_ne_zero.mpr
      (fun h => hxQR₃ (by rw [← h]; exact hxPS₁F'))
    -- strip the σ-companions from the reciprocity
    have hXY : AdjoinRoot.evalEval hQR₁.left aP₁ *
        AdjoinRoot.evalEval hR₃.left aP₁ *
        ((xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) *
        AdjoinRoot.evalEval hS₁.left t ^ p *
        ((xPS₁ - xR₁) ^ p * (xPS₁ - xQR₃) ^ p) =
        AdjoinRoot.evalEval hR₁.left aP₁ *
        AdjoinRoot.evalEval hQR₃.left aP₁ *
        ((xQR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p) *
        AdjoinRoot.evalEval hPS₁.left t ^ p *
        ((xS₁ - xR₁) ^ p * (xS₁ - xQR₃) ^ p) := by
      refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero hb1 hb2)
        (mul_ne_zero (pow_ne_zero p hne1) (pow_ne_zero p hne2)))
        (pow_ne_zero p hb3))
        (mul_ne_zero (pow_ne_zero p hne3) (pow_ne_zero p hne4))) ?_
      linear_combination hstarinst
    -- close: multiply by the two enabling verticals and telescope
    refine mul_right_cancel₀ (mul_ne_zero
      (pow_ne_zero p hne4) (pow_ne_zero p hne5)) ?_
    linear_combination
      (AdjoinRoot.evalEval hQR₁.left aP₁ * (xR₁ - xS₁) ^ p *
        (xPS₁ - xR₁) ^ p * (xQR₃ - xS₁) ^ p *
        AdjoinRoot.evalEval hR₃.left aP₁ *
        AdjoinRoot.evalEval hPS₁.left aQ₃ * (xPS₁ - xQR₃) ^ p) * hdS -
      (AdjoinRoot.evalEval hQR₃.left aP₁ * (xR₃ - xS₁) ^ p *
        AdjoinRoot.evalEval hS₁.left aQ₃ * (xQR₁ - xS₁) ^ p *
        AdjoinRoot.evalEval hR₁.left aP₁ * (xS₁ - xR₁) ^ p *
        (xS₁ - xQR₃) ^ p) * hdP +
      (c * AdjoinRoot.evalEval hS₁.left aQ₃ *
        AdjoinRoot.evalEval hPS₁.left aQ₃) * hXY
  exact hfin

end WeilPairing
