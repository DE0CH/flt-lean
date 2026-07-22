/-
WeilPairingRecgen.lean — the general two-level reciprocity comparison
(`WeilPairing.recgen`) of the Weil-pairing construction, extracted from
the proof of `exists_weilPairing_mu` (WeilPairing.lean). The R-side
telescoping step is `WeilPairing.stepR` (WeilPairingStepR.lean, imported
here); the S-side step (`hstepS`, the sorry below) is the active
frontier node — see HANDOFF-SESSION.md. Engine facts proved inside the
μ-theorem's body are taken as hypotheses.
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairingStepR

@[expose] public section

namespace WeilPairing

open WeierstrassCurve

set_option maxHeartbeats 16000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem recgen (q p : ℕ) [Fact q.Prime]
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
    : ∀ (F F' : Subfield (AlgebraicClosure (ZMod q))),
    (F : Set (AlgebraicClosure (ZMod q))).Finite →
    (F' : Set (AlgebraicClosure (ZMod q))).Finite → F ≤ F' →
    ∀ (xP yP : (AlgebraicClosure (ZMod q)))
      (hP : Wb.toAffine.Nonsingular xP yP)
      (xQ yQ : (AlgebraicClosure (ZMod q)))
      (hQ : Wb.toAffine.Nonsingular xQ yQ),
    xP ∈ F → yP ∈ F → xQ ∈ F → yQ ∈ F →
    ∀ (xS₁ yS₁ : (AlgebraicClosure (ZMod q)))
      (hS₁ : Wb.toAffine.Nonsingular xS₁ yS₁),
    xS₁ ∈ F' → yS₁ ∈ F' → xS₁ ∉ F →
    ∀ (xR₁ yR₁ : (AlgebraicClosure (ZMod q)))
      (hR₁ : Wb.toAffine.Nonsingular xR₁ yR₁), xR₁ ∉ F' →
    ∀ (xPS₁ yPS₁ : (AlgebraicClosure (ZMod q)))
      (hPS₁ : Wb.toAffine.Nonsingular xPS₁ yPS₁),
    (WeierstrassCurve.Affine.Point.some xPS₁ yPS₁ hPS₁ =
      WeierstrassCurve.Affine.Point.some xP yP hP +
      WeierstrassCurve.Affine.Point.some xS₁ yS₁ hS₁) →
    xPS₁ ∈ F' → yPS₁ ∈ F' →
    ∀ (xQR₁ yQR₁ : (AlgebraicClosure (ZMod q)))
      (hQR₁ : Wb.toAffine.Nonsingular xQR₁ yQR₁),
    (WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
      WeierstrassCurve.Affine.Point.some xR₁ yR₁ hR₁) →
    xQR₁ ≠ xS₁ → xQR₁ ≠ xPS₁ → xQR₁ ∉ F' →
    ∀ (aP₁ aQ₁ : Wb.toAffine.CoordinateRing),
    Ideal.span {aP₁} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xPS₁ (Polynomial.C yPS₁)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xS₁ (Polynomial.C (Wb.toAffine.negY xS₁ yS₁))) ^ p →
    Ideal.span {aQ₁} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xQR₁ (Polynomial.C yQR₁)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xR₁ (Polynomial.C (Wb.toAffine.negY xR₁ yR₁))) ^ p →
    ∀ (xS₃ yS₃ : (AlgebraicClosure (ZMod q)))
      (hS₃ : Wb.toAffine.Nonsingular xS₃ yS₃)
      (xR₃ yR₃ : (AlgebraicClosure (ZMod q)))
      (hR₃ : Wb.toAffine.Nonsingular xR₃ yR₃)
      (xPS₃ yPS₃ : (AlgebraicClosure (ZMod q)))
      (hPS₃ : Wb.toAffine.Nonsingular xPS₃ yPS₃)
      (xQR₃ yQR₃ : (AlgebraicClosure (ZMod q)))
      (hQR₃ : Wb.toAffine.Nonsingular xQR₃ yQR₃)
      (aP₃ aQ₃ : Wb.toAffine.CoordinateRing),
    xS₃ ∉ F' → xR₃ ∉ F' → xPS₃ ∉ F' → xQR₃ ∉ F' →
    (WeierstrassCurve.Affine.Point.some xPS₃ yPS₃ hPS₃ =
      WeierstrassCurve.Affine.Point.some xP yP hP +
      WeierstrassCurve.Affine.Point.some xS₃ yS₃ hS₃) →
    (WeierstrassCurve.Affine.Point.some xQR₃ yQR₃ hQR₃ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQ +
      WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃) →
    Ideal.span {aP₃} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xPS₃ (Polynomial.C yPS₃)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xS₃ (Polynomial.C (Wb.toAffine.negY xS₃ yS₃))) ^ p →
    Ideal.span {aQ₃} =
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xQR₃ (Polynomial.C yQR₃)) ^ p *
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
        xR₃ (Polynomial.C (Wb.toAffine.negY xR₃ yR₃))) ^ p →
    ∀ (xM yM : (AlgebraicClosure (ZMod q)))
      (hM : Wb.toAffine.Nonsingular xM yM),
    (WeierstrassCurve.Affine.Point.some xM yM hM =
      WeierstrassCurve.Affine.Point.some xQR₁ yQR₁ hQR₁ +
      WeierstrassCurve.Affine.Point.some xR₃ yR₃ hR₃) →
    xM ∉ F' →
    ∀ (xM' yM' : (AlgebraicClosure (ZMod q)))
      (hM' : Wb.toAffine.Nonsingular xM' yM'),
    (WeierstrassCurve.Affine.Point.some xM' yM' hM' =
      WeierstrassCurve.Affine.Point.some xPS₁ yPS₁ hPS₁ +
      WeierstrassCurve.Affine.Point.some xS₃ yS₃ hS₃) →
    xM' ∉ F' →
    ∀ (G'' : Subfield (AlgebraicClosure (ZMod q))),
    xR₃ ∈ G'' → yR₃ ∈ G'' → xQR₃ ∈ G'' → yQR₃ ∈ G'' →
    xS₁ ∉ G'' → xPS₁ ∉ G'' → xS₃ ∉ G'' → xPS₃ ∉ G'' → xM' ∉ G'' →
    (AdjoinRoot.evalEval hQR₁.left aP₁ *
      AdjoinRoot.evalEval hR₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₁ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p)) *
    (AdjoinRoot.evalEval hQR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₃) ^ p) *
      AdjoinRoot.evalEval hR₃.left aP₃ *
      AdjoinRoot.evalEval hS₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
      AdjoinRoot.evalEval hPS₃.left aQ₃) =
    (AdjoinRoot.evalEval hQR₃.left aP₃ *
      AdjoinRoot.evalEval hR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₃) ^ p) *
      AdjoinRoot.evalEval hS₃.left aQ₃ *
      AdjoinRoot.evalEval hPS₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) *
    (AdjoinRoot.evalEval hQR₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hR₁.left aP₁ *
      AdjoinRoot.evalEval hS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p) *
    AdjoinRoot.evalEval hPS₁.left aQ₁) := by
  intro F F' hFfin hF'fin hFF' xP yP hP xQ yQ hQ hxPF hyPF hxQF hyQF
    xS₁ yS₁ hS₁ hxS₁F' hyS₁F' hxS₁F xR₁ yR₁ hR₁ hxR₁
    xPS₁ yPS₁ hPS₁ hPSc₁ hxPS₁F' hyPS₁F' xQR₁ yQR₁ hQR₁ hQRc₁
    hxQR₁nS hxQR₁nPS hxQR₁F' aP₁ aQ₁ haP₁ haQ₁
    xS₃ yS₃ hS₃ xR₃ yR₃ hR₃ xPS₃ yPS₃ hPS₃ xQR₃ yQR₃ hQR₃ aP₃ aQ₃
    hxS₃ hxR₃ hxPS₃ hxQR₃ hPSc₃ hQRc₃ haP₃ haQ₃
    xM yM hM hMc hxMF' xM' yM' hM' hM'c hxM'F'
    G'' hxR₃G'' hyR₃G'' hxQR₃G'' hyQR₃G'' hxS₁G'' hxPS₁G'' hxS₃G'' hxPS₃G''
    hxM'G''
  have hstepR := stepR q p Wb yfib hyfib hCunits hline hoffdiv hevvert hnegYF hgenfac hww hbaldiv hevconst hevid hfib2 F' xQ yQ hQ xS₁ yS₁ hS₁ hxS₁F' hyS₁F' xR₁ yR₁ hR₁ hxR₁ xPS₁ yPS₁ hPS₁ hxPS₁F' hyPS₁F' xQR₁ yQR₁ hQR₁ hQRc₁ hxQR₁nS hxQR₁F' aP₁ aQ₁ haP₁ haQ₁ xR₃ yR₃ hR₃ hxR₃ xQR₃ yQR₃ hQR₃ hxQR₃ hQRc₃ aQ₃ haQ₃ xM yM hM hMc hxMF'
  -- the S-STEP: with the second translate R₃ fixed, moving the first
  -- translate S₁ → S₃ preserves the cross-ratio (mirror argument)
  have hstepS :
      (AdjoinRoot.evalEval hQR₃.left aP₁ *
        AdjoinRoot.evalEval hR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hS₁.left aQ₃ *
        AdjoinRoot.evalEval hPS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) *
      (AdjoinRoot.evalEval hQR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₃) ^ p) *
        AdjoinRoot.evalEval hR₃.left aP₃ *
        AdjoinRoot.evalEval hS₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
        AdjoinRoot.evalEval hPS₃.left aQ₃) =
      (AdjoinRoot.evalEval hQR₃.left aP₃ *
        AdjoinRoot.evalEval hR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₃) ^ p) *
        AdjoinRoot.evalEval hS₃.left aQ₃ *
        AdjoinRoot.evalEval hPS₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) *
      (AdjoinRoot.evalEval hQR₃.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
        AdjoinRoot.evalEval hR₃.left aP₁ *
        AdjoinRoot.evalEval hS₁.left
          ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
        AdjoinRoot.evalEval hPS₁.left aQ₃) := by
    -- the σ-mirror instance of the R-step: P↔Q, the S-family
    -- (S₁,PS₁,S₃,PS₃, words aP₁,aP₃) becomes the moving family, the
    -- R₃-family (R₃,QR₃, word aQ₃) the spectator, at the field G''
    have hinst := stepR q p Wb yfib hyfib hCunits hline hoffdiv hevvert hnegYF
      hgenfac hww hbaldiv hevconst hevid hfib2 G'' xP yP hP
      xR₃ yR₃ hR₃ hxR₃G'' hyR₃G''
      xS₁ yS₁ hS₁ hxS₁G''
      xQR₃ yQR₃ hQR₃ hxQR₃G'' hyQR₃G''
      xPS₁ yPS₁ hPS₁ hPSc₁ (fun h => hxR₃ (h ▸ hxPS₁F')) hxPS₁G''
      aQ₃ aP₁ haQ₃ haP₁
      xS₃ yS₃ hS₃ hxS₃G''
      xPS₃ yPS₃ hPS₃ hxPS₃G'' hPSc₃
      aP₃ haP₃
      xM' yM' hM' hM'c hxM'G''
    linear_combination -hinst
  -- the hybrid setup's products are nonzero (avoidance bookkeeping)
  have hDP₁ : Ideal.span {aP₁} =
      ((Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
        Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
        (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            P.1 (Polynomial.C P.2))).prod := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.map_replicate, Multiset.prod_replicate,
      Multiset.prod_replicate, haP₁]
  have hDQ₃ : Ideal.span {aQ₃} =
      ((Multiset.replicate p ((xQR₃, yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
        Multiset.replicate p ((xR₃, Wb.toAffine.negY xR₃ yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))).map
        (fun P : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)) =>
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal Wb.toAffine
            P.1 (Polynomial.C P.2))).prod := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.map_replicate, Multiset.prod_replicate,
      Multiset.prod_replicate, haQ₃]
  have hDP₁eq : ∀ T ∈ (Multiset.replicate p ((xPS₁, yPS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
      Multiset.replicate p ((xS₁, Wb.toAffine.negY xS₁ yS₁) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      Wb.toAffine.Equation T.1 T.2 := by
    intro T hT
    rcases Multiset.mem_add.mp hT with h | h
    · rw [Multiset.eq_of_mem_replicate h]
      exact hPS₁.left
    · rw [Multiset.eq_of_mem_replicate h]
      exact (WeierstrassCurve.Affine.equation_neg
        (W' := Wb.toAffine) _ _).mpr hS₁.left
  have hDQ₃eq : ∀ T ∈ (Multiset.replicate p ((xQR₃, yQR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q))) +
      Multiset.replicate p ((xR₃, Wb.toAffine.negY xR₃ yR₃) : (AlgebraicClosure (ZMod q)) × (AlgebraicClosure (ZMod q)))),
      Wb.toAffine.Equation T.1 T.2 := by
    intro T hT
    rcases Multiset.mem_add.mp hT with h | h
    · rw [Multiset.eq_of_mem_replicate h]
      exact hQR₃.left
    · rw [Multiset.eq_of_mem_replicate h]
      exact (WeierstrassCurve.Affine.equation_neg
        (W' := Wb.toAffine) _ _).mpr hR₃.left
  have hevP₁R₃ : AdjoinRoot.evalEval hR₃.left aP₁ ≠ 0 := by
    refine hoffdiv aP₁ _ hDP₁eq hDP₁ xR₃ yR₃ hR₃.left ?_
    intro hmem
    rcases Multiset.mem_add.mp hmem with h | h
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxR₃ (by rw [show xR₃ = xPS₁ from h1]; exact hxPS₁F')
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxR₃ (by rw [show xR₃ = xS₁ from h1]; exact hxS₁F')
  have hevP₁QR₃ : AdjoinRoot.evalEval hQR₃.left aP₁ ≠ 0 := by
    refine hoffdiv aP₁ _ hDP₁eq hDP₁ xQR₃ yQR₃ hQR₃.left ?_
    intro hmem
    rcases Multiset.mem_add.mp hmem with h | h
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxQR₃ (by rw [show xQR₃ = xPS₁ from h1]; exact hxPS₁F')
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxQR₃ (by rw [show xQR₃ = xS₁ from h1]; exact hxS₁F')
  have hevQ₃PS₁ : AdjoinRoot.evalEval hPS₁.left aQ₃ ≠ 0 := by
    refine hoffdiv aQ₃ _ hDQ₃eq hDQ₃ xPS₁ yPS₁ hPS₁.left ?_
    intro hmem
    rcases Multiset.mem_add.mp hmem with h | h
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxQR₃ (by rw [← show xPS₁ = xQR₃ from h1]; exact hxPS₁F')
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxR₃ (by rw [← show xPS₁ = xR₃ from h1]; exact hxPS₁F')
  have hevQ₃S₁ : AdjoinRoot.evalEval hS₁.left aQ₃ ≠ 0 := by
    refine hoffdiv aQ₃ _ hDQ₃eq hDQ₃ xS₁ yS₁ hS₁.left ?_
    intro hmem
    rcases Multiset.mem_add.mp hmem with h | h
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxQR₃ (by rw [← show xS₁ = xQR₃ from h1]; exact hxS₁F')
    · have h1 := congrArg Prod.fst (Multiset.eq_of_mem_replicate h)
      exact hxR₃ (by rw [← show xS₁ = xR₃ from h1]; exact hxS₁F')
  have hAh : (AdjoinRoot.evalEval hQR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hR₃.left aP₁ *
      AdjoinRoot.evalEval hS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
      AdjoinRoot.evalEval hPS₁.left aQ₃) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ hevP₁R₃) ?_) hevQ₃PS₁
    · rw [map_pow, hevvert xS₁ xQR₃ yQR₃ hQR₃.left]
      exact pow_ne_zero _ (sub_ne_zero.mpr
        (fun h => hxQR₃ (by rw [h]; exact hxS₁F')))
    · rw [map_pow, hevvert xR₃ xS₁ yS₁ hS₁.left]
      exact pow_ne_zero _ (sub_ne_zero.mpr
        (fun h => hxR₃ (by rw [← h]; exact hxS₁F')))
  have hBh : (AdjoinRoot.evalEval hQR₃.left aP₁ *
      AdjoinRoot.evalEval hR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₃ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hevP₁QR₃ ?_) hevQ₃S₁) ?_
    · rw [map_pow, hevvert xS₁ xR₃ yR₃ hR₃.left]
      exact pow_ne_zero _ (sub_ne_zero.mpr
        (fun h => hxR₃ (by rw [h]; exact hxS₁F')))
    · rw [map_pow, hevvert xR₃ xPS₁ yPS₁ hPS₁.left]
      exact pow_ne_zero _ (sub_ne_zero.mpr
        (fun h => hxR₃ (by rw [← h]; exact hxPS₁F')))
  refine mul_right_cancel₀ (mul_ne_zero hAh hBh) ?_
  linear_combination
    ((AdjoinRoot.evalEval hQR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₃) ^ p) *
      AdjoinRoot.evalEval hR₃.left aP₃ *
      AdjoinRoot.evalEval hS₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p) *
      AdjoinRoot.evalEval hPS₃.left aQ₃) *
     (AdjoinRoot.evalEval hQR₃.left aP₁ *
      AdjoinRoot.evalEval hR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₃ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p))) * hstepR +
    ((AdjoinRoot.evalEval hQR₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hR₁.left aP₁ *
      AdjoinRoot.evalEval hS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₁) ^ p) *
      AdjoinRoot.evalEval hPS₁.left aQ₁) *
     (AdjoinRoot.evalEval hQR₃.left aP₁ *
      AdjoinRoot.evalEval hR₃.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xS₁) ^ p) *
      AdjoinRoot.evalEval hS₁.left aQ₃ *
      AdjoinRoot.evalEval hPS₁.left
        ((WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xR₃) ^ p))) * hstepS

end WeilPairing
