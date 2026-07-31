/-
IsogenySignature.lean — own work for the Fermat project.

**HOISTED OUT OF `FreyCurve/MazurTorsion.lean` ON 2026-07-30 (flt-lean-164).
Statements, proofs and docstrings are unchanged; only their module has
changed.**

WHY.  `ModularCurve/X0.lean` had to restate Mazur 1978 §5 as its own leaf
`false_of_stable_of_forall_padicValRat_nonneg`, because the proof of that
statement lives in `MazurTorsion.lean` and `MazurTorsion.lean` IMPORTS
`X0.lean`.  Both files' docstrings recorded the repair — hoist the parts of
the argument that do not need `X0.lean` into a module upstream of both — and
recorded it as blocked on a boundary nobody had measured.  It is measured
here, and the boundary is clean:

* the material moved is `WeierstrassCurve.exists_isogenyCharacter` and its
  `hstable ↔ hlam` bridge (former lines 757–1012), together with steps 1–3 of
  Mazur's argument — Serre–Raynaud signatures, the resultant elimination and
  the class-number-one determination (former lines 5623–19690);
* over those 14 324 lines there is **not one** reference to a name declared in
  `X0.lean`, `X1.lean` or `Mathlib/AlgebraicGeometry/NeronModel.lean` — the
  only three imports of `MazurTorsion.lean` whose own closures reach `X0.lean`,
  so those three are dropped from the header below;
* and the moved block references exactly ONE declaration left behind in
  `MazurTorsion.lean`: `potentiallyGoodReduction_of_isogenyCharacter`, which is
  step 0 (Mazur's Cor. 4.4) and is precisely the half that DOES need `X0.lean`.
  Its single use is in the assembly `not_isogenyCharacter_of_prime_ge_twentyThree`,
  which therefore stays in `MazurTorsion.lean` with it.

WHAT THIS BUYS.  `X0.lean` now imports this module and proves
`false_of_stable_of_forall_padicValRat_nonneg` by citation instead of by
`sorry`, so the duplicated statement of Mazur §5 is gone.  The consumers of
this material inside `MazurTorsion.lean` are unaffected: that file imports
this one.

NOTE ON THE OLD LINE NUMBERS RECORDED IN `X0.lean`.  Its docstring said the
hoistable block was "`MazurTorsion.lean` lines ~2229–6700 plus ~600–780".
That was measured when the file was ~35 000 lines; it is now 80 329, and the
figures above supersede it.
-/

module

public import Fermat.FLT.FreyCurve.Basic
-- `curve11a3`, `curve11a3_finite` and `curve11a3_points`: the
-- Mordell–Weil input of level `11`, consumed by
-- `WeierstrassCurve.x1Eleven_11a3_x_eq_zero_or_one` below.
public import Fermat.FLT.EllipticCurve.MordellWeil
-- `MazurX0Nineteen.rational_point_x0Nineteen`: the two affine rational
-- points of `19a1`, the Mordell–Weil input of level `19`, consumed by
-- `X0GenusOne.finite_curve19a1` below.
public import Fermat.FLT.EllipticCurve.MordellWeil19
public import Fermat.FLT.EllipticCurve.Torsion
-- `natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq_le` and the Bézout
-- relation `isCoprime_Φ_ΨSq`: the division-polynomial inputs of the
-- `p`-divisibility of the kernel of reduction
-- (`exists_localKernelDivision_of_good_reduction`). Both modules are
-- already in the transitive cone through `TorsionCard`, but only via
-- PRIVATE imports there, which are not re-exported — so they must be
-- imported publicly here.
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
-- Short normal forms (`IsShortNF`, `exists_variableChange_isShortNF`,
-- `j_of_isShortNF`, `Δ_of_isShortNF`): PUBLIC because `IsShortNF` occurs in the
-- SIGNATURE of `MazurLevelSeven.exists_kernelCoords_of_isShortNF` below, and a
-- bare `import` is not re-exported.
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
-- `exists_variableChange_of_j_eq`: over a separably closed field, two elliptic
-- curves with the same `j`-invariant differ by an admissible change of
-- variables. This is what turns `j(E'') = j(E)` into a `ℚ̄`-isomorphism
-- `E'' ≅ E`, hence a SELF-isogeny of `E_ℚ̄`, in
-- `MazurLevelFortyNine.exists_selfIsogeny_of_j_eq` below.
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
-- Vélu's construction of the quotient of an elliptic curve by a finite
-- Galois-stable subgroup of odd order (`exists_velu_quotient_isogeny`), which
-- discharges `exists_quotient_isogeny_of_odd_prime_card` below.
public import Fermat.FLT.EllipticCurve.Velu
-- Isogeny-as-morphism: `WeierstrassCurve.End` and its `IsRationalMap`
-- faithfulness certificate, which is what lets the Atkin-Lehner conditions
-- `ψ² = [-125]` / `ψ² = [-169]` be STATED at all (see the level-125 and
-- level-169 descent leaves below). `public` because `End` occurs in signature
-- position there.
public import Fermat.FLT.EllipticCurve.Isogeny
-- The differential character `λ : End(E_ℚ̄) → ℚ̄` (`IsDiffChar`), which is what
-- `MazurLevelFortyNine.exists_sqrtNegOne_galSign` is proven over.
public import Fermat.FLT.EllipticCurve.DifferentialCharacter
public import Fermat.FLT.EllipticCurve.IsogenyTrace
-- Infinite Galois theory (`InfiniteGalois.mem_range_algebraMap_iff_fixed`) and
-- perfect fields (`Algebra.IsAlgebraic.isSeparable_of_perfectField`), used by
-- `MazurLevelFortyNine.mem_range_algebraMap_of_fixed` below.
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Perfect
-- `cyclotomicCharacterModL` and the stable-line extraction, used in the
-- character bookkeeping of the Serre §4.1 dichotomy.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `det_galoisRep_eq_cyclotomic` (the DERIVED determinant node), the
-- `χ₁χ₂ = ω̄` input of the dichotomy derivation.
public import Fermat.FLT.EllipticCurve.WeilPairing
-- `HasseBound.sq_frobeniusTrace_le` — Hasse's bound, proven there over the
-- single isogeny-degree leaf `HasseBound.natCard_ker_degreeFormEnd`, together
-- with the point-level Frobenius `HasseBound.frobeniusPointEnd` and the
-- endomorphism `HasseBound.degreeFormEnd` (`[m] − [n]∘F`).  Shared
-- infrastructure between `hasse_bound_natCard_affine_point` and
-- `natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` below.
public import Fermat.FLT.EllipticCurve.HasseBound
-- `WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`: the
-- automorphism group of an elliptic curve over a field has exponent dividing
-- `12` (Silverman *AEC* App. A.1; Kraus).  This is the geometric half of leaf
-- `B₀²` below — the ONLY place the classification of the semistability defect
-- is consumed, and what excludes an element of order `8` in the image of
-- inertia at a prime of potentially good reduction.
public import Fermat.FLT.EllipticCurve.AutomorphismExponent
-- `FreyCurve.torsion_isUnramified` (unramifiedness outside `{2, p}`),
-- consumed by the derivation of the semistability leaf.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.FreyConditions
-- `localInertiaGroup` and the restriction `Γ ℚ_q → Γ ℚ`, used to state
-- the Minkowski node.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- The Minkowski block itself (`minkowski_character_trivial`,
-- `isUnramifiedAt_of_inertia_le_fixingSubgroup`,
-- `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`,
-- `isOpen_setOf_galoisRep_eq_one`), hoisted VERBATIM out of this file on
-- 2026-07-27 so that the isogeny-character section ~27000 lines above its
-- old home can use it. `public` so every downstream consumer keeps
-- resolving these names through `MazurTorsion` exactly as before.
public import Fermat.FLT.GaloisRepresentation.SubQuotCharacter
public import Fermat.FLT.GaloisRepresentation.MinkowskiUnramified
-- TAME INERTIA THEORY at a finite place (`wildInertiaGroup`,
-- `exists_pow_eq_of_mem_wildInertiaGroup` — `P_v` is pro-`ℓ` so the `n`-th
-- power map is onto it for `ℓ ∤ n` — and
-- `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker` — every finite
-- abstract quotient of `I_v` killing `P_v` is cyclic). Those two are what
-- prove `WeierstrassCurve.exists_isogenyTameExponentAt` (leaf `A₀-2`) below.
-- COST CHECK (2026-07-27): this adds exactly ONE module to this file's
-- import cone — `ArtinConductor`'s own 23-module cone is already contained
-- in it.
public import Fermat.FLT.Deformations.RepresentationTheory.ArtinConductor
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, the place of `ℚ`
-- attached to a prime number.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- conjugacy of the valuation subrings of `ℚ̄` above a prime number
-- (`AlgebraicIntegersRat.exists_smul_eq_of_valuationSubring`), which closes
-- `GaloisRepresentation.exists_smul_eq_globalValuationSubring` below.
public import Fermat.FLT.Mathlib.RingTheory.Valuation.AlgebraicIntegerConjugacy
-- the reduction-of-POINTS theory (`WeierstrassCurve.IsReductionAlong`, `redHom`),
-- used in SIGNATURE position by the local reduction leaves below, hence `public`
public import Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction
-- the torsion/reduction brick (`exists_reduction_dvd_addOrderOf_of_jIntegral`,
-- `natCard_affine_point_le`, `natCard_affine_point_pos`), used by
-- `no_rational_point_of_isogenyPrime_jInvariant` below. Imported DIRECTLY: it
-- arrived on a branch that also carried a rival `14a4` route in
-- `MordellWeil.lean`, which was not taken, so it is not re-exported from there.
public import Fermat.FLT.EllipticCurve.TorsionReduction
-- the kernel-polynomial criterion for a rational cyclic `p`-isogeny
-- (`WeierstrassCurve.IsKernelPolynomial`, `exists_point_of_isKernelPolynomial`),
-- cut out of `exists_isogenyCurve_of_genusOneJTable` below. `IsKernelPolynomial`
-- appears in SIGNATURE position there, where a merely transitive import is not
-- re-exported, so this must be a `public import`.
public import Fermat.FLT.EllipticCurve.KernelPolynomial
-- the six explicit kernel-polynomial certificates at the genus-one isogeny
-- primes, which discharge `exists_kernelPolynomial_of_genusOneJTable` below.
-- `public` because that theorem's witnesses (`GenusOneKernel.curve₁`, …) and
-- their `IsElliptic` instances are used in the proof term.
public import Fermat.FLT.EllipticCurve.GenusOneKernelPolynomials
-- mathlib's reduction theory of Weierstrass equations over a DVR
-- (`IsMinimal`, `HasGoodReduction`, `reduction`). It already reaches this file
-- publicly through `TorsionReduction → GoodReduction`, and is named here
-- because `WeierstrassCurve.PotentiallyGoodModel` uses `HasGoodReduction` in
-- SIGNATURE position, where a merely transitive import is not re-exported.
-- (A 2026-07-28 branch hoisted that structure into a new
-- `Fermat.FLT.FreyCurve.PotentiallyGoodModel`; the release-12 integration
-- REJECTED the hoist and deleted the file, so the structure is still below in
-- THIS file and this import is still needed here.)
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
-- `IsOpenImmersion.of_flat_of_mono`, consumed by
-- `X0GenusOne.isIso_of_mono_of_relCurve` below.  PUBLIC deliberately: a
-- bare `import` is not re-exported, and this file is itself publicly
-- imported.
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
-- VENDORING ADDITION (2026-07-30): `Matrix.card_GL_field`, for
-- `card_units_end_finrank_two_five` below (`#GL₂(𝔽₅) = 480`).
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
-- NOTE (2026-07-30): `Fermat.locallyOfFinitePresentation_of_comp` (Stacks 02FV)
-- and `Fermat.flat_of_flat_fiberMap` (the fibrewise criterion of flatness), both
-- consumed by `X0GenusOne.etale_of_mono_of_relCurve` / `flat_of_mono_of_relCurve`
-- below, need NO import of their own: they live in
-- `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`, which is in this file's cone
-- along the fully PUBLIC path `MazurTorsion → ModularCurve/X0 → AbelianSchemeIsogeny`,
-- hence re-exported.  An earlier revision hoisted `locallyOfFinitePresentation_of_comp`
-- into a module of its own on the premise that `AbelianSchemeIsogeny` "is not in this
-- file's import cone, and cannot be"; that premise was FALSE when checked against the
-- import graph, and the hoist has been withdrawn.
-- Minkowski's discriminant theorem (`exists_not_isUnramifiedAt_int_of_isGalois`)
-- and the going-up prime lifting, used in the Minkowski assembly proof.
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Ideal.GoingUp
-- Quadratic reciprocity (`legendreSym.quadratic_reciprocity'`, `legendreSym.at_neg`,
-- `ZMod.χ₄_eq_neg_one_pow`): the bridge `(−N/q) = (q/N)` valid for `N ≡ 3 (mod 4)`,
-- proven as `mazurIsogeny_isSquare_of_isSquare_neg` and consumed by the
-- signature-`6` branch of Mazur's isogeny theorem.
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
-- The local inertia-fixed-field node (`e(M/ℚ_q) = 1` for finite
-- subextensions of `ℚ_qᵃˡᵍ` fixed by the local inertia), consumed by
-- the transport proof of the Minkowski surjectivity theorem below.
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- `adicCompletion.maximalIdeal_eq_span_uniformizer`, used to identify
-- the maximal ideal of `ℤ_q` with the span of `q`.
import Fermat.FLT.DedekindDomain.AdicValuation
-- `Ideal.Quotient.stabilizerHom_surjective_of_profinite`: a profinite group
-- acting on `B` with fixed subring `A` has the stabilizer of a prime `Q`
-- surjecting onto `Aut((B/Q)/(A/P))`.  This is the arithmetic engine of
-- `GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_intermediateField`.
-- (`Fermat.FLT.Deformations.RepresentationTheory.Frobenius` imports it
-- non-publicly, so it is not visible through that route.)
import Mathlib.RingTheory.Invariant.Profinite
-- `IntermediateField.adjoin_toSubalgebra_of_isAlgebraic`, identifying the
-- compositum `ℚ_q · F` with the `ℚ_q`-subalgebra generated by `F`, used by
-- `GaloisRepresentation.exists_int_sub_mem_maximalIdeal_of_mem_adjoin`.
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
-- The structure theorem for finite abelian groups
-- (`AddCommGroup.equiv_directSum_zmod_of_finite`) and the `ZMod` Chinese
-- remainder theorem (`ZMod.prodEquivPi`), used in the PROVEN rank-`≤ 2`
-- decomposition backing Mazur's classification.
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
-- `ordProj`/`ordCompl` and `Nat.floorRoot`, i.e. the prime-exponent bookkeeping
-- that turns "every exponent outside `{2, 37}` is a multiple of `3`" into an
-- actual cube.  Consumed by `exists_cubeClass_of_supp_dvd_296` in the level-`37`
-- descent below; `Factorization.PrimePow` above reaches `Factorization.Basic`
-- only transitively through a bare import, which does not re-export it.
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Root
-- `Rat.isSquare_intCast_iff`, the bridge turning "this rational is a
-- square" into "this integer is a square"; consumed by the `X_1(15)`
-- descent reduction `MazurLevel15.rank_zero_x`.
public import Mathlib.Data.Rat.Lemmas
-- `DualNumber R = R[ε]`, `ε² = 0`, and its algebra maps: the base over
-- which a TANGENT VECTOR to the special fibre is a relative point, used
-- by `IsCuspFormalImmersionCert` to state Mazur's §II.4 formal immersion
-- infinitesimally.
public import Mathlib.Algebra.DualNumber
-- The unramified quadratic twist to split multiplicative reduction and
-- its Galois-equivariant point equivalence, consumed by the PROVEN
-- local torsion quotient of the nonsplit multiplicative case
-- (`exists_localTorsionQuotient_of_nonsplit`).
-- PUBLIC (promoted 2026-07-28): `quadraticTwist`, `Algebra.IsQuadraticExtension`
-- and `quadraticCharacter` occur in SIGNATURE position in the two leaves of the
-- `T₁` cut below
-- (`hasSplitMultiplicativeReduction_or_exists_quadraticTwist_of_padicValRat_j_neg`
-- and `exists_splitModel_quadraticCharacter_pointEquiv_of_padicValRat_j_neg`),
-- where a bare `import` is not re-exported.
public import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
-- Fermat's little theorem (`ZMod.pow_card_sub_one_eq_one`), the cyclic
-- structure of a group of prime order (`isAddCyclic_of_prime_card`), and
-- Lagrange for the quotient by the eigenline
-- (`AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup`): the three
-- inputs of the Borel exponent bound `borel_bound_iterate_eq_self`.
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
-- `not_fermat_42` and the classification of primitive Pythagorean triples: the two
-- classical inputs of the `X_1(16)` descent in `MazurSixteen.not_sextic_square`.
import Mathlib.NumberTheory.FLT.Four
-- `fermatLastTheoremThree` (and `fermatLastTheoremFor_iff_rat`, re-exported
-- through it): the Mordell–Weil half of the `X_0(27)` node below.  `X_0(27)`
-- IS the Fermat cubic — `y² + y = x³ − 7` is `Y² = X³ − 432` is `x³ + y³ = z³`
-- — so the determination of its rational points is exactly Fermat's Last
-- Theorem for exponent `3`.  See `MazurLevel27.rational_point_x0TwentySeven`.
import Mathlib.NumberTheory.FLT.Three
-- `TorsionCharP.exists_zsmul_eq_of_charP`: cyclicity of the geometric
-- `p`-torsion in characteristic `p`, the inseparability input of
-- `exists_zsmul_eq_of_mem_torsionBy_of_charP` below.
import Fermat.FLT.EllipticCurve.TorsionCharP
-- The genus-`2` hyperelliptic layer: the smooth projective model of a monic
-- sextic in `ℙ(1,3,1)`, its integral weighted-projective coordinates, the
-- reduction map `X(ℚ) → X(𝔽ₚ)`, and the Jacobian package (`Pic⁰` + Abel–Jacobi
-- + reduction + rank `0`).  Supplies
-- `Fermat.Hyperelliptic.X18.no_noncuspidal_point`, the smooth-model form of
-- `MazurLevel18.no_noncuspidal_point_on_smooth_model` below, together with the
-- machine-checked count `#X_1(18)(𝔽₅) = 6`.
import Fermat.FLT.ModularCurve.HyperellipticJacobian
-- The Gaussian-integer infinite descent on `e² = X⁴ − 11X²Y² − Y⁴`: the
-- arithmetic input of the `X_1(2,10)` node
-- (`MazurTwoTen.quartic_no_solution`).
public import Fermat.FLT.FreyCurve.QuarticDescent
-- The modular curve `Y_0(N)` as a coarse moduli space over `ℚ`
-- (`Fermat.Y0HasNoRationalPoint`, `Fermat.false_of_stable_of_y0HasNoRationalPoint`):
-- the twelve levels of Kenku's non-prime-power determination below are proven
-- from the corresponding rational-point statements about that curve.
-- The modular curve `Y_1(N)`/`X_1(N)` as a coarse moduli space over `ℚ`, the
-- `Γ₁` companion of `X0.lean` (`Fermat.IsX1Compactification`,
-- `Fermat.exists_notCusp_of_ratPoint`, `Fermat.HasRankZeroJacobian` reused
-- from `X0.lean`): level `25` below — `MazurX1Plane.exists_isX1TwentyFiveDatum`
-- — is proven from it, the `Γ₀` route at that level being not merely
-- unavailable but REFUTED (`X_0(25)` has genus `0` and a rational cyclic
-- `25`-isogeny exists, the class `11a`).
-- The Tate normal form and the level-`7` parametrisation, used by
-- `not_order_two_and_order_seven_point` below.
public import Fermat.FLT.FreyCurve.TateNormalForm
-- Good reduction of abelian varieties (Serre–Tate / Néron–Ogg–Šafarevič) and the
-- Néron mapping property (`Fermat.exists_goodReductionModel_of_surjective`,
-- `Fermat.exists_neronExtension`): the two classical inputs from which
-- `exists_abelianGoodReductionModel` below is PROVEN.  They carry no modular
-- content and live outside this file so that `ModularCurve/X1.lean` can reuse them
-- verbatim.
-- Gauss's theory of integral binary quadratic forms — reduction theory and
-- Rabinowitsch's criterion — carrying `mazurIsogeny_rabinowitsch_bound` down
-- to the single deep input `neg_163_le_of_classNumberOne` (class number one).
public import Fermat.FLT.Mathlib.NumberTheory.BinaryQuadraticForm
-- `IsConjRoot.exists_algEquiv`: two elements of a normal extension with the same
-- minimal polynomial lie in one `Gal`-orbit.  Consumed by
-- `MazurLevelFortyNine.exists_gal_fix_sqrtNegOne_cyclotomicSeven_eq_three` to
-- produce the automorphism `ω ↦ ω¹⁷` of `ℚ̄` directly, with no intermediate
-- cyclotomic field and no lifting step.
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
-- `Polynomial.cyclotomic_eq_minpoly_rat`: `Φₙ` is the minimal polynomial over `ℚ`
-- of a primitive `n`-th root of unity (this is where the irreducibility of `Φ₂₈`
-- enters the same leaf).
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
-- `MvPolynomial` and `Ideal.Quotient.liftₐ`: the affine plane curve
-- `V(F) = Spec (ℚ[x,y]/(F))` and the dictionary between its `ℚ`-points and the
-- solutions of `F = 0`, used by the level-`37` plane model
-- (`relPointEquivZeroLocusQ` and the block around it).
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-- **The isogeny character of a Galois-stable cyclic subgroup**
(PROVEN 2026-07-25): if a geometric point `g` of an elliptic curve
`E/ℚ` has exact finite order `N > 0` and its cyclic subgroup `⟨g⟩` is
stable under `Gal(ℚ̄/ℚ)`, then the Galois action on `⟨g⟩` is given by a
character

  `λ : Gal(ℚ̄/ℚ) → (ℤ/N)ˣ`,    `σ(g) = λ(σ) · g`.

This is the object every treatment of Mazur's theorem begins from — the
**isogeny character** of the `N`-isogeny `E → E/⟨g⟩` whose kernel is
`⟨g⟩` (Mazur, *Rational isogenies of prime degree*, §5; Serre,
*Propriétés galoisiennes*, §5.4).

Proof: `σ` carries `g` into `⟨g⟩`, so `σ(g) = k(σ) · g` for some integer
`k(σ)`, well defined modulo `N` because `addOrderOf g = N`
(`addOrderOf_dvd_iff_zsmul_eq_zero` against
`ZMod.intCast_zmod_eq_zero_iff_dvd`). Multiplicativity is
`Affine.Point.map_map` — the coercion of a product in
`Field.absoluteGaloisGroup ℚ` is the composite of the coercions — plus
additivity of `Affine.Point.map`. The identity of `Gal(ℚ̄/ℚ)` acts as
the identity on points, so `k(1) = 1` and hence `k(σ) k(σ⁻¹) = 1`,
which exhibits `k(σ)` as a unit without any appeal to `ZMod N` being a
field.

No primality is needed, only `0 < N`. That hypothesis is not cosmetic:
it is what makes `ZMod.val` a section of `ℕ → ZMod N`, which the
normalisation `λ(σ).val • g` in the conclusion requires. For `N = 0`
(a point of infinite order) `ZMod.val` is `Int.natAbs` and the
conclusion as stated would be FALSE, even though the character itself
still exists with values in `{±1}`. -/
theorem WeierstrassCurve.exists_isogenyCharacter (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hNpos : 0 < N) (hg : addOrderOf g = N)
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g) :
    ∃ lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ,
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
          ((lam σ : ZMod N).val) • g := by
  classical
  haveI : NeZero N := ⟨hNpos.ne'⟩
  -- The integer coefficient of a multiple of `g` is determined modulo `N`.
  have hiff : ∀ a b : ℤ, a • g = b • g ↔ (a : ZMod N) = (b : ZMod N) := by
    intro a b
    constructor
    · intro h
      have h0 : (a - b) • g = 0 := by rw [sub_zsmul, h, add_neg_cancel]
      have hd : (addOrderOf g : ℤ) ∣ (a - b) :=
        addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
      rw [hg] at hd
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mpr hd
      rw [Int.cast_sub, sub_eq_zero] at hz
      exact hz
    · intro h
      have hz : ((a - b : ℤ) : ZMod N) = 0 := by rw [Int.cast_sub, h, sub_self]
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mp hz
      rw [← hg] at hd
      have h0 := addOrderOf_dvd_iff_zsmul_eq_zero.mp hd
      rw [sub_zsmul, add_neg_eq_zero] at h0
      exact h0
  -- Galois moves `g` inside `⟨g⟩`; choose an integer coefficient for each `σ`.
  have hmem : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g ∈
        AddSubgroup.zmultiples g :=
    fun σ => hstable σ g (AddSubgroup.mem_zmultiples g)
  choose k hk using fun σ => AddSubgroup.mem_zmultiples_iff.mp (hmem σ)
  -- The Galois action on points is a monoid action.
  have hcomp : ∀ σ τ : Field.absoluteGaloisGroup ℚ,
      ∀ P : (E⁄(AlgebraicClosure ℚ)).Point,
      Affine.Point.map
          ((σ * τ : Field.absoluteGaloisGroup ℚ) :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
          (Affine.Point.map
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P) := by
    intro σ τ P
    have hc : ((σ * τ : Field.absoluteGaloisGroup ℚ) :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom =
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.comp
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom :=
      AlgHom.ext fun x => rfl
    rw [Affine.Point.map_map, hc]
  -- Multiplicativity of the coefficient.
  have hmul : ∀ σ τ : Field.absoluteGaloisGroup ℚ,
      ((k (σ * τ) : ℤ) : ZMod N) = ((k σ : ℤ) : ZMod N) * ((k τ : ℤ) : ZMod N) := by
    intro σ τ
    have h1 : (k (σ * τ)) • g = (k σ * k τ) • g := by
      rw [hk (σ * τ), hcomp σ τ g, ← hk τ, map_zsmul, ← hk σ, smul_smul,
        mul_comm (k τ) (k σ)]
    have h2 := (hiff _ _).mp h1
    push_cast at h2
    exact h2
  -- The identity acts trivially, so the coefficient at `1` is `1`.
  have hmap1 : ∀ P : (E⁄(AlgebraicClosure ℚ)).Point,
      Affine.Point.map
        ((1 : Field.absoluteGaloisGroup ℚ) :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom P = P := by
    intro P; cases P <;> rfl
  have hone : ((k 1 : ℤ) : ZMod N) = 1 := by
    have h1 : (k 1) • g = (1 : ℤ) • g := by rw [hk 1, one_zsmul, hmap1 g]
    have h2 := (hiff _ _).mp h1
    rwa [Int.cast_one] at h2
  -- Hence every coefficient is a unit, with inverse the coefficient at `σ⁻¹`.
  have hunit : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ((k σ : ℤ) : ZMod N) * ((k σ⁻¹ : ℤ) : ZMod N) = 1 := by
    intro σ
    rw [← hmul σ σ⁻¹, mul_inv_cancel, hone]
  refine ⟨MonoidHom.mk' (fun σ => ⟨((k σ : ℤ) : ZMod N), ((k σ⁻¹ : ℤ) : ZMod N),
      hunit σ, (mul_comm _ _).trans (hunit σ)⟩)
    (fun σ τ => Units.ext (by simpa using hmul σ τ)), ?_⟩
  intro σ
  rw [← hk σ, ← natCast_zsmul]
  refine (hiff _ _).mpr ?_
  simp [ZMod.natCast_val]

/-!
##### Mazur's isogeny theorem, cut along its own proof (2026-07-26)

`not_isogenyCharacter_of_prime_ge_twentyThree` used to be a single bare
`sorry` carrying an audit that read "IRREDUCIBLE at this mathlib pin:
the proof is the Eisenstein-ideal descent on `J_0(N)`". That audit was
right that the Eisenstein ideal is needed and WRONG about how much of
the theorem needs it. Following Mazur's own argument — as laid out in
P. Michaud-Jacobs, *Mazur's isogeny theorem* (arXiv:2209.03153v2, an
expository account of Mazur, Invent. Math. 44 (1978), Thm 1) — the proof
factors into FOUR steps that rest on three completely different bodies
of mathematics, and only ONE of them is modular:

0. `potentiallyGoodReduction_of_isogenyCharacter` (Mazur 1978, Cor 4.4;
   [MJ, Thm 3.1]). For `N > 19`, a curve with a rational `N`-isogeny has
   potentially good reduction at every prime `q ∉ {2, N}`. **This is the
   only modular step.** Its proof is: a point of potentially
   multiplicative reduction reduces to a cusp of `X_0(N)` mod `q`; the
   Abel–Jacobi map into the Eisenstein quotient `J_e(N)` — which has
   Mordell–Weil rank `0` over `ℚ` by Mazur, *Modular curves and the
   Eisenstein ideal*, IHÉS 47 (1977), Thm 4 — is a formal immersion at
   the cusp in characteristic `q ≠ 2`, so the point IS the cusp.
   Note what the STATEMENT costs: nothing. It is an inequality on the
   `q`-adic valuation of the `j`-invariant, so it can be stated, and
   consumed, with no modular curve, no Jacobian and no Hecke algebra in
   sight. All of that machinery is needed only to PROVE it.

1. `exists_isogenySignature` (Serre 1972 + Raynaud; [MJ, Thm 4.1]).
   `λ¹² = χ^s` globally, with the *isogeny signature* `s ∈ {0,4,6,8,12}`,
   and `s = 6` forces `N ≡ 3 (mod 4)`. Local theory at `N` only: over
   `ℚ_N` the curve is a (twisted) Tate curve or acquires good reduction
   over an extension of ramification degree `e ∈ {1,2,3,4,6}`, and
   Raynaud's classification gives `λ^e|_{I'} = χ^r|_{I'}` with `0 ≤ r ≤ e`;
   `s = 12r/e`. Away from `N`, `λ¹²` is unramified in BOTH reduction
   types, so `λ¹²χ^{-s}` is everywhere unramified, hence trivial. This
   step does NOT use step 0.

2. `not_isogenyCharacter_of_isogenySignature_ne_six` ([MJ, Prop 4.3]).
   For a Frobenius `σ_q` at a prime `q ≠ N` of potentially good
   reduction, `λ(σ_q)` is a common root mod `N` of `X¹² − q^s` and of
   `X² − Tr ρ(σ_q) X + q`, where `Tr ρ(σ_q) ∈ ℤ` with `|Tr| ≤ 2√q`
   (Serre–Tate, Thm 3; Hasse–Weil in the good-reduction case). So `N`
   divides `R_{q,s} := lcm_{|a| ≤ 2√q} Res(X² − aX + q, X¹² − q^s)`, a
   FINITE integer depending only on `q` and `s`. Step 0 is what licenses
   `q = 3` and `q = 5`. Verified here in PARI/GP (untrusted searcher; the
   Lean proof must recompute these resultants in-kernel), reproducing
   [MJ, §4.2]:

   * `R(3,0)  = 8131531262400 = 2⁶·3²·5²·7²·13²·19·37·97`
   * `R(5,0)  = 17072929032886039622400 = 2⁸·3⁵·5²·7²·13²·17·31²·37·61·157·229`
   * `R(3,4)  = 9815256000 = 2⁶·3⁸·5³·11·17`
   * `R(3,8)  = 795035736000 = 2⁶·3¹²·5³·11·17`
   * `R(3,12) = 4321429105621118400 = 2⁶·3¹⁴·5²·7²·13²·19·37·97`
   * `R(5,12) = 4168195564669443267187500000000`
     `= 2⁸·3⁵·5¹⁴·7²·13²·17·31²·37·61·157·229`
   * `R(q,6)  = 0` for every `q` — `X² − q` and `X¹² − q⁶` share a root,
     so signature `6` yields no information at all. That is exactly why
     it is a separate leaf.

   Reading these off: for `s ∈ {4,8}` already `R(3,s)` has NO prime
   factor `> 19`, so `N ≤ 19`, contradicting `N ≥ 23`. For `s ∈ {0,12}`
   the primes `> 19` dividing `R(3,s)` are `{37, 97}` and those dividing
   `R(5,s)` are `{31,37,61,157,229}`; `N` divides both, and the
   intersection is `{37}`, which the hypothesis `N ≠ 37` excludes.
   (Note [MJ] prints `R(3,4) = R(3,8)`; the `3`-exponents actually differ,
   `3⁸` against `3¹²`. The conclusion — no prime factor `> 19` — is
   unaffected, and the value of `R(3,4)` printed there is correct.)

3. `mem_classNumberOnePrimes_of_isogenySignature_six` ([MJ, Prop 4.4]).
   Signature `6`: `λ = ψ·χ^{(N+1)/4}` with `ψ⁶ = 1`, and for `2 < q < N/4`
   the Hasse–Weil bound forces `q` INERT in `ℚ(√−N)`. Hence every ideal
   of norm below the Minkowski bound `2√N/π < N/4` is principal, so
   `ℚ(√−N)` has class number `1`; by Baker–Heegner–Stark and `N ≡ 3
   (mod 4)`, `N ∈ {3,7,11,19,43,67,163}`, so `N ≥ 23` leaves
   `{43,67,163}`. **The class-number-one theorem is a SECOND deep input,
   entirely disjoint from the Eisenstein ideal, and the old audit did not
   mention it.** Everything else here is Minkowski-bound algebraic number
   theory, which mathlib has.

FAITHFULNESS AUDIT of the exclusion list (2026-07-26, PARI/GP). The list
`{37,43,67,163}` is not folklore, it has a structure, and the structure
is exactly steps 2 and 3. `ellisomat` on curves with each of the thirteen
class-number-one CM `j`-invariants gives the rational prime isogeny
degrees of CM curves as `{2,3,7,11,19,43,67,163}` — the primes dividing a
class-number-one discriminant — whose members `≥ 23` are PRECISELY
`{43,67,163}`, i.e. the output of step 3. And `37` is non-CM: the two
non-cuspidal rational points of `X_0(37)` have `j = -9317` and
`j = -162677523113838677`, both confirmed to carry a rational 37-isogeny,
and `37` is the output of step 2. So `hN23` and `hNexc` are exactly right:
`19` is the largest prime below the excluded four, and nothing else `≥ 23`
can be added or removed.

CONSUMER-SHAPE FINDING, for whoever owns the cut rather than the leaves
(2026-07-26). Every path into this whole `X_0` cluster — `prime_…`,
`composite_…`, `mem_cyclicIsogenyDegrees` and Kenku's five nodes — runs
through `mem_cyclicIsogenyDegrees_of_addOrderOf`, which builds `g` as
`Affine.Point.baseChange` of a RATIONAL point. For such a `g` the
isogeny character is TRIVIAL: `σ g = g`, i.e. `lam = 1`. So the cluster
is stated on `X_0` but is only ever consumed on `X_1`, and an `X_1`-shaped
leaf (no rational point of prime order `≥ 23`) would be strictly weaker
than what is assumed here. That is a cut-level repair spanning
declarations this owner does not own, so it is reported, not made.
-/

/-- **The isogeny character makes `⟨g⟩` Galois-stable** (PROVEN
2026-07-27): the trivial converse of `exists_isogenyCharacter`.

If `σ` sends `g` to a multiple of `g` then it sends every multiple of `g`
to a multiple of `g`, since `Affine.Point.map` is additive. This exists
only to feed the elementary `hlam` phrasing used throughout this file
into `X0.lean`'s moduli-side interfaces, whose hypotheses are stated in
the `AddSubgroup.zmultiples` form (verbatim those of
`nonempty_gamma0Datum_of_stable`).

No hypothesis on `N` is needed: for `N = 0` the statement is still true
and still trivial, because it never inspects `ZMod.val` beyond using it
as some integer coefficient. -/
lemma WeierstrassCurve.stable_zmultiples_of_isogenyCharacter (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g) :
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈
          AddSubgroup.zmultiples g := by
  intro σ x hx
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [map_zsmul, hlam σ]
  exact AddSubgroup.zsmul_mem _
    (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) _) _


/-- **The admissible signatures, enumerated** (PROVEN 2026-07-26): if
`e ∈ {1, 2, 3, 4, 6}` is the ramification index over which `E` acquires
good reduction at `N`, `r` is Raynaud's exponent with `0 ≤ r ≤ e` and `r`
even whenever `e` is, and `s` is defined by `s·e = 12·r`, then
`s ∈ {0, 4, 6, 8, 12}`, and `s = 6` occurs for the single pair
`(e, r) = (4, 2)`.

This is the combinatorial half of `exists_isogenySignature`, separated
out so that the Serre–Raynaud local theory — the actual mathematical
input — is the only thing left sorried. The enumeration in full:

| `e` | admissible `r`  | `s = 12r/e`     |
|-----|-----------------|-----------------|
| `1` | `0, 1`          | `0, 12`         |
| `2` | `0, 2`          | `0, 12`         |
| `3` | `0, 1, 2, 3`    | `0, 4, 8, 12`   |
| `4` | `0, 2, 4`       | `0, 6, 12`      |
| `6` | `0, 2, 4, 6`    | `0, 4, 8, 12`   |

so `6` really does arise only at `(4, 2)` — which is what makes the
implication `s = 6 → N ≡ 3 (mod 4)` a statement about ONE local
situation rather than a case analysis. The parity constraint is what
does the work: without it `e = 4, r = 1` would give `s = 3` and `e = 2,
r = 1` would give `s = 6` from a second pair. -/
theorem mazurIsogeny_signatureEnumeration {e r s : ℕ}
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) (hre : r ≤ e)
    (hpar : e % 2 = 0 → r % 2 = 0) (hs : s * e = 12 * r) :
    (s = 0 ∨ s = 4 ∨ s = 6 ∨ s = 8 ∨ s = 12) ∧ (s = 6 → e = 4 ∧ r = 2) := by
  rcases he with rfl | rfl | rfl | rfl | rfl <;> interval_cases r <;> omega

/-! ##### The three-way cut of `exists_isogenyRamificationData`
(CARRIED OUT 2026-07-27, from the plan drafted in that leaf's docstring
the previous day)

The four leaves below plus ~20 lines of glue REPLACE the single sorry at
`exists_isogenyRamificationData`.  The split is the one its docstring
prescribed — local theory at `N`, unramifiedness away from `N`,
Minkowski globalization — with one correction and one addition, both
recorded here because they change what a successor should work on.

**CORRECTION to the drafted plan: leaf `C` must NOT be stated for an
abstract character.**  The plan already flagged this ("`C` REQUIRES
continuity of `ψ`"), and the fix it proposed — derive continuity in the
glue and pass it to `C` as a hypothesis — is available but strictly
worse here, because the derivation itself needs
`isOpen_setOf_galoisRep_eq_one`, which is declared ~27000 lines BELOW
this point (see the next paragraph).  So `C` is instead stated with the
CURVE data `g`, `hg`, `hlam` in hand.  Continuity is then not a
hypothesis at all: it is a consequence of `C`'s own inputs, since `lam`
factors through the continuous `E.galoisRep N` (if
`galoisRep N σ = galoisRep N τ` then `lam σ • g = lam τ • g`, and
`addOrderOf g = N` cancels `g`).  This keeps `C` TRUE as stated — the
abstract form is false, `Γ ℚ` not being topologically finitely generated,
so Nikolov–Segal does not apply and a discontinuous character trivial on
every inertia group is not excluded.

**DECLARATION-ORDER OBSTRUCTION — DISCHARGED 2026-07-27, and leaf `C` is
now PROVEN.**  `C` was never missing mathematics.  Its globalization
input, `minkowski_character_trivial`, was already proven IN THIS FILE,
~27000 lines BELOW this point, together with the ideal-to-inertia bridge
(`isUnramifiedAt_of_inertia_le_fixingSubgroup`,
`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`) that the
2026-07-27 MACHINERY AUDIT called "the only thing missing"; Lean has no
forward references, so none of it could be used here.

The fix was the mechanical one this note prescribed, in the variant it
recommended: the whole block — those three plus
`inertia_eq_bot_of_exists_prime_over`,
`inertia_eq_bot_of_le_fixingSubgroup`,
`open_normal_subgroup_eq_top_of_inertia_le` and
`isOpen_setOf_galoisRep_eq_one` — was hoisted VERBATIM (534 lines,
sorted-identical, no `namespace`/`section`/`variable`/`open` boundary
crossed) into the new upstream module
`Fermat.FLT.GaloisRepresentation.MinkowskiUnramified`, which this file
`public import`s.  Every downstream consumer — `InertiaCardTransport`,
`Family`, `ModThree`, `HermiteMinkowski`, `HilbertModularity`,
`Modularity/Interface` — resolves these names through `MazurTorsion`
exactly as before, unedited.

`C` then closed exactly as predicted: `ψ := λ¹²·χ^{-s}` has open kernel
because `ker lam ⊓ ker χ` is open and a subgroup containing an open
subgroup is open (`Subgroup.isOpen_mono`); `ψ` is trivial on every local
inertia image by hypothesis; `minkowski_character_trivial` finishes.
Openness of `ker lam` is where the curve data earns its place — see `C`'s
own docstring.

NOTE FOR ANYONE WORKING ABOVE THIS POINT: `isOpen_setOf_galoisRep_eq_one`
came along in the hoist, so it too is now usable HERE.  The alternative
formulation of `C` this note rejected — abstract character plus an
explicit continuity hypothesis, derived in the glue — is therefore no
longer blocked either.  It is still not worth switching to: `C` as stated
is true and proven, and the abstract form is FALSE without the continuity
hypothesis.

**ADDITION to the drafted plan: leaf `D`.**  The plan's glue assumed
"general-`ℓ` triviality of `χ` on inertia away from `N`" as though it
were available.  It is not: the only version in the tree,
`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup`
(`HardlyRamified/Threeadic.lean`), is hardcoded to `ℓ = 3` and lives
DOWNSTREAM of this module.  So it is stated here as its own leaf.

**`D` IS NOW PROVEN (2026-07-27)** — the `ℓ = 3` proof does transcribe,
but not by the route this note first drafted (`∏_{j<N}(1 - ζ^j) = N`,
then peel off a factor).  See `D`'s docstring and the ring-theoretic core
`rootOfUnity_index_eq_one_of_sub_mem_maximalIdeal`: the whole argument
runs in the RESIDUE FIELD and needs no product formula.

**SECOND CUT, 2026-07-27: `A` and `B` are now PROVEN GLUE, and the
Tate-curve content is FACTORED OUT.**  `A` and `B` each carried the same
Tate-curve description of the isogeny character at potentially
multiplicative reduction — `A` at `N`, `B` at `q ≠ N` — plus their own
distinct residue.  Both are now the reduction-type dichotomy
(`v(j) < 0` vs `v(j) ≥ 0`, Silverman *AEC* VII.5.5, the encoding this
file already uses in `potentiallyGoodReduction_of_isogenyCharacter`) over
three smaller leaves:

* `T` = `exists_isogenyTateExponent_of_padicValRat_j_neg` — the Tate
  curve, stated once, uniformly in the prime `v`, consumed by BOTH `A`
  and `B`.  What makes one statement serve both is `D`: at `v = q ≠ N`
  the `χ^(12r)` on its right-hand side collapses to `1`, at `v = N` it
  does not, and `D` is exactly that distinction.
* `A₀` = `exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg`
  — Serre's tame-inertia theory plus Raynaud's classification at `N`.
  Was the deep leaf of the cluster; **itself DECOMPOSED and PROVEN
  2026-07-27** over the three leaves `A₀-1`, `A₀-2`, `A₀-3` — see the
  section note directly above it, which also records that two of its five
  conclusion clauses turned out to be arithmetic consequences of the tame
  congruence rather than inputs from Raynaud.
* `B₀` = `isogenyCharacter_pow_twelve_eq_one_of_padicValRat_j_nonneg` —
  Néron–Ogg–Shafarevich at `q ≠ N`.  Its docstring carries a FAITHFULNESS
  correction to the old prose of `B`, which claimed the ramification
  index is always in `{1,2,3,4,6}`: that is the residue-characteristic
  `≥ 5` statement only, and at `q = 2, 3` the argument genuinely needs
  the stable line.
-/

/-! ##### The two-way cut of `T` (CARRIED OUT 2026-07-27)

`T` was one sorry carrying two quite different things: Tate's `v`-adic
uniformisation of a curve with potentially multiplicative reduction (hard
analysis and geometry, and the reason the leaf was called "the Tate curve"),
and the reading-off of the isogeny character from that uniformisation (group
theory in `Ωˣ/Qᶻ` plus the mod-`N` cyclotomic character).  They are now `T₁`
and `T₂` below, and `T` itself is PROVEN glue over them.

**STATUS UPDATE 2026-07-28: `T₂` is now PROVEN.**  The only leaf left in this
cut is `T₁` (`exists_tateParametrisation_of_padicValRat_j_neg`), i.e. Tate's
uniformisation itself.  `T₂` closed over one new auxiliary declaration,
`tateQuotient_dichotomy_of_intertwined_action` immediately above it, which
isolates the arithmetic-free group theory; the arithmetic input `T₂` supplies
to it is exactly two facts — that `Point.map` along `ℚ̄ → Ω` is injective and
equivariant (`Field.absoluteGaloisGroup.lift_map`), and that every `N`-th root
of unity of `Ω` is the image of one of `ℚ̄`, so that the mod-`N` cyclotomic
character of `Γ ℚ` computes the local action on them.

**What the cut buys, and why the intermediate statement is SHARPER than `T`.**
`T₂`'s conclusion is `λ = χ·ψ` or `λ = ψ` for the quadratic twisting character
`ψ` — the identity Serre actually states — rather than `λ¹² = χ^{12r}`.  The
twelfth power is then pure bookkeeping: `ψ` lands in `ℤˣ`, so `ψ² = 1` by
`Int.units_sq` and `ψ¹² = (ψ²)⁶ = 1`, which is what collapses the two cases to
`r = 1` and `r = 0`.  Keeping `ψ` explicit — rather than discarding it as the
old prose did — is also what keeps `T₂` TRUE without restricting to inertia:
see the faithfulness note on `T₂`.

**The machinery for `T₁` exists in this tree and should be reused.**
`Fermat.FLT.KnownIn1980s.EllipticCurves.TateSepClosure` is SORRY-FREE and
already proves the uniformisation `Ωˣ/q(E)ᶻ ≅ E(Ω)` Galois-equivariantly
(`WeierstrassCurve.exists_tateEquivSepClosure`) for a curve in minimal form
with SPLIT multiplicative reduction over a nonarchimedean local field.  The
instance package making `k = adicCompletion ℚ v` such a field is
`Fermat.FLT.Mathlib.NumberTheory.Padics.LocalField`
(`IsNonarchimedeanLocalField (HeightOneSpectrum.adicCompletion ℚ v)`), and
`Fermat.FLT.GaloisRepresentation.HardlyRamified.FreyConditions`'s
`exists_tame_quotient_of_nonsplit_padic_two` is a WORKED EXAMPLE of the whole
assembly at `ℚ_[2]`: quadratic twist to split reduction
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`), minimal model,
`exists_tateEquivSepClosure`, and the `±1`-twisted equivariance
(`quadraticTwistPointEquiv_galois`, `quadraticCharacter`).  So what `T₁` needs
beyond that example is exactly the step from POTENTIALLY multiplicative
(`v(j) < 0`) to multiplicative-after-a-quadratic-twist — Tate's criterion,
Silverman *ATAEC* V.5.3 — plus the change of local field from `ℚ_[v]` to
`adicCompletion ℚ v`.

**AVAILABILITY NOTE, established 2026-07-27 by `#check` in a scratch module
importing ONLY this one — not by reading the header, which is misleading
here.**  `TateSepClosure` does not appear in this file's import list, but it
IS in its transitive `public` cone (through `Semistable.lean`), and the
following are all in scope HERE, with no new import needed:

* `WeierstrassCurve.exists_tateEquivSepClosure`,
  `exists_rep_pow_eq_zpow_of_torsion`,
  `WeierstrassCurve.exists_tateTorsionQuotient`,
  `WeierstrassCurve.tate_inertia_unipotent` (`TateSepClosure.lean`);
* `algebraRatAlgClosureAdic`, `algClosureEmbeddingRat`, `algClosureSigmaRat`,
  `point_map_algClosureEmbeddingRat_comm` (`Semistable.lean`) — the adic
  analogue of the `ℚ_[q]` transport used by `FreyConditions.lean`, i.e.
  exactly the `ℚ̄ → Ω` plumbing `T₂` needs.

What was genuinely NOT in scope is
`WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction`:
`QuadraticTwists.SplitMultiplicativeReduction` was imported by this file with a
bare `import`, which is not re-exported.  **PROMOTED to `public import`
2026-07-28** (see the note on that import line), because `quadraticTwist` and
`Algebra.IsQuadraticExtension` occur in SIGNATURE position in `T₁a`/`T₁b₁`/`T₁b₂`
below.  That is a header change to a 52k-line module, so budget a full rebuild
of it and its `public import` consumers.
-/

/-- **The two `ℚ`-algebra structures on `Ω = Kᵥᵃˡᵍ` agree** (PROVEN
2026-07-27, and it is a TRAP worth one lemma): `Semistable.lean` installs the
tower structure `ℚ → Kᵥ → Ω` as the non-instance `algebraRatAlgClosureAdic`
and states all of its adic transport lemmas under `letI` with it, while the
ambient instance found by typeclass search — the one `T₁` and `T₂` below are
stated with, and the one `(E⁄(AlgebraicClosure ℚ)).Point` already uses — is
the `CharZero` `ℚ`-algebra structure.

The two are NOT definitionally equal (checked: `rfl` fails), so a proof of
`T₂` that reaches for `point_map_algClosureEmbeddingRat_comm` or
`algClosureSigmaRat` will hit a spurious instance mismatch.  They ARE equal,
for the reason that makes `ℚ` initial: a ring homomorphism out of `ℚ` into a
division ring is unique, so the two `algebraMap`s coincide and
`Algebra.algebra_ext` finishes.  Rewriting with this lemma is what lets the
two idioms be mixed. -/
theorem algebraRatAlgClosureAdic_eq_inst
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    algebraRatAlgClosureAdic v =
      (inferInstance :
        Algebra ℚ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  exact congrArg
    (fun f : ℚ →+* AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) => f r)
    (Subsingleton.elim _ _)

/-! ##### The two-way cut of `T₁` (CARRIED OUT 2026-07-28)

`T₁` was one sorry carrying two things that live in different worlds:
**Tate's criterion** — the reduction-type statement "`v(j) < 0` forces split
multiplicative reduction after at most one quadratic twist", which is
arithmetic geometry over the local field `Kᵥ` and knows nothing about `Ω` or
about Galois actions — and the **twist transport**, which is the plumbing that
turns that reduction-type conclusion into a `ψ`-twisted comparison of `Ω`-point
groups.  They are `T₁a` and `T₁b₁`/`T₁b₂` below, and `T₁` itself is now PROVEN glue
over them together with the sorry-free `TateSepClosure.lean`.

**Why the cut is at THIS seam.**  Everything the `Ω`-level assembly needs from
`v(j) < 0` is a curve over `Kᵥ` with SPLIT multiplicative reduction plus a way
back to `E`; and everything Tate's criterion produces is exactly that.  The
seam is therefore the reduction-type dichotomy, and it is stated in the shape
`exists_quadraticTwist_hasSplitMultiplicativeReduction` already speaks
(`(… ).minimal 𝒪[Kᵥ]` has split multiplicative reduction), so that the second
disjunct of `T₁a` and the conclusion of that PROVEN theorem are literally the
same proposition.

**The disjunction is not cosmetic and must NOT be collapsed to its second
disjunct.**  `exists_quadraticTwist_hasSplitMultiplicativeReduction`'s own
docstring records the reason: if `E` ALREADY has split multiplicative
reduction then *no* quadratic twist of it does — the unramified quadratic
twist is nonsplit multiplicative and every ramified quadratic twist is
additive.  So "some quadratic twist has split multiplicative reduction" is
FALSE precisely in the case one is most tempted to think of as trivial, and
the first disjunct is what covers it.

**Where the remaining depth is.**  `T₁a` is Tate's criterion (Silverman
*ATAEC* V.5.3, and *AEC* VII.5.5 for the `v(j) < 0` ⟺ potentially
multiplicative half); it was the genuinely new mathematics of this cluster.
**UPDATE 2026-07-28: `T₁a` is now DECOMPOSED and PROVEN** over the three-way
cut documented in the next section — `T₁a₁` (the `padicValRat`-to-valuation
bridge, PROVEN), `T₁a₂` (the twist classification at a fixed `j`, OPEN) and
`T₁a₃` (the Tate curve at a prescribed `j`, PROVEN).  Contrary to what this
paragraph used to say, most of what was needed WAS already in this project,
in `KnownIn1980s/EllipticCurves/TateCurve.lean`; only the twist
classification is genuinely new.  `T₁b₁` and `T₁b₂` are
transport, one per disjunct: no new mathematical content, but not one-liners
either.  **`T₁b₁` (the untwisted disjunct) is PROVEN.**  `T₁b₂` remains open
because the quadratic extension `L` produced by `T₁a` arrives as an abstract
field with no embedding into `Ω`, and `quadraticTwistPointEquiv` needs one
(`IsAlgClosed.lift`, exactly as `Semistable.lean` does it in
`torsionFlatPackage_of_unramified_quadraticTwist`).

**Note on why `T₁b₂` carries the quadratic character rather than `T₁a`.**
`ψ` is `quadraticCharacter Kᵥ L Ω` in the twisted branch and `1` in the
untwisted one; it is therefore a function of the CHOSEN embedding `L ↪ Ω`,
which does not exist yet at `T₁a`'s level.  Pushing `ψ` down into `T₁a` would
force that choice into the reduction-type statement, where it does not belong.
-/

/-! ##### The three-way cut of `T₁a` (CARRIED OUT 2026-07-28)

`T₁a` — Tate's criterion — was one sorry carrying three things that live in
different worlds, and none of the three mentions the other two:

* `T₁a₁`, **a valuation-theoretic fact about `ℚ` with no elliptic curves in
  it**: `padicValRat v x < 0` says exactly that `x` has valuation `> 1` in
  `Kᵥ = ℚ_v`.  This is the only place where `padicValRat` — the shape the
  whole `FreyCurve` tree phrases local hypotheses in — meets the
  `ValuativeRel` valuation the Tate-curve framework is written against.
* `T₁a₂`, **the twist classification of elliptic curves with a given
  `j`-invariant** (Silverman *AEC* X.5.4): over any field of characteristic
  zero, two elliptic curves with the same `j ∉ {0, 1728}` are quadratic twists
  of one another.  Pure algebra: no valuation, no reduction, no local field.
* `T₁a₃`, **the Tate curve at a prescribed `j`** (Silverman *ATAEC* V.5.2/V.5.3):
  for `|j| > 1` over a nonarchimedean local field, `E_{q(j)}` is elliptic with
  `j`-invariant `j`, and it has SPLIT MULTIPLICATIVE reduction.

**Why the cut is at THIS seam, and why it is not the reduction-type case
split the old docstring proposed.**  The obvious route — split on the
reduction type of `(E⁄Kᵥ).minimal` and dispatch the multiplicative case to
`exists_quadraticTwist_hasSplitMultiplicativeReduction` — needs *three*
separate arguments (good reduction excluded by `v(j) ≥ 0`; multiplicative
handled by the twist theorem; additive genuinely needing *ATAEC* V.5.3) and
still leaves the additive case as deep as the whole leaf.  The Tate route
handles all three cases at once, because `E_{q(j)}` is available from `v(j) < 0`
alone and knows nothing about the reduction type of `E`: `E` is a quadratic
twist of `E_{q(j)}` in every case, and the dichotomy "the twisting class is
trivial or it is not" IS the disjunction `T₁a` asserts.  Concretely, the
nonsplit-multiplicative case and the additive potentially-multiplicative case
are the unramified and the ramified twist respectively, and neither needs its
own argument.

**`T₁a₁` and `T₁a₃` are PROVEN below**, and `T₁a` itself is PROVEN glue over
the three.  `T₁a₂` — the twist classification — is the ONE remaining leaf of
this cut, and it is the only piece that is genuinely new mathematics.

**The disjunction is still not collapsible** — see the FAITHFULNESS NOTE on
`T₁a` — and the same warning now applies one level down, to `T₁a₂`: if `W₁ ≅ W₂`
over `k` then NO nontrivial quadratic twist of `W₂` is isomorphic to `W₁`
(`j ∉ {0, 1728}` makes `Aut = {±1}`, so the twists by distinct square classes
are pairwise non-isomorphic over `k`), and conversely.  Each disjunct of
`T₁a₂` is false exactly where the other one holds.
-/

open ValuativeRel IsDedekindDomain in
/-- **`T₁a₁` — `v(j) < 0` in valuation form** (PROVEN 2026-07-28; pure valuation
theory on `ℚ`, no elliptic curves): a rational number of negative `v`-adic
valuation has valuation `> 1` in the completion `Kᵥ`, for the `ValuativeRel`
valuation that the Tate-curve framework
(`Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurve`) is written against.

This is the *only* impedance mismatch in the `T₁` cluster: the `FreyCurve`
tree states its local hypotheses with `padicValRat`, while everything
downstream of `TateParameter.lean` is phrased with `ValuativeRel.valuation`.
Isolating it here keeps that translation out of the geometry.

Proof, and the point of it is that BOTH sides are `≤ 1`-conditions on the
DENOMINATOR, so no valuation is ever computed.

* Arithmetic side.  `padicValRat v x = padicValInt v x.num - padicValNat v x.den`
  by definition, and `padicValInt` is a `ℕ` cast; so if `v ∤ x.den` then
  `padicValNat v x.den = 0` (`padicValNat.eq_zero_of_not_dvd`) and the
  difference is `≥ 0`.  Contrapositive: `padicValRat v x < 0` forces
  `v ∣ x.den`.
* Valuation side.  The `ValuativeRel` valuation of `Kᵥ` is equivalent to
  `Valued.v` (`ValuativeRel.isEquiv`, with the `Compatible` instance
  `AdicCompletionRat.compatibleValuedAdicCompletionRat` from
  `Fermat/FLT/Mathlib/NumberTheory/Padics/LocalField.lean`), so
  `Valuation.IsEquiv.one_lt_iff_one_lt` moves the goal to `Valued.v`;
  `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`
  moves it down to `v.valuation ℚ x` on `ℚ` itself; and `Rat.valuation_le_one_iff_den`
  (mathlib, `RingTheory/DedekindDomain/AdicValuation.lean`) says
  `v.valuation ℚ x ≤ 1 ↔ (x.den : 𝓞 ℚ) ∉ v.asIdeal`.  Negating,
  `1 < v.valuation ℚ x ↔ (x.den : 𝓞 ℚ) ∈ v.asIdeal`, which
  `Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal` (PROVEN in
  `Fermat/FLT/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`) turns into
  `(v : ℤ) ∣ x.den`.

THE TRAP, and it cost a whole build cycle — worth recording because it will bite
anything else that mixes this project's adic machinery with mathlib's.  There
are TWO `Algebra ℚ (adicCompletion ℚ v)` instances in scope here.  This project
carries its own `Field` instance on the adic completion
(`HeightOneSpectrum.instFieldAdicCompletion_fermat`, in
`Fermat/FLT/DedekindDomain/AdicValuation.lean`), and through it
`DivisionRing.toRatAlgebra` wins typeclass search over mathlib's
`IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion`.  Which one a
given `algebraMap ℚ Kᵥ` elaborates to therefore depends on the IMPORT
ENVIRONMENT, and a proof that works in a small scratch can fail in a large
module for that reason alone.  The two are of course propositionally equal —
there is only one ring homomorphism `ℚ → Kᵥ` — but they are NOT defeq, and
unifying them drags the elaborator into trying to unfold
`HeightOneSpectrum.valuation`, which is `@[no_expose]` in mathlib and therefore
cannot be unfolded by anyone.  The symptom is a type mismatch whose two sides
pretty-print IDENTICALLY, with the tell-tale note
`definitions were not unfolded because their definition is not exposed:
HeightOneSpectrum.valuation`.

The fix is to stop relying on which instance is found: pin mathlib's instance
explicitly on the lemma's side, and bridge to whatever the ambient one is with
`Subsingleton.elim` on `ℚ →+* Kᵥ` (the same `ℚ`-initiality argument as
`algebraRatAlgClosureAdic_eq_inst` above).  That is what the `h2` block does,
and it is robust to the instance search changing again.

Second, smaller trap: `Rat.valuation_le_one_iff_den` lives in the `Rat`
namespace, not in `IsDedekindDomain.HeightOneSpectrum` where the neighbouring
lemmas are.

The obvious alternative route — through `Rat.HeightOneSpectrum.valuation_equiv_padicValuation`
and `Rat.padicValuation` — also works but is strictly longer, because it ends
up owing `(Rat.HeightOneSpectrum.primesEquiv hv.toHeightOneSpectrumRingOfIntegersRat : ℕ) = v`,
a `natGenerator` computation through `Rat.IsIntegralClosure.intEquiv`. -/
theorem one_lt_valuation_algebraMap_adicCompletionRat_of_padicValRat_neg
    {v : ℕ} (hv : v.Prime) {x : ℚ} (hx : padicValRat v x < 0) :
    1 < valuation (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) x) := by
  haveI : Fact v.Prime := ⟨hv⟩
  have hden : v ∣ x.den := by
    by_contra hnd
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hnd] at hx
    omega
  have h1 : (valuation (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) (WithZero (Multiplicative ℤ))) :=
    ValuativeRel.isEquiv _ _
  have h2 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) (WithZero (Multiplicative ℤ)))
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) x)
      = hv.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x := by
    have hml : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat) (WithZero (Multiplicative ℤ)))
        (@algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat) _ _
          (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
            (NumberField.RingOfIntegers ℚ) ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat) x)
        = hv.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
        hv.toHeightOneSpectrumRingOfIntegersRat x
    rw [show (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)) x
        = (@algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat) _ _
            (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
              (NumberField.RingOfIntegers ℚ) ℚ
              hv.toHeightOneSpectrumRingOfIntegersRat)) x from
      congrArg (fun f : ℚ →+* HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat => f x) (Subsingleton.elim _ _)]
    exact hml
  rw [h1.one_lt_iff_one_lt, h2,
    ← not_le, Rat.valuation_le_one_iff_den, not_not,
    hv.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal, map_natCast,
    Int.natCast_dvd_natCast]
  exact hden

/-- **Twisting commutes with a change of variables** (PROVEN 2026-07-28): the
quadratic twist by `(t, n)` of a curve moved by `C = ⟨u, r, s, t₀⟩` is the twist
of the original moved by the explicit change `⟨u, D·r, t·s, D·t·t₀⟩`, where
`D = t² - 4n`.

This is the companion of `exists_smul_quadraticTwistOf_eq`
(`QuadraticTwists.lean:263`), which instead varies the parameters `(t, n)`; it
belongs beside it and should be moved there when that file is next touched (it
is stated here only to keep this task inside its own file).

The witness is forced by the coordinates: over the quadratic extension the twist
is cut out by `X = D·x`, `Y = D·((t - 2θ)y - θ·(a₁x + a₃))`, so substituting
`x = u²x' + r`, `y = u³y' + u²s·x' + t₀` gives `X = u²X' + D·r` and
`Y = u³Y' + u²·(t·s)·X' + D·t·t₀` — note the `s`-entry picks up only `t`, not
`D·t`, because `X' = D·x'` already carries one factor of `D`. -/
theorem WeierstrassCurve.exists_smul_quadraticTwistOf_smul_eq {k : Type u} [Field k]
    (W : WeierstrassCurve k) (C : WeierstrassCurve.VariableChange k) (t n : k) :
    ∃ C' : WeierstrassCurve.VariableChange k,
      C' • W.quadraticTwistOf t n = (C • W).quadraticTwistOf t n := by
  refine ⟨⟨C.u, (t ^ 2 - 4 * n) * C.r, t * C.s, (t ^ 2 - 4 * n) * t * C.t⟩, ?_⟩
  simp only [WeierstrassCurve.variableChange_def]
  ext <;> simp only [WeierstrassCurve.quadraticTwistOf] <;> ring

/-- **`T₁a₂` — the twist classification at a fixed `j`** (PROVEN 2026-07-28;
Silverman
*AEC* X.5.4 and III.10.1(c), Prop. X.5.4 in the `j ≠ 0, 1728` case): over a
field of characteristic zero, two elliptic curves with the same `j`-invariant,
that `j` being neither `0` nor `1728`, are quadratic twists of one another —
either they are isomorphic over `k` outright, or there is a separable
quadratic extension `L/k` with `W₁ ≅ W₂ ⊗ L`.

FAITHFULNESS NOTE, and the reason for the disjunction — it is the same
phenomenon as in `T₁a` one level up, and a prover must not "simplify" either
one.  When `j ∉ {0, 1728}` the automorphism group of the curve is `{±1}`, so
the `k`-forms of `W₂` are classified by `H¹(Γ k, {±1}) = kˣ/(kˣ)²`; distinct
square classes give NON-isomorphic curves.  So the second disjunct is FALSE
exactly when the first one holds (a nontrivial twist is never isomorphic to
the curve itself), and the first is false whenever the twisting class is
nontrivial.  Neither disjunct alone is a theorem.

The hypotheses `hj0`/`hj1728` are not decoration: at `j = 0` the automorphism
group is `μ₆` and at `j = 1728` it is `μ₄`, so the forms are sextic resp.
quartic twists and the conclusion is false as stated (over `ℚ`, `y² = x³ + 1`
and `y² = x³ + 2` both have `j = 0` and are not quadratic twists).

ROUTE, and it is largely already written down in this project.
`WeierstrassCurve.exists_variableChange_of_j_eq_of_split`
(`Fermat/FLT/KnownIn1980s/EllipticCurves/TateCurve.lean:1172`) proves the
SPLIT-multiplicative special case, and everything in it up to its last five
lines is exactly this lemma's argument with `1 < valuation k j` in place of
`hj0`/`hj1728`: put both curves in short normal form `y² = x³ + Aᵢx + Bᵢ`
(characteristic zero, `exists_variableChange_isShortNF`), note `Aᵢ ≠ 0`
(else `j = 0`) and `Bᵢ ≠ 0` (else `j = 1728`), and read off from `j₁ = j₂`
the relation `A₁³B₂² = A₂³B₁²`, so that `w := B₂A₁/(B₁A₂)` satisfies
`A₂ = w²A₁` and `B₂ = w³B₁`.  That says precisely that the second short model
is the quadratic twist of the first by `w`
(`quadraticTwistOf 0 (-w/4)`, whose `D = t² - 4n` is `w`).  From there the two
disjuncts are the two cases of "is `w` a square in `k`":

* `w = e²`: the change of variables `⟨(Units.mk0 e _)⁻¹, 0, 0, 0⟩` carries the
  first short model to the second — this is verbatim the last five lines of
  `exists_variableChange_of_j_eq_of_split`, with its appeal to
  `isSquare_of_scaled_split` (which is where that theorem uses splitness, and
  is exactly what is NOT available here) replaced by the case hypothesis.
* `w` not a square: take `L := AdjoinRoot (X² - C w)`, a separable quadratic
  extension in characteristic zero (irreducibility from
  `X_pow_sub_C_irreducible_of_prime` at `p = 2`; separability is then FREE —
  `k` is perfect by `PerfectField.ofCharZero` and `L/k` is finite, so mathlib's
  `Algebra.IsSeparable` instance fires, and no `Separable` computation is
  needed), and `θ := AdjoinRoot.root`,
  whose minimal polynomial is `X² - w`, so `Algebra.trace k L θ = 0` and
  `Algebra.norm k L θ = -w` by `PowerBasis.trace_gen_eq_nextCoeff_minpoly` and
  `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`.  Hence
  `W₂.quadraticTwistBy θ = W₂.quadraticTwistOf 0 (-w)`, with `D = t² - 4n = 4w`.
  Applying that twist to the SHORT model `S₂ = ⟨0,0,0, w²A₁, w³B₁⟩` gives
  `⟨0,0,0, D²·w²A₁, D³·w³B₁⟩ = ⟨0,0,0, 16w⁴A₁, 64w⁶B₁⟩`, which is exactly the
  `u⁻¹ = 2w` rescaling of `S₁ = ⟨0,0,0,A₁,B₁⟩` — one twist, no second one.
  Convert `quadraticTwistBy θ` to `quadraticTwist L` by
  `exists_smul_quadraticTwist_eq_quadraticTwistBy`, and move the twist between
  `W₂` and its short model by `exists_smul_quadraticTwistOf_smul_eq` above.

(The earlier plan recorded here — twist the `w`-twist again by `4w` to reach the
square `4w²` — also works, but is a detour: the `(2w)`-rescaling above lands on
`S₁` directly.  Note also that the SQUARE case must be handled first and
separately: if `w` were a square then `X² - w` is reducible and `L` is not a
field at all.)

IMPORT TRAP, cost one build cycle on 2026-07-28: this project's own `AdjoinRoot`
helpers — `AdjoinRoot.finrank_eq_natDegree`,
`AdjoinRoot.isSeparable_of_separable`, `AdjoinRoot.root_notMem_range_algebraMap`
— are NOT visible from this module.  `Fermat.FLT.Mathlib.RingTheory.AdjoinRoot`
is in this file's textual import closure but only through NON-`public` imports,
and under the module system a plain `import` does not re-export, so the
constants are genuinely unknown here.  A source-level BFS over `import` lines
will say they are available and be wrong; only `public import` chains carry
visibility.  All three are inlined above from mathlib (`PowerBasis.finrank`,
the `PerfectField` instance, `minpoly.eq_X_sub_C`) rather than imported. -/
theorem WeierstrassCurve.exists_variableChange_or_exists_quadraticTwist_of_j_eq
    {k : Type u} [Field k] [CharZero k]
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    (hj : W₁.j = W₂.j) (hj0 : W₁.j ≠ 0) (hj1728 : W₁.j ≠ 1728) :
    (∃ C : WeierstrassCurve.VariableChange k, C • W₁ = W₂) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
        (_ : Algebra.IsQuadraticExtension k L) (_ : Algebra.IsSeparable k L)
        (C : WeierstrassCurve.VariableChange k), C • W₁ = W₂.quadraticTwist L := by
  haveI h2 : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  haveI h3 : Invertible (3 : k) := invertibleOfNonzero (by norm_num : (3 : k) ≠ 0)
  obtain ⟨C₁, hC₁⟩ := W₁.exists_variableChange_isShortNF
  obtain ⟨C₂, hC₂⟩ := W₂.exists_variableChange_isShortNF
  -- the short models have the same `j`, still avoiding `0` and `1728`
  have hj' : (C₁ • W₁).j = (C₂ • W₂).j := by
    rw [WeierstrassCurve.variableChange_j, WeierstrassCurve.variableChange_j, hj]
  have hj₁0 : (C₁ • W₁).j ≠ 0 := by rw [WeierstrassCurve.variableChange_j]; exact hj0
  have hj₁1728 : (C₁ • W₁).j ≠ 1728 := by rw [WeierstrassCurve.variableChange_j]; exact hj1728
  have hj₂0 : (C₂ • W₂).j ≠ 0 := by rw [← hj']; exact hj₁0
  have hj₂1728 : (C₂ • W₂).j ≠ 1728 := by rw [← hj']; exact hj₁1728
  set A₁ := (C₁ • W₁).a₄ with hA₁def
  set B₁ := (C₁ • W₁).a₆ with hB₁def
  set A₂ := (C₂ • W₂).a₄ with hA₂def
  set B₂ := (C₂ • W₂).a₆ with hB₂def
  have hΔ : ∀ (W : WeierstrassCurve k) [W.IsElliptic], W.Δ ≠ 0 := fun W _ ↦ W.isUnit_Δ.ne_zero
  have hjeq : ∀ (W : WeierstrassCurve k) [W.IsElliptic],
      W.j = (W.Δ)⁻¹ * W.c₄ ^ 3 := by
    intro W _
    rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl,
      Units.val_inv_eq_inv_val, W.coe_Δ']
  -- `Aᵢ ≠ 0`: otherwise `c₄ = -48Aᵢ = 0`, so `j = 0`
  have hA0 : ∀ (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF],
      W.j ≠ 0 → W.a₄ ≠ 0 := by
    intro W _ _ hjne h0
    exact hjne (by
      rw [hjeq W, W.c₄_of_isShortNF, h0, mul_zero, zero_pow (by norm_num), mul_zero])
  have hA₁0 : A₁ ≠ 0 := hA0 (C₁ • W₁) hj₁0
  have hA₂0 : A₂ ≠ 0 := hA0 (C₂ • W₂) hj₂0
  -- `Bᵢ ≠ 0`: otherwise `j = 1728`
  have hB0 : ∀ (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF],
      W.j ≠ 1728 → W.a₄ ≠ 0 → W.a₆ ≠ 0 := by
    intro W _ _ hjne hA h0
    refine hjne ?_
    have hΔW : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := W.Δ_of_isShortNF
    rw [hjeq W, W.c₄_of_isShortNF, hΔW, h0]
    field_simp
    ring
  have hB₁0 : B₁ ≠ 0 := hB0 (C₁ • W₁) hj₁1728 hA₁0
  have hB₂0 : B₂ ≠ 0 := hB0 (C₂ • W₂) hj₂1728 hA₂0
  -- the cross-multiplied `j`-equation
  have hcross : (C₁ • W₁).c₄ ^ 3 * (C₂ • W₂).Δ =
      (C₂ • W₂).c₄ ^ 3 * (C₁ • W₁).Δ := by
    have h1 := hjeq (C₁ • W₁)
    have h2 := hjeq (C₂ • W₂)
    rw [h1, h2, inv_mul_eq_div, inv_mul_eq_div,
      div_eq_div_iff (hΔ (C₁ • W₁)) (hΔ (C₂ • W₂))] at hj'
    exact hj'
  -- the fundamental relation `A₁³B₂² = A₂³B₁²`
  have hkey : A₁ ^ 3 * B₂ ^ 2 = A₂ ^ 3 * B₁ ^ 2 := by
    rw [(C₁ • W₁).c₄_of_isShortNF, (C₂ • W₂).c₄_of_isShortNF,
      (C₁ • W₁).Δ_of_isShortNF, (C₂ • W₂).Δ_of_isShortNF,
      ← hA₁def, ← hB₁def, ← hA₂def, ← hB₂def] at hcross
    have h27 : ((27 : k) * ((-48 : k) ^ 3 * (-16 : k))) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h27
    linear_combination hcross
  -- the twisting scalar
  set w := (B₂ * A₁) / (B₁ * A₂) with hwdef
  have hw0 : w ≠ 0 :=
    div_ne_zero (mul_ne_zero hB₂0 hA₁0) (mul_ne_zero hB₁0 hA₂0)
  have hA₂w : A₂ = w ^ 2 * A₁ := by
    rw [hwdef, div_pow, div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero 2 (mul_ne_zero hB₁0 hA₂0))]
    linear_combination -hkey
  have hB₂w : B₂ = w ^ 3 * B₁ := by
    rw [hwdef, div_pow, div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero 3 (mul_ne_zero hB₁0 hA₂0))]
    linear_combination -B₁ * B₂ * hkey
  -- identify the two short models with explicit quintuples
  have hS₁eq : (C₁ • W₁) = (⟨0, 0, 0, A₁, B₁⟩ : WeierstrassCurve k) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · exact (C₁ • W₁).a₁_of_isShortNF
    · exact (C₁ • W₁).a₂_of_isShortNF
    · exact (C₁ • W₁).a₃_of_isShortNF
    · rfl
    · rfl
  have hS₂eq : (C₂ • W₂) =
      (⟨0, 0, 0, w ^ 2 * A₁, w ^ 3 * B₁⟩ : WeierstrassCurve k) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · exact (C₂ • W₂).a₁_of_isShortNF
    · exact (C₂ • W₂).a₂_of_isShortNF
    · exact (C₂ • W₂).a₃_of_isShortNF
    · exact hA₂w
    · exact hB₂w
  by_cases hsq : IsSquare w
  · -- `w = v²`: scaling by `v⁻¹` is a change of variables over `k` itself
    left
    obtain ⟨v, hv⟩ := hsq
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hw0 (by rw [hv, mul_zero])
    set Cv : WeierstrassCurve.VariableChange k := ⟨(Units.mk0 v hv0)⁻¹, 0, 0, 0⟩ with hCvdef
    have hCv : Cv • (C₁ • W₁) = C₂ • W₂ := by
      rw [hS₁eq, hS₂eq]
      refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
        simp only [WeierstrassCurve.variableChange_def, hCvdef, hv, inv_inv,
          Units.val_mk0] <;>
        field_simp <;>
        ring
    exact ⟨C₂⁻¹ * (Cv * C₁), by rw [mul_smul, mul_smul, hCv, inv_smul_smul]⟩
  · -- `w` is not a square: `W₁` is the twist of `W₂` by `L = k(√w)`
    right
    have hnr : ∀ b : k, b ^ 2 ≠ w := fun b hb ↦ hsq ⟨b, by rw [← hb]; ring⟩
    have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C w) :=
      X_pow_sub_C_irreducible_of_prime Nat.prime_two hnr
    haveI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C w)) := ⟨hirr⟩
    have hmon : (Polynomial.X ^ 2 - Polynomial.C w).Monic :=
      Polynomial.monic_X_pow_sub_C w two_ne_zero
    have hne0 : (Polynomial.X ^ 2 - Polynomial.C w) ≠ 0 := hmon.ne_zero
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C w).natDegree = 2 :=
      Polynomial.natDegree_X_pow_sub_C
    haveI hfin : Module.Finite k (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C w)) :=
      (AdjoinRoot.powerBasis hne0).finite
    haveI hquad : Algebra.IsQuadraticExtension k
        (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C w)) :=
      ⟨by rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne0), AdjoinRoot.powerBasis_dim, hdeg]⟩
    -- separability is free in characteristic zero: `k` is perfect and `L/k` is finite
    haveI hsep : Algebra.IsSeparable k
        (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C w)) := inferInstance
    set L := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C w) with hLdef
    set θ : L := AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C w) with hθdef
    -- the minimal polynomial of `θ` is `X² - w`, so `tr θ = 0` and `N θ = -w`
    have hpbgen : (AdjoinRoot.powerBasis hne0).gen = θ := AdjoinRoot.powerBasis_gen hne0
    have hminp : minpoly k θ = Polynomial.X ^ 2 - Polynomial.C w := by
      rw [← hpbgen]
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon
    have hθ : θ ∉ Set.range (algebraMap k L) := by
      rintro ⟨c, hc⟩
      have h : (minpoly k θ).natDegree = 2 := by rw [hminp, hdeg]
      rw [← hc, minpoly.eq_X_sub_C, Polynomial.natDegree_X_sub_C] at h
      omega
    have htr : Algebra.trace k L θ = 0 := by
      rw [← hpbgen, PowerBasis.trace_gen_eq_nextCoeff_minpoly, hpbgen, hminp]
      simp [Polynomial.nextCoeff, hdeg]
    have hnm : Algebra.norm k θ = -w := by
      rw [← hpbgen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hpbgen, hminp,
        AdjoinRoot.powerBasis_dim, hdeg]
      simp
    have htwistBy : W₂.quadraticTwistBy θ = W₂.quadraticTwistOf 0 (-w) := by
      rw [WeierstrassCurve.quadraticTwistBy, htr, hnm]
    obtain ⟨C'', hC''⟩ := W₂.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
    obtain ⟨C', hC'⟩ := W₂.exists_smul_quadraticTwistOf_smul_eq C₂ 0 (-w)
    -- the twist of `S₂` by `(0, -w)` is the `(2w)`-rescaling of `S₁`
    have hw2 : (2 : k) * w ≠ 0 := mul_ne_zero two_ne_zero hw0
    set Cu : WeierstrassCurve.VariableChange k := ⟨(Units.mk0 (2 * w) hw2)⁻¹, 0, 0, 0⟩ with hCudef
    have hCu : Cu • (C₁ • W₁) = (C₂ • W₂).quadraticTwistOf 0 (-w) := by
      rw [hS₁eq, hS₂eq]
      refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
        simp only [WeierstrassCurve.variableChange_def, WeierstrassCurve.quadraticTwistOf,
          hCudef, inv_inv, Units.val_mk0] <;>
        ring
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      (C' * C'')⁻¹ * (Cu * C₁), ?_⟩
    have hchain : (C' * C'') • W₂.quadraticTwist L = (Cu * C₁) • W₁ := by
      rw [mul_smul, hC'', htwistBy, hC', ← hCu, mul_smul]
    rw [mul_smul, ← hchain, inv_smul_smul]

open ValuativeRel in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **`T₁a₃` — the Tate curve at a prescribed `j`** (PROVEN 2026-07-28;
Silverman *ATAEC* V.5.2): over a nonarchimedean local field, if `|j| > 1` then
the Tate curve of the Tate parameter `q(j)` is elliptic with `j`-invariant
exactly `j`.

This is `WeierstrassCurve.isElliptic_tateCurve_and_j`
(`TateCurve.lean:770`) with its hypotheses weakened to what its proof actually
uses.  That statement is about `E.q = tateParameter E.j` for a curve `E` which
is ASSUMED to have split multiplicative reduction, and the assumption enters
its proof at exactly one point, through `E.one_lt_valuation_j`; every other
step is about the bare element `E.j`.  Here the curve is gone and `1 < |j|` is
the hypothesis, which is what the `T₁a` assembly can supply — it knows
`v(j) < 0` and has no curve with split multiplicative reduction in hand (that
is what it is trying to produce).

Proof (transcribed from `isElliptic_tateCurve_and_j`, whose two `set_option`s
are carried across with it because the same series computations need them):
`Δ(E_q) = Δ̂(q)` has valuation `|q| ≠ 0` by the leading-coefficient lemma
`TateCurve.valuation_evalInt_eq`, so `E_q` is elliptic; then
`ĵ⁻¹(q) = j(E_q)⁻¹` by the `c₄`- and `Δ`-evaluations, while
`ĵ⁻¹(q) = ĵ⁻¹(ĵ⁻¹⁻¹(j⁻¹)) = j⁻¹` because `tateParameter j` is by definition
the evaluation at `j⁻¹` of the compositional inverse of `ĵ⁻¹`
(`TateCurve.jInv_subst_jInvReverse`, `TateCurve.evalInt_subst`).  Inverting
gives `j(E_q) = j`.

FOLLOW-UP (not done here, to keep this task inside its own file): once this
lands, `TateCurve.lean`'s `isElliptic_tateCurve_and_j` should be re-derived
from it in one line, `fun => this E.one_lt_valuation_j`, and the duplicated
proof deleted. -/
theorem WeierstrassCurve.isElliptic_tateCurve_tateParameter_and_j
    {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {j : k} (hj : 1 < valuation k j) :
    ∃ _ : (WeierstrassCurve.tateCurve (WeierstrassCurve.tateParameter j)).IsElliptic,
      (WeierstrassCurve.tateCurve (WeierstrassCurve.tateParameter j)).j = j := by
  set q : k := WeierstrassCurve.tateParameter j with hqdef0
  have hq0 : q ≠ 0 := WeierstrassCurve.tateParameter_ne_zero hj
  have hq : valuation k q < 1 := WeierstrassCurve.valuation_tateParameter_lt_one hj
  have hΔ : (WeierstrassCurve.tateCurve q).Δ = TateCurve.evalInt q TateCurve.ΔFormal :=
    WeierstrassCurve.Δ_tateCurve_eq_evalInt q hq
  have hvΔ : valuation k ((WeierstrassCurve.tateCurve q).Δ) = valuation k q := by
    rw [hΔ]
    exact TateCurve.valuation_evalInt_eq q hq0 hq
      TateCurve.constantCoeff_ΔFormal TateCurve.coeff_one_ΔFormal
  have hΔne : (WeierstrassCurve.tateCurve q).Δ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvΔ
    exact hq0 ((valuation k).zero_iff.mp hvΔ.symm)
  haveI hell : (WeierstrassCurve.tateCurve q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔne⟩
  refine ⟨hell, ?_⟩
  have hcc₄3 : PowerSeries.constantCoeff (TateCurve.c₄Formal ^ 3) = 1 := by
    rw [map_pow, TateCurve.constantCoeff_c₄Formal, one_pow]
  have hjinv : TateCurve.evalInt q TateCurve.jInv =
      ((WeierstrassCurve.tateCurve q).j)⁻¹ := by
    rw [TateCurve.jInv, TateCurve.evalInt_mul q hq,
      TateCurve.evalInt_invOfUnit q hq _ hcc₄3,
      TateCurve.evalInt_pow q hq, ← WeierstrassCurve.c₄_tateCurve_eq_evalInt q hq, ← hΔ]
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
      (WeierstrassCurve.tateCurve q).coe_Δ']
    rw [mul_inv, inv_inv]
  have hvjinv : valuation k j⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hj
  have hcomp : TateCurve.evalInt q TateCurve.jInv = j⁻¹ := by
    have hqdef : q = TateCurve.evalInt j⁻¹ TateCurve.jInvReverse :=
      hqdef0.trans WeierstrassCurve.tateParameter_eq
    rw [hqdef, ← TateCurve.evalInt_subst j⁻¹ hvjinv _ _
      TateCurve.constantCoeff_jInvReverse,
      TateCurve.jInv_subst_jInvReverse, TateCurve.evalInt_X]
  exact inv_injective (by rw [← hjinv, hcomp])

open ValuativeRel in
/-- **`T₁a` over a general nonarchimedean local field** (PROVEN 2026-07-28
from `T₁a₂` and `T₁a₃`; Silverman *ATAEC* V.5.3): over a nonarchimedean local
field `k` of characteristic zero, an elliptic curve whose `j`-invariant has
`|j| > 1` acquires SPLIT MULTIPLICATIVE reduction after at most one quadratic
twist.  This is `T₁a` with the arithmetic of `ℚ` stripped out; `T₁a` itself is
this statement at `k = Kᵥ` together with `T₁a₁`.

FAITHFULNESS NOTE: the disjunction is the one `T₁a` carries and is not
collapsible in either direction — see `T₁a`'s own note and `T₁a₂`'s.

Proof.  Let `T := E_{q(j(W))}` be the Tate curve of the Tate parameter of
`j(W)`.  `T₁a₃` says `T` is elliptic with `j(T) = j(W)`, and
`hasSplitMultiplicativeReduction_tateCurve` (PROVEN in `TateCurve.lean`) says
`T` has split multiplicative reduction, since
`valuation_tateParameter_lt_one` puts `q(j(W))` in the punctured open unit
disc.  Now `j(T) = j(W)` has valuation `> 1`, so it is neither `0` nor `1728`
— both of those have valuation `≤ 1`, the second by `valuation_intCast_le_one`
— and `T₁a₂` applies to the pair `(T, W)`.  Its two cases are the two
disjuncts: in each, `W` (respectively `W ⊗ L`) is `C • T` for a change of
variables `C` over `k`, and
`WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_smul` (PROVEN in
`TateCurve.lean`, Silverman VII.1.3(b)) transports split multiplicativity from
`T` to the minimal model of `C • T`.

Note where the twist actually comes from: `T₁a₂` produces `L` from the square
class of a scalar attached to `W`, and NOT from the reduction type of `W`.  So
the nonsplit-multiplicative case (unramified `L`) and the additive
potentially-multiplicative case (ramified `L`) are handled by one and the same
line, which is what makes this route shorter than the reduction-type case
split. -/
theorem WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_or_exists_quadraticTwist_of_one_lt_valuation_j
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k]
    (W : WeierstrassCurve k) [W.IsElliptic] (hj : 1 < valuation k W.j) :
    (W.minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] ∨
      ∃ (L : Type) (_ : Field L) (_ : Algebra k L)
        (_ : Algebra.IsQuadraticExtension k L) (_ : Algebra.IsSeparable k L),
        ((W.quadraticTwist L).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] := by
  set T : WeierstrassCurve k :=
    WeierstrassCurve.tateCurve (WeierstrassCurve.tateParameter W.j) with hTdef
  obtain ⟨hTell, hTj⟩ :=
    WeierstrassCurve.isElliptic_tateCurve_tateParameter_and_j (j := W.j) hj
  haveI : T.IsElliptic := hTell
  haveI hTsplit : T.HasSplitMultiplicativeReduction 𝒪[k] :=
    WeierstrassCurve.hasSplitMultiplicativeReduction_tateCurve _
      (WeierstrassCurve.valuation_tateParameter_lt_one hj)
  have hj0 : T.j ≠ 0 := by
    rw [hTj]
    intro h0
    rw [h0, map_zero] at hj
    exact absurd hj (not_lt.mpr zero_le_one)
  have hj1728 : T.j ≠ 1728 := by
    rw [hTj]
    intro h0
    rw [h0, show ((1728 : k)) = ((1728 : ℤ) : k) by norm_num] at hj
    exact absurd (lt_of_lt_of_le hj (valuation_intCast_le_one 1728)) (lt_irrefl _)
  rcases WeierstrassCurve.exists_variableChange_or_exists_quadraticTwist_of_j_eq
      T W hTj hj0 hj1728 with
    ⟨C, hC⟩ | ⟨L, hLfield, hLalg, hLquad, hLsep, C, hC⟩
  · refine Or.inl ?_
    rw [← hC]
    exact WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_smul T C
  · refine Or.inr ⟨L, hLfield, hLalg, hLquad, hLsep, ?_⟩
    rw [← hC]
    exact WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_smul T C

open ValuativeRel IsDedekindDomain in
/-- **`T₁a` — Tate's criterion, in reduction-type form** (DECOMPOSED and PROVEN
2026-07-28 from `T₁a₁`, `T₁a₂` and `T₁a₃` above;
Silverman *ATAEC* V.5.3 and *AEC* VII.5.5; Tate's 1959 notes): at a prime `v`
with `v(j) < 0` the base change of `E` to `Kᵥ = ℚ_vˆ` has SPLIT MULTIPLICATIVE
reduction after AT MOST ONE quadratic twist — either its own minimal model
already does, or the minimal model of its twist by some separable quadratic
`L/Kᵥ` does.

This is the whole of the new arithmetic geometry in the `T₁` cluster.  The
classical statement is in two halves.  First (*AEC* VII.5.5): `v(j) < 0` if
and only if `E` has POTENTIALLY multiplicative reduction, i.e. acquires
multiplicative reduction over a finite extension.  Second (*ATAEC* V.5.3): in
that case `E` is, over `Kᵥ`, the twist of a Tate curve `E_Q` by a UNIQUE
character `Γ Kᵥ → {±1}`; a character of order dividing `2` is either trivial —
first disjunct, `E` itself is already split multiplicative — or cuts out a
quadratic extension `L/Kᵥ`, and then `E ⊗ L` is the twist, which is the second
disjunct.  Separability of `L` is automatic in characteristic `0`.

FAITHFULNESS NOTE, and the reason for the disjunction.  The second disjunct
ALONE would be FALSE: `exists_quadraticTwist_hasSplitMultiplicativeReduction`
records that when `E` already has split multiplicative reduction, no quadratic
twist of it has — the unramified twist is nonsplit multiplicative, the
ramified ones are additive.  So a prover must not "simplify" this statement by
dropping the left disjunct.  Conversely the first disjunct alone is false at
any `E` with additive potentially-multiplicative reduction (a ramified twist
is then genuinely needed), which is exactly the case that makes `ψ` ramified
downstream and is why `T₁`'s twist cannot be discarded.

Proof, now formalised, and it is three lines over the cut above.
`WeierstrassCurve.map_j` turns the `j`-invariant of the base change into the
image of `j(E)`; `T₁a₁` turns `padicValRat v (j E) < 0` into
`1 < |j(E⁄Kᵥ)|`; and the general local statement
`hasSplitMultiplicativeReduction_minimal_or_exists_quadraticTwist_of_one_lt_valuation_j`
(PROVEN above from `T₁a₂` and `T₁a₃`) is the conclusion.  `CharZero Kᵥ` comes
from injectivity of `algebraMap ℚ Kᵥ`.

A NOTE ON THE ROUTE, because the paragraph this replaces recommended a
different one and it is worth saying why it was not taken.  The old plan was
to case on the reduction type of `(E⁄Kᵥ).minimal` — good reduction excluded by
integrality of `j`, multiplicative reduction handled by
`exists_quadraticTwist_hasSplitMultiplicativeReduction`, additive reduction
left to *ATAEC* V.5.3.  That plan is correct, but it pays for the split: the
additive branch still needs the whole Tate comparison, and the other two
branches need their own arguments on top.  The route actually taken builds the
Tate curve `E_{q(j)}` from `v(j) < 0` alone — which is all *ATAEC* V.5.2 needs —
and gets all three reduction types from the single observation that `E⁄Kᵥ` and
`E_{q(j)}` have the same `j`-invariant, hence are quadratic twists.  The
reduction type of `E` never has to be named. -/
theorem WeierstrassCurve.hasSplitMultiplicativeReduction_or_exists_quadraticTwist_of_padicValRat_j_neg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {v : ℕ} (hv : v.Prime) (hj : padicValRat v E.j < 0) :
    ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))).minimal
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat]).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat] ∨
    ∃ (L : Type) (_ : Field L)
      (_ : Algebra (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) L)
      (_ : Algebra.IsQuadraticExtension (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) L)
      (_ : Algebra.IsSeparable (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) L),
      (((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))).quadraticTwist L).minimal
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat]).HasSplitMultiplicativeReduction
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat] := by
  haveI : CharZero (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)).injective
  refine WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_or_exists_quadraticTwist_of_one_lt_valuation_j
    _ ?_
  rw [WeierstrassCurve.map_j]
  exact one_lt_valuation_algebraMap_adicCompletionRat_of_padicValRat_neg hv hj

set_option maxHeartbeats 1000000 in
open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
/-- **`T₁b₁` — the twist transport, UNTWISTED branch** (PROVEN 2026-07-28):
when `E⁄Kᵥ` already has split multiplicative reduction — the first disjunct of
`T₁a` — the model `X` demanded by `T₁` is just its minimal model, the
character `ψ` is trivial, and `φ` is the minimal-model change of variables.

Proof.  `X := C • (E⁄Kᵥ)` with `C := ((E⁄Kᵥ).exists_isMinimal 𝒪[Kᵥ]).choose`,
so `X` IS `(E⁄Kᵥ).minimal 𝒪[Kᵥ]` by definitional unfolding and `hsplit`
transfers verbatim.  `φ` is
`Affine.Point.equivVariableChangeBaseChange (E⁄Kᵥ) C Ω` followed by
`Affine.Point.equivOfEq` for `(E⁄Kᵥ)⁄Ω = E⁄Ω`.  That last equality is where
the two towers meet, and it holds for the reason that makes `ℚ` initial: after
`WeierstrassCurve.map_map` the two sides are `E.map` of two ring
homomorphisms `ℚ → Ω`, and `Subsingleton.elim` identifies them — the same
argument as `algebraRatAlgClosureAdic_eq_inst` above, in its `map` guise.
Equivariance is `equivVariableChangeBaseChange_galois` (a base-changed
variable change is `Kᵥ`-rational, hence fixed by every `σ ∈ Γ Kᵥ`) together
with a two-case `Point.map`/`equivOfEq` transport; the `restrictScalars ℚ` on
the `E`-side map is invisible to it, both sides being the same function of `Ω`.

Note the `HasSplitMultiplicativeReduction` hypothesis is stated on
`(E⁄Kᵥ).minimal 𝒪[Kᵥ]` rather than on `E⁄Kᵥ` itself: mathlib's reduction-type
classes all extend `IsMinimal`, so the predicate is only ever asserted of a
minimal model. -/
theorem WeierstrassCurve.exists_splitModel_quadraticCharacter_pointEquiv_of_hasSplitMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {v : ℕ} (hv : v.Prime)
    (hsplit :
      ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))).minimal
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat]).HasSplitMultiplicativeReduction
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat]) :
    ∃ (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))
      (_ : X.IsElliptic)
      (_ : X.HasSplitMultiplicativeReduction
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat])
      (ψ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) →* ℤˣ)
      (φ : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point ≃+
        ((E⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point),
      ∀ (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))
        (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point),
        WeierstrassCurve.Affine.Point.map (W' := E)
            ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ) (φ P) =
          ((ψ σ : ℤ)) • φ (WeierstrassCurve.Affine.Point.map (W' := X)
            ((σ : _ ≃ₐ[_] _).toAlgHom) P) := by
  classical
  set W : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) :=
    E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) with hWdef
  set C : WeierstrassCurve.VariableChange (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) :=
    (W.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat]).choose with hCdef
  haveI hWell : W.IsElliptic := by
    rw [hWdef]; exact inferInstanceAs (E.map (algebraMap ℚ _)).IsElliptic
  -- `W⁄Ω = E⁄Ω`: the two ring homomorphisms `ℚ → Ω` agree because `ℚ` is initial
  have hbase : (W⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))) =
      (E⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))) := by
    show W.map (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) _) = E.map (algebraMap ℚ _)
    rw [hWdef, WeierstrassCurve.map_map]
    congr 1
  refine ⟨C • W, inferInstanceAs ((C • W).IsElliptic), hsplit, 1,
    (WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange W C
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))).trans
      (WeierstrassCurve.Affine.Point.equivOfEq hbase), ?_⟩
  -- transporting `Point.map` across the curve identification `W⁄Ω = E⁄Ω`
  have key : ∀ R : (W⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))).Point,
      ∀ σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat),
      WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ)
          (WeierstrassCurve.Affine.Point.equivOfEq hbase R) =
        WeierstrassCurve.Affine.Point.equivOfEq hbase
          (WeierstrassCurve.Affine.Point.map (W' := W) ((σ : _ ≃ₐ[_] _).toAlgHom) R) := by
    intro R σ
    cases R with
    | zero =>
      simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero]
    | some x y hns =>
      rw [WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.equivOfEq_some]
      rfl
  intro σ P
  have hg := WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange_galois W C
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) (σ : _ ≃ₐ[_] _) P
  show WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ)
      (WeierstrassCurve.Affine.Point.equivOfEq hbase
        (WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange W C _ P)) =
    ((1 : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) →* ℤˣ) σ : ℤ) •
      WeierstrassCurve.Affine.Point.equivOfEq hbase
        (WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange W C _
          (WeierstrassCurve.Affine.Point.map (W' := C • W) ((σ : _ ≃ₐ[_] _).toAlgHom) P))
  rw [key, hg, MonoidHom.one_apply, Units.val_one, one_zsmul]

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
/-- **`T₁b₂` — the twist transport, TWISTED branch** (PROVEN 2026-07-28; pure
plumbing over `quadraticTwistPointEquiv_galois`): the second disjunct of
`T₁a`, where the quadratic extension `L/Kᵥ` is genuinely needed.

This is where `T₁`'s twist is manufactured, and it is the only place in the
whole cluster where an EMBEDDING of `L` into `Ω` has to be chosen — which is
exactly why it could not be pushed into `T₁a`, whose statement is about
reduction types over `Kᵥ` alone.

Proof.  Fix `ι : L →ₐ[Kᵥ] Ω` by `IsAlgClosed.lift` and
install `Algebra L Ω` / `IsScalarTower Kᵥ L Ω` along it — verbatim the step
`Semistable.lean` performs in
`torsionFlatPackage_of_unramified_quadraticTwist`.  Take
`X := ((E⁄Kᵥ).quadraticTwist L).minimal 𝒪[Kᵥ] = C • ((E⁄Kᵥ).quadraticTwist L)`,
`ψ := quadraticCharacter Kᵥ L Ω` (which already has type `(Ω ≃ₐ[Kᵥ] Ω) →* ℤˣ`,
i.e. `Γ Kᵥ →* ℤˣ`, since `Field.absoluteGaloisGroup` is reducible), and for `φ`
the composite

    X(Ω) ≃ ((E⁄Kᵥ).quadraticTwist L)(Ω) ≃ (E⁄Kᵥ)(Ω) = E(Ω)

of `equivVariableChangeBaseChange`, `quadraticTwistPointEquiv Kᵥ L Ω`, and the
`equivOfEq` for `(E⁄Kᵥ)⁄Ω = E⁄Ω`.  The twisted equivariance is
`quadraticTwistPointEquiv_galois`, whose conclusion is *verbatim* the one here
with `ψ σ = quadraticCharacter Kᵥ L Ω σ`; the outer two factors contribute
nothing, by `equivVariableChangeBaseChange_galois` and by the `key` transport
already carried out in `T₁b₁` above — **both of those are PROVEN there and
should be copied rather than redone.**

Assembly, in the order the three factors are peeled off `φ`.  `key` moves the
outer `equivOfEq` past `Point.map` (the `restrictScalars ℚ` on the `E`-side is
invisible to it, both sides being the same function of `Ω`);
`equivVariableChangeBaseChange_galois` moves the inner one past `Point.map`
untwisted, since `C` is `Kᵥ`-rational; and `quadraticTwistPointEquiv_galois`
supplies the single factor of `χ σ`.  The character then appears TWICE — once
from the goal's `ψ σ`, once from the middle factor — and `Int.units_coe_mul_self`
collapses `χ(σ)² = 1`, which is the formal shadow of `ψ` being quadratic.

Note the conclusion is quantified over ALL of `Γ Kᵥ`, not over inertia: that
is the whole point of carrying `ψ`, and it is what makes `T₂` true in its
stated (non-inertial) generality.  A RAMIFIED `ψ` occurs exactly here, in the
additive potentially-multiplicative case — an unramified `ψ` would be
invisible to inertia and the twist could then be dropped, which is precisely
the collapse `T₂`'s faithfulness note forbids. -/
theorem WeierstrassCurve.exists_splitModel_quadraticCharacter_pointEquiv_of_quadraticTwist
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {v : ℕ} (hv : v.Prime)
    (htwist :
      ∃ (L : Type) (_ : Field L)
        (_ : Algebra (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat) L)
        (_ : Algebra.IsQuadraticExtension (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat) L)
        (_ : Algebra.IsSeparable (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat) L),
        (((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat))).quadraticTwist L).minimal
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat]).HasSplitMultiplicativeReduction
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat]) :
    ∃ (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))
      (_ : X.IsElliptic)
      (_ : X.HasSplitMultiplicativeReduction
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat])
      (ψ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) →* ℤˣ)
      (φ : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point ≃+
        ((E⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point),
      ∀ (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))
        (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point),
        WeierstrassCurve.Affine.Point.map (W' := E)
            ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ) (φ P) =
          ((ψ σ : ℤ)) • φ (WeierstrassCurve.Affine.Point.map (W' := X)
            ((σ : _ ≃ₐ[_] _).toAlgHom) P) := by
  classical
  obtain ⟨L, hLfield, hLalg, hLquad, hLsep, hsplit⟩ := htwist
  letI := hLfield
  letI := hLalg
  letI := hLquad
  letI := hLsep
  -- fix an embedding of `L` into the local algebraic closure, over `Kᵥ`
  letI algLΩ : Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) :=
    (IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))
      (R := HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) (S := L)).toAlgebra
  haveI : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))
        (R := HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)
        (S := L)).commutes x).symm)
  set W : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) :=
    E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) with hWdef
  haveI hWell : W.IsElliptic := by
    rw [hWdef]; exact inferInstanceAs (E.map (algebraMap ℚ _)).IsElliptic
  set T : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) := W.quadraticTwist L with hTdef
  haveI hTell : T.IsElliptic := by
    rw [hTdef]; exact inferInstanceAs (W.quadraticTwist L).IsElliptic
  set C : WeierstrassCurve.VariableChange (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) :=
    (T.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat]).choose with hCdef
  -- `W⁄Ω = E⁄Ω`: the two ring homomorphisms `ℚ → Ω` agree because `ℚ` is initial
  have hbase : (W⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))) =
      (E⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))) := by
    show W.map (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) _) = E.map (algebraMap ℚ _)
    rw [hWdef, WeierstrassCurve.map_map]
    congr 1
  refine ⟨C • T, inferInstanceAs ((C • T).IsElliptic), hsplit,
    quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)),
    (WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange T C
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))).trans
      ((W.quadraticTwistPointEquiv L (AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat))).trans
        (WeierstrassCurve.Affine.Point.equivOfEq hbase)), ?_⟩
  intro σ P
  -- transporting `Point.map` across the curve identification `W⁄Ω = E⁄Ω`
  have key : ∀ R : (W⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))).Point,
      WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ)
          (WeierstrassCurve.Affine.Point.equivOfEq hbase R) =
        WeierstrassCurve.Affine.Point.equivOfEq hbase
          (WeierstrassCurve.Affine.Point.map (W' := W) ((σ : _ ≃ₐ[_] _).toAlgHom) R) := by
    intro R
    cases R with
    | zero =>
      simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero]
    | some x y hns =>
      rw [WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.equivOfEq_some]
      rfl
  have h1 := WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange_galois T C
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) (σ : _ ≃ₐ[_] _) P
  have h2 := W.quadraticTwistPointEquiv_galois L
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) (σ : _ ≃ₐ[_] _)
    (WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange T C
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)) P)
  simp only [AddEquiv.trans_apply]
  rw [key, h1, h2, map_zsmul, smul_smul, Int.units_coe_mul_self, one_zsmul]

open ValuativeRel IsDedekindDomain in
/-- **`T₁` — Tate's `v`-adic uniformisation, in twisted form** (DECOMPOSED and
PROVEN 2026-07-28 from `T₁a` and `T₁b₁`/`T₁b₂` above;
Silverman *ATAEC* V.3.1, V.5.3; Serre, Invent. Math. 15 (1972), §5.4): at a
prime `v` of POTENTIALLY MULTIPLICATIVE reduction, i.e. `v(j) < 0`, the curve
`E` over the algebraic closure `Ω` of `Kᵥ = ℚ_v` is uniformised by `Ωˣ/Qᶻ` for
a Galois-FIXED parameter `Q` of infinite order, equivariantly up to the sign
of a quadratic twisting character `ψ : Γ Kᵥ →* ℤˣ`.

The three conjuncts are, in order: `Q` has infinite order (equivalently
`v(Q) ≠ 0`; this is what makes the exponent of `Q` a well-defined integer and
is used four times in `T₂`); `Q` is fixed by every `σ ∈ Γ Kᵥ` (it comes from
`Kᵥ` itself); and the uniformisation `e` intertwines the Galois action with
the action on `Ωˣ/Qᶻ` TWISTED BY `ψ`.

Why the twist cannot be dropped from the statement.  `E` need not itself have
multiplicative reduction over `Kᵥ` — only potentially so — and the curve with
split multiplicative reduction it becomes isomorphic to over `Ω` differs from
it by a quadratic twist.  If `φ : E_Q → E` is that `Ω`-isomorphism then
`φ^σ = φ ∘ [ψ(σ)]`, so `σ(φ P) = φ(ψ(σ)·σP) = ψ(σ)·φ(σP)`, which is exactly
the displayed equivariance.  Over INERTIA the twist is invisible when it is
unramified, but it need not be, and it is certainly not invisible over `Γ Kᵥ`
— so it is carried, not discarded.

Proof, now formalised, and it is three lines over the cut above plus the
sorry-free `TateSepClosure.lean`.  `T₁a` gives the reduction-type dichotomy
and `T₁b₁`/`T₁b₂` turn it into a split-multiplicative model `X/Kᵥ` together with the
quadratic character `ψ` and the twisted comparison `φ : X(Ω) ≃+ E(Ω)`.  Tate's
uniformisation `exists_tateEquivSepClosure` then applies to `X` — it needs
exactly `X.IsElliptic` and `X.HasSplitMultiplicativeReduction 𝒪[Kᵥ]`, minimality
being implied by the latter (`HasSplitMultiplicativeReduction` extends
`HasMultiplicativeReduction` extends `IsMinimal`) and explicitly `omit`ted
there — giving an UNtwisted `e₀ : Ωˣ/Qᶻ ≃+ X(Ω)` with
`Q := X.qUnitSepClosure Ω`.  Set `e := e₀.trans φ`; the two `Q`-conjuncts are
the PROVEN `qUnitSepClosure_zpow_injective` (the Tate parameter has valuation
`< 1` in `Kᵥ`, so `a ↦ Q^a` is injective) and `map_qUnitSepClosure_eq` (`Q` is
the image of an element of `Kᵥ`, so every `σ ∈ Γ Kᵥ` fixes it), and the third
is `hφ` followed by `he₀`.

Note that `Q` is produced for the TWISTED curve `X`, not for `E` — which is
harmless because `T₁` asserts only its existence, and is in fact forced: `E`
itself need have no Tate parameter over `Kᵥ` at all. -/
theorem WeierstrassCurve.exists_tateParametrisation_of_padicValRat_j_neg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {v : ℕ} (hv : v.Prime) (hj : padicValRat v E.j < 0) :
    ∃ (Q : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))ˣ)
      (ψ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) →* ℤˣ)
      (e : Additive ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸ Subgroup.zpowers Q) ≃+
        ((E⁄(AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat)))).Point),
      Function.Injective (fun n : ℤ => Q ^ n) ∧
      (∀ σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat),
        Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom Q = Q) ∧
      (∀ (σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))
        (u : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hv.toHeightOneSpectrumRingOfIntegersRat))ˣ),
        WeierstrassCurve.Affine.Point.map (W' := E)
            ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ) (e (Additive.ofMul ↑u)) =
          ((ψ σ : ℤ)) • e (Additive.ofMul
            ↑(Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom u))) := by
  obtain ⟨X, hXell, hXsplit, ψ, φ, hφ⟩ :=
    (E.hasSplitMultiplicativeReduction_or_exists_quadraticTwist_of_padicValRat_j_neg
        hv hj).elim
      (fun h => E.exists_splitModel_quadraticCharacter_pointEquiv_of_hasSplitMultiplicativeReduction
        hv h)
      (fun h => E.exists_splitModel_quadraticCharacter_pointEquiv_of_quadraticTwist hv h)
  haveI : X.IsElliptic := hXell
  haveI : X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat] := hXsplit
  obtain ⟨e₀, he₀⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ hv.toHeightOneSpectrumRingOfIntegersRat)
    (E := X)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))
  refine ⟨X.qUnitSepClosure _, ψ, e₀.trans φ,
    X.qUnitSepClosure_zpow_injective _,
    fun σ => X.map_qUnitSepClosure_eq _ (σ : _ ≃ₐ[_] _), fun σ u => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [hφ σ (e₀ (Additive.ofMul ↑u)), he₀ (σ : _ ≃ₐ[_] _) u]

/-- **The `μ_N`-vs-étale dichotomy inside a Tate quotient** (PROVEN
2026-07-28; pure group theory, the arithmetic-free core of `T₂` below).

Setting: a commutative group `G` with a distinguished element `Q` whose
integer powers are distinct, the quotient `G/Qᶻ` written additively and
identified with an abelian group `A` by `e`, and a point `P ∈ A` of exact
order a prime `N`.  An index type `Γ` acts on `G` by `S` and on `A` by `T`,
the two actions being intertwined by `e` UP TO THE SIGN `s σ` (this is the
quadratic twist of `T₁`), `Q` is `S`-fixed, `T σ` scales `P` by `m σ`, and
`S σ` raises every `N`-th root of unity to the power `c σ` (this is the
cyclotomic character).

Conclusion: either `m = c·s` throughout, or `m = s` throughout — with the
SAME alternative for every `σ`, because the alternative is decided by a
single integer `a` attached to `P` and not by `σ`.

Proof.  Pick a representative `u ∈ G` of `e⁻¹ P` with `uᴺ = Qᵃ`.  The
intertwining gives `S σ u = u^{s σ · m σ} · Q^{d σ}`, and taking `N`-th
powers (using `S σ Q = Q`) forces `a = a·(s σ · m σ) + d σ · N`.

* If `N ∤ a`, then `a` is invertible mod `N` and the displayed relation
  collapses to `s σ · m σ ≡ 1`, i.e. `m σ ≡ s σ` (as `s σ² = 1`).  This is
  the étale case.
* If `N ∣ a`, say `a = N·b`, then `z := u · Q^{-b}` satisfies `zᴺ = 1` and
  has the same class as `u`, so `z ≠ 1` (else `P = 0`) and `z` has order
  exactly `N`.  A second `N`-th power computation kills the `Q`-factor and
  leaves `S σ z = z^{s σ · m σ}`; comparing with `S σ z = z^{c σ}` and using
  `orderOf z = N` gives `s σ · m σ ≡ c σ`, i.e. `m σ ≡ c σ · s σ`.  This is
  the `μ_N` case. -/
theorem tateQuotient_dichotomy_of_intertwined_action
    {G : Type*} [CommGroup G] (Q : G)
    (hQinj : Function.Injective (fun n : ℤ => Q ^ n))
    {A : Type*} [AddCommGroup A]
    (e : Additive (G ⧸ Subgroup.zpowers Q) ≃+ A)
    {N : ℕ} (hN : N.Prime)
    (P : A) (hP : addOrderOf P = N)
    {Γ : Type*}
    (S : Γ → (G →* G)) (T : Γ → (A →+ A))
    (s : Γ → ℤ) (m : Γ → ℕ) (c : Γ → ℕ)
    (hs : ∀ σ, s σ * s σ = 1)
    (hQfix : ∀ σ, S σ Q = Q)
    (he : ∀ (σ : Γ) (u : G), T σ (e (Additive.ofMul (↑u : G ⧸ Subgroup.zpowers Q))) =
      (s σ) • e (Additive.ofMul (↑(S σ u) : G ⧸ Subgroup.zpowers Q)))
    (hT : ∀ σ, T σ P = (m σ) • P)
    (hc : ∀ (σ : Γ) (w : G), w ^ N = 1 → S σ w = w ^ (c σ)) :
    (∀ σ, ((m σ : ℕ) : ZMod N) = ((c σ : ℕ) : ZMod N) * ((s σ : ℤ) : ZMod N)) ∨
    (∀ σ, ((m σ : ℕ) : ZMod N) = ((s σ : ℤ) : ZMod N)) := by
  classical
  haveI : NeZero N := ⟨hN.ne_zero⟩
  haveI : Fact N.Prime := ⟨hN⟩
  -- the class of `P` is `N`-torsion, so it has a representative `u` with `u ^ N = Q ^ a`
  have hPtor : ((N : ℕ) : ℤ) • (e.symm P) = 0 := by
    have h1 : ((N : ℕ) : ℤ) • P = 0 := by
      rw [natCast_zsmul, ← hP]
      exact addOrderOf_nsmul_eq_zero P
    rw [← map_zsmul e.symm, h1, map_zero]
  obtain ⟨u, a, hu, ha⟩ := exists_rep_pow_eq_zpow_of_torsion Q (e.symm P) hPtor
  have hPu : e (Additive.ofMul (↑u : G ⧸ Subgroup.zpowers Q)) = P := by
    rw [hu, e.apply_symm_apply]
  -- for each `σ`, `S σ u` and `u ^ (s σ * m σ)` have the same class
  have key : ∀ σ : Γ, ∃ d : ℤ,
      S σ u = u ^ ((s σ) * ((m σ : ℕ) : ℤ)) * Q ^ d := by
    intro σ
    have h1 : (s σ) • e (Additive.ofMul (↑(S σ u) : G ⧸ Subgroup.zpowers Q)) =
        ((m σ : ℕ) : ℤ) • P := by
      rw [← he σ u, hPu, hT σ, natCast_zsmul]
    have h2 : e (Additive.ofMul (↑(S σ u) : G ⧸ Subgroup.zpowers Q)) =
        ((s σ) * ((m σ : ℕ) : ℤ)) • P := by
      rw [mul_zsmul, ← h1, smul_smul, hs σ, one_zsmul]
    have h3 : Additive.ofMul (↑(S σ u) : G ⧸ Subgroup.zpowers Q) =
        Additive.ofMul ((↑u : G ⧸ Subgroup.zpowers Q) ^ ((s σ) * ((m σ : ℕ) : ℤ))) := by
      rw [ofMul_zpow, hu, ← map_zsmul e.symm, ← h2, e.symm_apply_apply]
    have h4 : ((u ^ ((s σ) * ((m σ : ℕ) : ℤ)) : G) : G ⧸ Subgroup.zpowers Q) =
        ((S σ u : G) : G ⧸ Subgroup.zpowers Q) := by
      rw [QuotientGroup.mk_zpow]
      exact (Additive.ofMul.injective h3).symm
    obtain ⟨d, hd⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp h4)
    exact ⟨d, by rw [hd, mul_inv_cancel_left]⟩
  choose d hd using key
  -- the exponent relation, obtained by taking `N`-th powers
  have hrel : ∀ σ : Γ, a = a * ((s σ) * ((m σ : ℕ) : ℤ)) + d σ * (N : ℤ) := by
    intro σ
    apply hQinj
    have hL : Q ^ a = S σ (u ^ N) := by rw [ha, map_zpow, hQfix σ]
    have hR : S σ (u ^ N) = Q ^ (a * ((s σ) * ((m σ : ℕ) : ℤ)) + d σ * (N : ℤ)) := by
      calc S σ (u ^ N) = (S σ u) ^ N := map_pow _ _ _
        _ = (u ^ ((s σ) * ((m σ : ℕ) : ℤ)) * Q ^ (d σ)) ^ N := by rw [hd σ]
        _ = (u ^ N) ^ ((s σ) * ((m σ : ℕ) : ℤ)) * Q ^ (d σ * (N : ℤ)) := by
              rw [mul_pow, ← zpow_natCast (u ^ ((s σ) * ((m σ : ℕ) : ℤ))) N,
                ← zpow_natCast (Q ^ (d σ)) N, ← zpow_mul, ← zpow_mul,
                mul_comm ((s σ) * ((m σ : ℕ) : ℤ)) (N : ℤ), zpow_mul, zpow_natCast]
        _ = Q ^ (a * ((s σ) * ((m σ : ℕ) : ℤ)) + d σ * (N : ℤ)) := by
              rw [ha, ← zpow_mul, ← zpow_add]
    exact hL.trans hR
  have hss : ∀ σ : Γ, ((s σ : ℤ) : ZMod N) * ((s σ : ℤ) : ZMod N) = 1 := by
    intro σ
    have := congrArg (fun z : ℤ => ((z : ZMod N))) (hs σ)
    push_cast at this
    exact this
  by_cases hdvd : ((N : ℤ)) ∣ a
  · -- `N ∣ a`: the stable line is `μ_N`
    left
    obtain ⟨b, hb⟩ := hdvd
    set z : G := u * Q ^ (-b) with hzdef
    have hzN : z ^ N = 1 := by
      rw [hzdef, mul_pow, ha, ← zpow_natCast (Q ^ (-b)) N, ← zpow_mul, ← zpow_add, hb]
      rw [show (N : ℤ) * b + -b * (N : ℤ) = 0 by ring, zpow_zero]
    have hzcls : ((z : G) : G ⧸ Subgroup.zpowers Q) = ((u : G) : G ⧸ Subgroup.zpowers Q) := by
      rw [hzdef, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _),
        mul_one]
    have hzne : z ≠ 1 := by
      intro h0
      have h1 : e.symm P = 0 := by
        rw [← hu, ← hzcls, h0, QuotientGroup.mk_one, ofMul_one]
      have h2 : P = 0 := by
        have := congrArg e h1
        rwa [e.apply_symm_apply, map_zero] at this
      rw [h2, addOrderOf_zero] at hP
      exact hN.one_lt.ne hP
    have hzord : orderOf z = N := by
      rcases hN.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hzN) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hzne
      · exact h
    have hzS : ∀ σ : Γ, S σ z = z ^ ((s σ) * ((m σ : ℕ) : ℤ)) := by
      intro σ
      have hex : S σ z = z ^ ((s σ) * ((m σ : ℕ) : ℤ)) *
          Q ^ (d σ - b + b * ((s σ) * ((m σ : ℕ) : ℤ))) := by
        rw [hzdef, map_mul, map_zpow, hQfix σ, hd σ, mul_zpow, ← zpow_mul,
          mul_assoc, mul_assoc, ← zpow_add, ← zpow_add]
        congr 1
        rw [show d σ + -b = -b * ((s σ) * ((m σ : ℕ) : ℤ)) +
          (d σ - b + b * ((s σ) * ((m σ : ℕ) : ℤ))) from by ring]
      have hzero : d σ - b + b * ((s σ) * ((m σ : ℕ) : ℤ)) = 0 := by
        have h1 : (S σ z) ^ N = 1 := by rw [← map_pow, hzN, map_one]
        rw [hex, mul_pow, ← zpow_natCast (z ^ ((s σ) * ((m σ : ℕ) : ℤ))) N, ← zpow_mul,
          mul_comm ((s σ) * ((m σ : ℕ) : ℤ)) (N : ℤ), zpow_mul, zpow_natCast, hzN,
          one_zpow, one_mul, ← zpow_natCast (Q ^ _) N, ← zpow_mul] at h1
        have h2 : (d σ - b + b * ((s σ) * ((m σ : ℕ) : ℤ))) * (N : ℤ) = 0 := by
          apply hQinj
          show Q ^ ((d σ - b + b * ((s σ) * ((m σ : ℕ) : ℤ))) * (N : ℤ)) = Q ^ (0 : ℤ)
          rw [zpow_zero]
          exact h1
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (by exact_mod_cast hN.ne_zero)
      rw [hex, hzero, zpow_zero, mul_one]
    intro σ
    have h1 : z ^ ((s σ) * ((m σ : ℕ) : ℤ)) = z ^ ((c σ : ℕ) : ℤ) := by
      rw [← hzS σ, hc σ z hzN, zpow_natCast]
    have h2 : ((s σ) * ((m σ : ℕ) : ℤ)) ≡ ((c σ : ℕ) : ℤ) [ZMOD (N : ℤ)] := by
      rw [← hzord]
      exact zpow_eq_zpow_iff_modEq.mp h1
    have h3 : (((s σ : ℤ) : ZMod N)) * ((m σ : ℕ) : ZMod N) = ((c σ : ℕ) : ZMod N) := by
      have := (ZMod.intCast_eq_intCast_iff' _ _ _).mpr h2
      push_cast at this
      exact this
    calc ((m σ : ℕ) : ZMod N)
        = (((s σ : ℤ) : ZMod N) * ((s σ : ℤ) : ZMod N)) * ((m σ : ℕ) : ZMod N) := by
          rw [hss σ, one_mul]
      _ = ((c σ : ℕ) : ZMod N) * ((s σ : ℤ) : ZMod N) := by rw [← h3]; ring
  · -- `N ∤ a`: the stable line is étale
    right
    intro σ
    have h2 : ((s σ : ℤ) : ZMod N) * ((m σ : ℕ) : ZMod N) = 1 := by
      have hNp : Prime ((N : ℤ)) := Nat.prime_iff_prime_int.mp hN
      have h4 : ((N : ℤ)) ∣ a * (1 - (s σ) * ((m σ : ℕ) : ℤ)) :=
        ⟨d σ, by linear_combination hrel σ⟩
      have h5 : ((N : ℤ)) ∣ (1 - (s σ) * ((m σ : ℕ) : ℤ)) :=
        (hNp.dvd_mul.mp h4).resolve_left hdvd
      have h6 : (((1 - (s σ) * ((m σ : ℕ) : ℤ)) : ℤ) : ZMod N) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h5
      push_cast at h6
      exact (sub_eq_zero.mp h6).symm
    calc ((m σ : ℕ) : ZMod N)
        = (((s σ : ℤ) : ZMod N) * ((s σ : ℤ) : ZMod N)) * ((m σ : ℕ) : ZMod N) := by
          rw [hss σ, one_mul]
      _ = ((s σ : ℤ) : ZMod N) := by rw [mul_assoc, h2, mul_one]

/-- **`T₂` — the isogeny character read off a Tate parametrisation** (PROVEN
2026-07-28; Serre, Invent. Math. 15 (1972), §5.4, the dichotomy `μ_N` vs
étale): given the twisted uniformisation of `T₁` and a Galois-stable line
`⟨g⟩` of order `N` with character `lam`, the character is either `χ·ψ` or `ψ`.

Proof, and it is elementary given `T₁`.  Push `g` forward
along `ι = AlgebraicClosure.map (algebraMap ℚ Kᵥ)` to `gΩ ∈ E(Ω)`;
`Affine.Point.map_injective` keeps its order `N`, and
`Field.absoluteGaloisGroup.lift_map` turns `hlam` into
`σ(gΩ) = (lam (map σ)).val • gΩ` for every `σ ∈ Γ Kᵥ`.  Write
`t := e.symm gΩ` and pick, by
`exists_rep_pow_eq_zpow_of_torsion` (`TateSepClosure.lean`), a representative
`u ∈ Ωˣ` of `t` with `u^N = Q^a`.  The dichotomy is on `a mod N`:

* `a ≡ 0 (mod N)`, say `a = N·b`.  Then `z := u·Q^{-b}` satisfies `z^N = 1`
  and has the same class as `u`, and `z` is a PRIMITIVE `N`-th root of unity
  because `[z]` has order exactly `N`.  The equivariance of `T₁` reads
  `[σz]^{ψσ} = [z]^m` with `m = (lam (map σ)).val`, i.e.
  `z^{χ(σ)ψ(σ)} = z^m·Q^c`; taking `N`-th powers gives `Q^{cN} = 1`, so `c = 0`
  by the injectivity conjunct, and primitivity gives `m ≡ χ(σ)ψ(σ)`.  This is
  the `μ_N` case, `r = 1` downstream.
* `a ≢ 0 (mod N)`.  Then `(σu)^{ψσ} = u^m·Q^c`; taking `N`-th powers and using
  `σ(Q) = Q` gives `Q^{aψσ} = Q^{am + cN}`, so `a(ψσ − m) ≡ 0 (mod N)` by
  injectivity, and `N` prime with `a ≢ 0` gives `m ≡ ψ(σ)`.  This is the étale
  case, `r = 0` downstream.

FAITHFULNESS NOTE.  The conclusion is quantified over
`localInertiaGroup v` only because that is what `T` needs; the argument above
proves it for every `σ ∈ Γ Kᵥ`, and it is TRUE in that wider form **because
`ψ` is carried explicitly**.  It is the version with `ψ` discarded that is
false outside inertia — an unramified twist is invisible to inertia and to
nothing else.  A prover may freely strengthen the two disjuncts to range over
all of `Γ Kᵥ`; do NOT instead drop `ψ`.

The formalised proof CONFIRMS that note mechanically: the inertia-membership
hypothesis is introduced as `_` and never used, so what is actually proven is
the statement with both disjuncts ranging over all of `Γ Kᵥ`.  The conclusion
is left in the inertia-restricted shape only so that `T` below — a released,
proven consumer — keeps typechecking unchanged; a later consumer that wants
the wider form may widen the quantifier here without touching this proof.

Two implementation notes for anyone editing this.  (a) The `ℚ`-algebra map
`ι : ℚ̄ → Ω` is built HERE with the AMBIENT `ℚ`-algebra structure on `Ω`
rather than reusing `Semistable.lean`'s `algClosureEmbeddingRat`, which is
stated under the non-instance tower structure `algebraRatAlgClosureAdic`;
building it locally (its `commutes'` is one `Subsingleton.elim` on ring homs
out of `ℚ`) avoids having to transport along `algebraRatAlgClosureAdic_eq_inst`
inside every `Point.map`.  (b) The step `rw [halg σ]; rfl` is not redundant:
`rw` closes goals only up to REDUCIBLE transparency, and the two sides differ
by instance arguments of `Point.map` that are defeq only at default
transparency. -/
theorem WeierstrassCurve.isogenyCharacter_eq_cyclotomic_mul_or_eq_of_tateParametrisation
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {v : ℕ} (hv : v.Prime)
    (Q : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))ˣ)
    (ψ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat) →* ℤˣ)
    (e : Additive ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸ Subgroup.zpowers Q) ≃+
      ((E⁄(AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat)))).Point)
    (hQinj : Function.Injective (fun n : ℤ => Q ^ n))
    (hQfix : ∀ σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat),
      Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom Q = Q)
    (he : ∀ (σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))
      (u : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat))ˣ),
      WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ) (e (Additive.ofMul ↑u)) =
        ((ψ σ : ℤ)) • e (Additive.ofMul
          ↑(Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom u))) :
    (∀ σ ∈ localInertiaGroup hv.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
          (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hv.toHeightOneSpectrumRingOfIntegersRat)) σ)) *
        Units.map (Int.castRingHom (ZMod N)).toMonoidHom (ψ σ)) ∨
    (∀ σ ∈ localInertiaGroup hv.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hv.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        Units.map (Int.castRingHom (ZMod N)).toMonoidHom (ψ σ)) := by
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  -- notation: `Kᵥ` is the completion, `Ω` its algebraic closure, `ι : ℚ̄ → Ω`
  -- (1) the chosen embedding `ℚ̄ → Ω`, as a `ℚ`-algebra map for the AMBIENT
  -- `ℚ`-algebra structure on `Ω` (the one this statement is written with);
  -- `commutes'` holds because a ring homomorphism out of `ℚ` is unique.
  obtain ⟨i, hiapp⟩ : ∃ i : (AlgebraicClosure ℚ) →ₐ[ℚ] AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat),
      ∀ x, i x = AlgebraicClosure.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) x :=
    ⟨{ AlgebraicClosure.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) with
        commutes' := fun r =>
          congrArg (fun f : ℚ →+* AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) => f r)
            (Subsingleton.elim ((AlgebraicClosure.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))).comp
              (algebraMap ℚ (AlgebraicClosure ℚ))) (algebraMap ℚ (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)))) },
      fun _ => rfl⟩
  have hlift : ∀ (σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) (x : AlgebraicClosure ℚ),
      (σ : _ ≃ₐ[_] _) (i x) =
        i ((Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x) := by
    intro σ x
    rw [hiapp, hiapp]
    exact (Field.absoluteGaloisGroup.lift_map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ x).symm
  have halg : ∀ σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat),
      ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ).comp i =
        i.comp ((Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom :=
    fun σ => AlgHom.ext fun x => hlift σ x
  -- (2) the transported point keeps its order, `Point.map i` being injective
  have hgord : addOrderOf (WeierstrassCurve.Affine.Point.map (W' := E) i g) = N := by
    rw [addOrderOf_injective (WeierstrassCurve.Affine.Point.map (W' := E) i)
      (WeierstrassCurve.Affine.Point.map_injective i) g, hg]
  -- (3) the local Galois action on the transported point is by `lam ∘ map`
  have hact : ∀ σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat),
      WeierstrassCurve.Affine.Point.map (W' := E) ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ)
          (WeierstrassCurve.Affine.Point.map (W' := E) i g) =
        ((lam (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : ZMod N).val) •
          WeierstrassCurve.Affine.Point.map (W' := E) i g := by
    intro σ
    calc WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ)
          (WeierstrassCurve.Affine.Point.map (W' := E) i g)
        = WeierstrassCurve.Affine.Point.map (W' := E)
            (((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ).comp i) g :=
          WeierstrassCurve.Affine.Point.map_map _ _ _
      _ = WeierstrassCurve.Affine.Point.map (W' := E)
            (i.comp ((Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom) g := by
          rw [halg σ]; rfl
      _ = WeierstrassCurve.Affine.Point.map (W' := E) i
            (WeierstrassCurve.Affine.Point.map (W' := E)
              ((Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ :
                AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom g) :=
          (WeierstrassCurve.Affine.Point.map_map _ _ _).symm
      _ = WeierstrassCurve.Affine.Point.map (W' := E) i
            (((lam (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : ZMod N).val) • g) := by
          rw [hlam (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ)]
      _ = ((lam (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : ZMod N).val) •
            WeierstrassCurve.Affine.Point.map (W' := E) i g := map_nsmul _ _ _
  -- (4) the `N`-th roots of unity of `Ω` all come from `ℚ̄`, so the mod-`N`
  -- cyclotomic character of `Γ ℚ` describes the local action on them
  obtain ⟨z0, hz0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hz0u : IsUnit z0 := hz0.isUnit hN.ne_zero
  have hspec : ∀ τ : Field.absoluteGaloisGroup ℚ,
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) z0 =
        z0 ^ ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ τ :
          (ZMod N)ˣ) : ZMod N).val := by
    intro τ
    have hmem : hz0u.unit ∈ rootsOfUnity N (AlgebraicClosure ℚ) := by
      rw [mem_rootsOfUnity]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
      exact hz0.pow_eq_one
    have hsp := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ) τ) hmem
    rw [IsUnit.unit_spec] at hsp
    exact hsp
  have hzz : IsPrimitiveRoot (i z0) N := hz0.map_of_injective i.injective
  have hcyc : ∀ (σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) (w : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))ˣ), w ^ N = 1 →
      Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom w =
        w ^ ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
          (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : (ZMod N)ˣ) : ZMod N).val := by
    intro σ w hw
    apply Units.ext
    have hwval : ((w : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
    obtain ⟨j, -, hj⟩ := hzz.eq_pow_of_pow_eq_one hwval
    rw [Units.val_pow_eq_pow_val]
    show (σ : _ ≃ₐ[_] _) ((w : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))) =
      ((w : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat))) ^ ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : (ZMod N)ˣ) : ZMod N).val
    rw [← hj, map_pow, hlift σ z0, hspec, map_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  -- (5) the dichotomy itself is pure group theory
  have hmain := tateQuotient_dichotomy_of_intertwined_action Q hQinj e hN
    (WeierstrassCurve.Affine.Point.map (W' := E) i g) hgord
    (S := fun σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) =>
      Units.map (σ : _ ≃ₐ[_] _).toAlgHom.toRingHom.toMonoidHom)
    (T := fun σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) =>
      WeierstrassCurve.Affine.Point.map (W' := E) ((σ : _ ≃ₐ[_] _).toAlgHom.restrictScalars ℚ))
    (s := fun σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) => ((ψ σ : ℤ)))
    (m := fun σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) =>
      ((lam (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : ZMod N).val))
    (c := fun σ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat) =>
      ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hv.toHeightOneSpectrumRingOfIntegersRat)) σ) : (ZMod N)ˣ) : ZMod N).val)
    (fun σ => by
      have h1 : (ψ σ) * (ψ σ) = 1 := by rw [← sq, Int.units_sq]
      have h2 := congrArg (Units.val) h1
      rw [Units.val_mul, Units.val_one] at h2
      exact h2)
    hQfix he hact hcyc
  -- (6) repackage the two cases as equalities of UNITS of `ZMod N`
  have hval : ∀ x : (ZMod N)ˣ, (((x : ZMod N).val : ℕ) : ZMod N) = (x : ZMod N) := by
    intro x
    simp [ZMod.natCast_val, ZMod.cast_id]
  rcases hmain with h | h
  · left
    intro σ _
    apply Units.ext
    have h2 := h σ
    rw [hval, hval] at h2
    rw [Units.val_mul, h2, Units.coe_map]
    rfl
  · right
    intro σ _
    apply Units.ext
    have h2 := h σ
    rw [hval] at h2
    rw [h2, Units.coe_map]
    rfl

/-- **`T` — the Tate-curve half, SHARED by `A` and `B`** (DECOMPOSED and
PROVEN 2026-07-27 from `T₁` and `T₂` above; Tate's `v`-adic uniformisation —
Silverman *ATAEC* V.3, V.5; Serre, Invent. Math. 15 (1972), §5.4): at a prime
`v` of POTENTIALLY MULTIPLICATIVE reduction, i.e. `v(j) < 0`, the twelfth
power of the isogeny character agrees on the inertia group at `v` with
`χ^(12r)` for a single `r ∈ {0, 1}`.

**Why this leaf exists** (cut made 2026-07-27).  The Tate-curve description
of the isogeny character was previously duplicated: `A` needed it at `N` and
`B` needed it at every `q ≠ N`, and each carried it as part of a larger
sorry.  It is the SAME statement at both places — the local argument does not
know which prime it is at — so it is stated once here and consumed twice.
What is left in `A` is then exactly Serre's tame-inertia theory plus
Raynaud's classification, and what is left in `B` is exactly
Néron–Ogg–Shafarevich; neither leaf mentions Tate curves any more.

The proof is now three lines of bookkeeping over `T₂`'s dichotomy.  `T₂` gives
`λ = χ·ψ` or `λ = ψ` with `ψ` valued in `ℤˣ`; `Int.units_sq` makes `ψ²= 1`,
hence `ψ¹² = (ψ²)⁶ = 1`, and the two cases become `λ¹² = χ¹²` (take `r = 1`)
and `λ¹² = 1 = χ⁰` (take `r = 0`).

`hN19` is deliberately unused (hence underscored): `19 < N` is what `A₀` and
`B₀` need, and the Tate half of the cluster never sees it.  It is kept in the
signature because both consumers pass it positionally.

Note the conclusion is quantified over `localInertiaGroup v` and NOT over
`Γ ℚ`: an unramified twist is invisible to inertia, which is precisely why
the quadratic character `ψ` may be discarded here and may NOT be discarded
globally.  Widening the quantifier would make the leaf false — but see `T₂`,
whose statement KEEPS `ψ` and is therefore true over all of `Γ Kᵥ`. -/
theorem WeierstrassCurve.exists_isogenyTateExponent_of_padicValRat_j_neg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (_hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {v : ℕ} (hv : v.Prime) (hj : padicValRat v E.j < 0) :
    ∃ r : ℕ, r ≤ 1 ∧
      ∀ σ ∈ localInertiaGroup hv.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hv.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hv.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ (12 * r) := by
  classical
  obtain ⟨Q, ψ, e, hQinj, hQfix, he⟩ :=
    E.exists_tateParametrisation_of_padicValRat_j_neg hv hj
  -- the twisting character is quadratic, so its twelfth power is trivial
  have hψ12 : ∀ σ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hv.toHeightOneSpectrumRingOfIntegersRat),
      (Units.map (Int.castRingHom (ZMod N)).toMonoidHom (ψ σ)) ^ 12 = 1 := by
    intro σ
    have h1 : (Units.map (Int.castRingHom (ZMod N)).toMonoidHom (ψ σ)) ^ 2 = 1 := by
      rw [← map_pow, Int.units_sq, map_one]
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, h1, one_pow]
  rcases E.isogenyCharacter_eq_cyclotomic_mul_or_eq_of_tateParametrisation
      g hN hg lam hlam hv Q ψ e hQinj hQfix he with hcase | hcase
  · -- the stable line is `μ_N`: `λ = χ·ψ`, so `λ¹² = χ¹²ψ¹² = χ¹²`
    refine ⟨1, le_refl 1, ?_⟩
    intro σ hσ
    rw [hcase σ hσ, mul_pow, hψ12 σ, mul_one, mul_one]
  · -- the stable line is étale: `λ = ψ`, so `λ¹² = 1 = χ⁰`
    refine ⟨0, Nat.zero_le 1, ?_⟩
    intro σ hσ
    rw [hcase σ hσ, hψ12 σ, Nat.mul_zero, pow_zero]

/-! ##### The three-way cut of `A₀` (CARRIED OUT 2026-07-27)

The three leaves below plus ~50 lines of glue REPLACE the single sorry at
`exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg`.  The cut
separates the three inputs Serre's argument actually uses, and it turns TWO
of `A₀`'s five conclusion clauses from assumptions into theorems.

* `A₀-1` = `exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq` —
  surjectivity of `χ` on inertia at `N`.  **PROVEN 2026-07-28 by the hoist:
  it was never a mathematical leaf, only a declaration-order one, and the
  Gauss-period theorem it needed now sits just above it in this file.**
* `A₀-2` = `exists_isogenyTameExponentAt` — `λ|_{I_N}` is a power of
  `χ|_{I_N}` (tame-inertia theory).  **PROVEN 2026-07-28**, over the tame
  block of
  `Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`
  (`exists_pow_eq_of_mem_wildInertiaGroup`,
  `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker`) plus `A₀-1`.
  Its own docstring's step-1 audit — "`ker lam` is OPEN, so the curve data
  is load-bearing" — is REFUTED there: the proof uses no continuity and no
  curve data at all.
* `A₀-3` = `exists_isogenyRaynaudExponentAt_of_padicValRat_j_nonneg` —
  the semistability defect `e ∈ {1,2,3,4,6}` and Raynaud's exponent `r ≤ e`
  with `λ^e = χ^r` on `I_N`.  Was the genuinely deep leaf; **DECOMPOSED and
  PROVEN 2026-07-28** over two further leaves, cut along the good-reduction
  extension `L/ℚ_N^{nr}` presented by its inertia subgroup `J = I_L ≤ I_N`
  (the subgroup acting trivially on `E[5]`), so that no good MODEL — and
  hence no hoist of `WeierstrassCurve.PotentiallyGoodModel`, declared ~1500
  lines below — is needed to state either half:
  * `A₀-3a` = `exists_semistabilityDefect_of_padicValRat_j_nonneg` —
    Serre's `e = [I_N : J] ∈ {1,2,3,4,6}` at residue characteristic `≥ 5`;
    **DECOMPOSED and PROVEN 2026-07-29**: `J` is now CONSTRUCTED as the
    pointwise stabiliser of `E[5]` in `I_N` and `e` as its relative index, so
    all clauses but the bound hold by construction; the bound is the leaf
    `A₀-3a-i` =
    `exists_relIndex_dvd_reductionAutOrder_of_padicValRat_j_nonneg`
    (`[I_N : J] ∣ #Aut(Ẽ)`, and `#Aut(Ẽ) ∈ {2,4,6}` in char `≥ 5`).
  * `A₀-3b` = `exists_raynaudExponent_modEq_of_semistabilityDefect` —
    Raynaud's exponent, delivered as the congruence `a·e ≡ r (mod N−1)`
    rather than as a character identity.  **DECOMPOSED and PROVEN
    2026-07-29** over the leaf `A₀-3b-i` =
    `exists_fundamentalCharacter_of_semistabilityDefect`, which produces the
    level-one fundamental character `ψ_L : J ↠ 𝔽_N^×` with `λ|_J = ψ_L^r`
    (`r ≤ e`) and `χ|_J = ψ_L^e`; what is left in `A₀-3b` is reading both at
    a `σ` with `ψ_L(σ)` a generator.

**FINDING (2026-07-27): two of `A₀`'s clauses are ARITHMETIC CONSEQUENCES of
the tame congruence, not extra inputs from Raynaud.**  Reading `λ^e = χ^r`
at an inertia element on which `χ` takes a GENERATOR of `(ZMod N)ˣ` (leaf
`A₀-1`) and substituting `λ = χ^a` (leaf `A₀-2`) yields

  `a · e ≡ r (mod N − 1)`,

and `N − 1` is even because `N` is an odd prime.  Hence:

* *parity*: if `e` is even then `a · e` is even, so `r ≡ a·e (mod 2)` is
  even.  So `A₀-3` does **not** have to assert `e % 2 = 0 → r % 2 = 0`, and
  it does not — the glue proves it.  (This also silently rules out the
  `(e, r)` pairs `(2,1)`, `(4,1)`, `(4,3)`, `(6,1)`, `(6,3)`, `(6,5)`: each
  would need an odd number congruent to an even one modulo an even modulus.)
* *the `(4,2)` condition*: `4a ≡ 2 (mod N−1)` with `N − 1 = 2m` forces
  `m ∣ 2a − 1`, so `m` is odd, i.e. `N ≡ 3 (mod 4)`.  Equivalently, if
  `4 ∣ N − 1` then `4 ∣ 2 − 4a`, which is absurd.  So `A₀-3` does not have
  to assert that either.

The previous prose above `A₀` attributed the `N ≡ 3 (mod 4)` clause to the
existence of a quartic ramified extension "`ℚ_N(⁴√N)`-like".  That is not
where it comes from — it is pure congruence arithmetic, and the corrected
derivation is the one just given.

What is left genuinely missing is exactly two things, and — as of 2026-07-28,
when `A₀-2` closed — both of them are in `A₀-3` alone: the `{1,2,3,4,6}` bound
on the semistability defect at residue characteristic `≥ 5`, and Raynaud's
classification of finite flat group schemes over a base of absolute
ramification `e < N − 1`.  Neither is in mathlib, in `~/cs/FLT`, or in this
project.  (The earlier version of this sentence named `A₀-2` as well; that was
true when written and stopped being true once the tame-inertia block was
hoisted into `ArtinConductor.lean` and cut along the seam that removes the
continuity hypothesis.)
-/

/-! ##### HOIST (2026-07-28): the Gauss-period surjectivity theorem

`exists_mem_localInertiaGroup_cyclotomicCharacter_toZModPow_eq` was PROVEN
in `Fermat/FLT/Modularity/Interface.lean` and is MOVED here verbatim (same
namespace `GaloisRepresentation.Modularity`, same statement, same proof) so
that leaf `A₀-1` below can cite it: `Interface.lean` `public import`s this
module, so the dependency could only ever run in this direction.  Its only
project inputs are `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`
and `maximalIdeal_adicCompletionIntegers_eq_span`, both of whose modules
were already in this module's import cone — so nothing else travelled with
it and `Interface.lean`'s eight call sites resolve unchanged.
-/

namespace GaloisRepresentation.Modularity

open _root_.IsDedekindDomain in
set_option maxHeartbeats 2000000 in
/-- **The mod-`p` cyclotomic character maps the inertia at `p` ONTO
`(ℤ/p)^×`** (PROVEN 2026-07-24 — the surjectivity core of the
Serre §1.3 fundamental-character leaf below): every unit `u` of
`ℤ/p^1 = ℤ/p` is the level-`1` reduction of `ω(σ)` for some element
`σ` of the local inertia at `p`. This is the total tame ramification
of `ℚ_p(ζ_p)/ℚ_p` in inertia-element form, proven by a Gauss-period
argument that needs no ramification theory beyond the project's
PROVEN inertia-fixed-field node: let `H ⊆ (ℤ/p)^×` be the image of
the inertia under `ω` and suppose some unit `u₀ ∉ H`. The period
`τ₁ = ∏_{a ∈ H} (1 − ζ^a)` is then fixed by the whole inertia (the
inertia permutes the factors by translation inside `H`), so
`ℚ_pᵥ(τ₁)` lies in the fixed field of `localInertiaGroup v`, whence
`e = 1` there (`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`,
Neukirch II.9.11) and the maximal ideal of its integral closure is
generated by `p` (`maximalIdeal_adicCompletionIntegers_eq_span`). At
the finite level `τ₁` is therefore either a unit — and then the
cofactor identity `1 − ζ = (1 − ζ^{u₀})·(integral)` inverts the
MISSING factor `1 − ζ^{u₀}` — or divisible by `p`, and cancelling `p`
from `∏_{all a}(1 − ζ^a) = Φ_p(1) = p`
(`Polynomial.eval_one_cyclotomic_prime`) again inverts every factor
outside `H`, `u₀` among them. Either way all `p − 1` factors become
invertible with integral inverses, so `1/p` is integral over the
DVR `𝒪ᵥ`, hence lies in it (`IsIntegrallyClosed`) — contradicting
`p ∈ 𝔪ᵥ`. Hence `H = (ℤ/p)^×`. (Serre, Duke Math. J. 54 (1987),
§1.3, 1.7; Serre, *Corps Locaux*, IV §4.) -/
theorem exists_mem_localInertiaGroup_cyclotomicCharacter_toZModPow_eq
    {p : ℕ} [hp : Fact p.Prime] (u : (ZMod (p ^ 1))ˣ) :
    ∃ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      PadicInt.toZModPow 1
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (HeightOneSpectrum.adicCompletion ℚ
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
                (Fact.out : p.Prime)))) σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) =
        (u : ZMod (p ^ 1)) := by
  classical
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
    (Fact.out : p.Prime) with hvdef
  set f : ℚ →+* HeightOneSpectrum.adicCompletion ℚ v :=
    algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v) with hfdef
  -- the exponent character on the local Galois group: the level-`1`
  -- reduction of the global cyclotomic character
  set χring : Field.absoluteGaloisGroup ℚ →*
      ((AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) :=
    { toFun := fun g => g.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hχringdef
  set χcomp : Field.absoluteGaloisGroup
      (HeightOneSpectrum.adicCompletion ℚ v) →* (ZMod (p ^ 1))ˣ :=
    ((Units.map (PadicInt.toZModPow (p := p) 1).toMonoidHom).comp
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p).comp χring)).comp
      (Field.absoluteGaloisGroup.map f).toMonoidHom with hχcompdef
  have hχval : ∀ σ : Field.absoluteGaloisGroup
      (HeightOneSpectrum.adicCompletion ℚ v),
      ((χcomp σ : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1)) =
        PadicInt.toZModPow 1
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p
            ((Field.absoluteGaloisGroup.map f σ).toRingEquiv) : ℤ_[p]ˣ) :
            ℤ_[p]) := fun _ => rfl
  -- it suffices that the image subgroup of the local inertia is full
  suffices hHfull : ∀ w : (ZMod (p ^ 1))ˣ,
      w ∈ Subgroup.map χcomp (localInertiaGroup v) by
    obtain ⟨σ, hσ, hσval⟩ := Subgroup.mem_map.mp (hHfull u)
    exact ⟨σ, hσ, by rw [← hχval σ, hσval]⟩
  intro u₀
  by_contra hu₀mem
  -- a primitive `p`-th root of unity over `ℚ` and its local image
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure ℚ) p
  set ζ' : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f ζ₀ with hζ'def
  have hζ'prim : IsPrimitiveRoot ζ' p :=
    hζ₀.map_of_injective (AlgebraicClosure.map f).injective
  have hζ'p1 : ζ' ^ p ^ 1 = 1 := by rw [pow_one]; exact hζ'prim.pow_eq_one
  have hpow_mod : ∀ m : ℕ, ζ' ^ m = ζ' ^ (m % p ^ 1) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m (p ^ 1)]
    rw [pow_add, pow_mul, hζ'p1, one_pow, one_mul]
  -- the Galois action on `ζ'` is by the level-`1` cyclotomic exponent
  have hact : ∀ σ : Field.absoluteGaloisGroup
      (HeightOneSpectrum.adicCompletion ℚ v),
      σ ζ' = ζ' ^ ((χcomp σ : ZMod (p ^ 1))).val := by
    intro σ
    have hζ₀p1 : ζ₀ ^ p ^ 1 = 1 := by rw [pow_one]; exact hζ₀.pow_eq_one
    have hspec := cyclotomicCharacter.spec p
      ((Field.absoluteGaloisGroup.map f σ).toRingEquiv) ζ₀ hζ₀p1
    have hlift := Field.absoluteGaloisGroup.lift_map f σ ζ₀
    rw [hζ'def, ← hlift, show ((Field.absoluteGaloisGroup.map f σ) ζ₀ :
        AlgebraicClosure ℚ) =
      ((Field.absoluteGaloisGroup.map f σ).toRingEquiv) ζ₀ from rfl,
      hspec, map_pow, hχval σ]
  -- the factors of `Φ_p(1) = p`
  set q : (ZMod (p ^ 1))ˣ → AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ v) :=
    fun a => 1 - ζ' ^ ((a : ZMod (p ^ 1))).val with hqdef
  have hζ'int : _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      ζ' := by
    refine ⟨Polynomial.X ^ p - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_one, hζ'prim.pow_eq_one, sub_self]
  have hqint : ∀ a : (ZMod (p ^ 1))ˣ,
      _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v) (q a) := by
    intro a
    simp only [hqdef]
    exact isIntegral_one.sub (hζ'int.pow _)
  -- mutual divisibility of the factors, with integral cofactors
  have hdvd : ∀ a b : (ZMod (p ^ 1))ˣ, ∃ c,
      _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v) c ∧
      q b = q a * c := by
    intro a b
    refine ⟨∑ j ∈ Finset.range (((a⁻¹ * b : (ZMod (p ^ 1))ˣ) :
        ZMod (p ^ 1))).val, (ζ' ^ ((a : ZMod (p ^ 1))).val) ^ j, ?_, ?_⟩
    · exact IsIntegral.sum _ fun j _ => (hζ'int.pow _).pow _
    · simp only [hqdef]
      have hx : (ζ' ^ ((a : ZMod (p ^ 1))).val) ^
          (((a⁻¹ * b : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1))).val =
          ζ' ^ (((b : ZMod (p ^ 1))).val) := by
        rw [← pow_mul, hpow_mod, ← ZMod.val_mul, ← Units.val_mul,
          mul_inv_cancel_left]
      rw [← hx]
      linear_combination geom_sum_mul (ζ' ^ ((a : ZMod (p ^ 1))).val)
        (((a⁻¹ * b : (ZMod (p ^ 1))ˣ) : ZMod (p ^ 1))).val
  -- the full product over `(ℤ/p)ˣ` is `Φ_p(1) = p`
  have hprodfull : ∏ a : (ZMod (p ^ 1))ˣ, q a =
      ((p : ℕ) : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) := by
    have hcyc := Polynomial.eval_one_cyclotomic_prime
      (R := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ'prim,
      Polynomial.eval_prod] at hcyc
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      at hcyc
    rw [← hcyc]
    refine Finset.prod_bij (fun a _ => ζ' ^ ((a : ZMod (p ^ 1))).val)
      ?_ ?_ ?_ ?_
    · intro a _
      rw [mem_primitiveRoots hp.out.pos]
      refine hζ'prim.pow_of_coprime _ ?_
      exact (ZMod.val_coe_unit_coprime a).coprime_dvd_right
        (dvd_pow_self p one_ne_zero)
    · intro a _ b _ hab
      have ha : ((a : ZMod (p ^ 1))).val < p :=
        calc ((a : ZMod (p ^ 1))).val < p ^ 1 := ZMod.val_lt _
          _ = p := pow_one p
      have hb : ((b : ZMod (p ^ 1))).val < p :=
        calc ((b : ZMod (p ^ 1))).val < p ^ 1 := ZMod.val_lt _
          _ = p := pow_one p
      exact Units.ext (ZMod.val_injective _ (hζ'prim.pow_inj ha hb hab))
    · intro μ hμ
      rw [mem_primitiveRoots hp.out.pos] at hμ
      obtain ⟨j, hjlt, hjcop, hjeq⟩ := (hζ'prim.isPrimitiveRoot_iff).mp hμ
      refine ⟨ZMod.unitOfCoprime j (hjcop.pow_right 1), Finset.mem_univ _, ?_⟩
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by rw [pow_one]; exact hjlt)]
      exact hjeq
    · intro a _
      rfl
  -- the local closure has characteristic zero
  haveI : CharZero (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) :=
    charZero_of_injective_algebraMap
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ v) _).injective
  have hp0 : ((p : ℕ) : AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ v)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- the Gauss period over the (assumed proper) image subgroup
  set Hfin : Finset (ZMod (p ^ 1))ˣ :=
    Finset.univ.filter (· ∈ Subgroup.map χcomp (localInertiaGroup v))
    with hHfindef
  set τ₁ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v) :=
    ∏ a ∈ Hfin, q a with hτ₁def
  -- every inertia element fixes the period
  have hτ₁fix : ∀ σ ∈ localInertiaGroup v, σ τ₁ = τ₁ := by
    intro σ hσ
    have hcmem : χcomp σ ∈ Subgroup.map χcomp (localInertiaGroup v) :=
      Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩
    have hqσ : ∀ a : (ZMod (p ^ 1))ˣ, σ (q a) = q (χcomp σ * a) := by
      intro a
      simp only [hqdef]
      rw [map_sub, map_one, map_pow, hact σ, ← pow_mul, hpow_mod,
        ← ZMod.val_mul, ← Units.val_mul]
    rw [hτ₁def, map_prod, Finset.prod_congr rfl fun a _ => hqσ a]
    refine Finset.prod_nbij' (fun a => χcomp σ * a) (fun a => (χcomp σ)⁻¹ * a)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hHfindef, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, Subgroup.mul_mem _ hcmem ha.2⟩
    · intro a ha
      simp only [hHfindef, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hcmem) ha.2⟩
    · intro a _
      rw [inv_mul_cancel_left]
    · intro a _
      rw [mul_inv_cancel_left]
    · intro a _
      rfl
  -- the adjoined field `Kᵥ(τ₁)` is finite and inertia-fixed
  have hτ₁algK : _root_.IsIntegral (HeightOneSpectrum.adicCompletion ℚ v) τ₁ :=
    (Algebra.IsAlgebraic.isAlgebraic τ₁).isIntegral
  haveI hfdM : FiniteDimensional (HeightOneSpectrum.adicCompletion ℚ v)
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
        {τ₁}) :=
    IntermediateField.adjoin.finiteDimensional hτ₁algK
  have hMle : IntermediateField.adjoin
      (HeightOneSpectrum.adicCompletion ℚ v) {τ₁} ≤
      IntermediateField.fixedField (localInertiaGroup v) := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    exact hτ₁fix
  -- `𝔪ᵥ = (p)` generates the maximal ideal of the integral closure
  have hideal := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup v
    (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v) {τ₁})
    hMle
  have hspan : IsLocalRing.maximalIdeal
      (HeightOneSpectrum.adicCompletionIntegers ℚ v) =
      Ideal.span {((p : ℕ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ v)} :=
    maximalIdeal_adicCompletionIntegers_eq_span (Fact.out : p.Prime)
  have hMR : IsLocalRing.maximalIdeal
      (IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
        {τ₁})) =
      Ideal.span {((p : ℕ) :
        IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
          {τ₁}))} := by
    rw [← hideal, hspan, Ideal.map_span, Set.image_singleton, map_natCast]
  -- `τ₁` as an element of the integral closure at the finite level
  have hτ₁mem : τ₁ ∈ IntermediateField.adjoin
      (HeightOneSpectrum.adicCompletion ℚ v) {τ₁} :=
    IntermediateField.mem_adjoin_simple_self _ τ₁
  have hτ₁int : _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      τ₁ := by
    rw [hτ₁def]
    exact Finset.prod_induction q _ (fun x y hx hy => hx.mul hy)
      isIntegral_one fun a _ => hqint a
  have hτ₁Mint : _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (⟨τ₁, hτ₁mem⟩ :
      IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
        {τ₁}) := by
    rw [← isIntegral_algebraMap_iff (algebraMap
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v) {τ₁})
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))).injective]
    exact hτ₁int
  obtain ⟨T, hT⟩ := (IsIntegralClosure.isIntegral_iff
    (A := IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
        {τ₁}))).mp hτ₁Mint
  -- pushing integral-closure elements back into the algebraic closure
  set toC : IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
        {τ₁}) → AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v) :=
    fun Z => algebraMap
      (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v) {τ₁})
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
      (algebraMap (IntegralClosure
        (HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
          {τ₁}))
        (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
          {τ₁}) Z) with htoCdef
  have hpushint : ∀ Z,
      _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v) (toC Z) := by
    intro Z
    simp only [htoCdef]
    exact ((Algebra.IsIntegral.isIntegral
      (R := HeightOneSpectrum.adicCompletionIntegers ℚ v)
      Z).algebraMap).algebraMap
  have hToCT : toC T = τ₁ := by
    simp only [htoCdef]
    rw [hT]
    rfl
  -- either way, the missing factor `1 − ζ'^{u₀}` acquires an integral
  -- inverse
  have hqu₀inv : ∃ y,
      _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v) y ∧
      q u₀ * y = 1 := by
    by_cases hTu : IsUnit T
    · -- the period is a unit at the finite level
      obtain ⟨Tu, hTueq⟩ := hTu
      have hTmul : T * ((Tu⁻¹ : _ˣ) : IntegralClosure
          (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
            {τ₁})) = 1 := by
        rw [← hTueq, Units.mul_inv]
      have hTCinv : toC T * toC ((Tu⁻¹ : _ˣ) : IntegralClosure
          (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
            {τ₁})) = 1 := by
        simp only [htoCdef]
        rw [← map_mul, ← map_mul, hTmul, map_one, map_one]
      have hTinv : τ₁ * toC ((Tu⁻¹ : _ˣ) : IntegralClosure
          (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
            {τ₁})) = 1 :=
        calc τ₁ * toC ((Tu⁻¹ : _ˣ) : IntegralClosure
              (HeightOneSpectrum.adicCompletionIntegers ℚ v)
              (IntermediateField.adjoin
                (HeightOneSpectrum.adicCompletion ℚ v) {τ₁}))
            = toC T * toC ((Tu⁻¹ : _ˣ) : IntegralClosure
              (HeightOneSpectrum.adicCompletionIntegers ℚ v)
              (IntermediateField.adjoin
                (HeightOneSpectrum.adicCompletion ℚ v) {τ₁})) := by
              rw [hToCT]
          _ = 1 := hTCinv
      obtain ⟨c, hcint, hc⟩ := hdvd u₀ 1
      have h1H : (1 : (ZMod (p ^ 1))ˣ) ∈ Hfin := by
        simp only [hHfindef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Subgroup.one_mem _⟩
      have hτfact : τ₁ = q u₀ * (c * ∏ a ∈ Hfin.erase 1, q a) := by
        rw [hτ₁def, ← Finset.mul_prod_erase Hfin q h1H, hc]
        ring
      refine ⟨(c * ∏ a ∈ Hfin.erase 1, q a) * toC ((Tu⁻¹ : _ˣ) :
        IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntermediateField.adjoin
            (HeightOneSpectrum.adicCompletion ℚ v) {τ₁})), ?_, ?_⟩
      · exact (hcint.mul (Finset.prod_induction q _
          (fun x y hx hy => hx.mul hy) isIntegral_one
          fun a _ => hqint a)).mul (hpushint _)
      · rw [← mul_assoc, ← hτfact]
        exact hTinv
    · -- the period is divisible by `p` at the finite level
      have hTm : T ∈ IsLocalRing.maximalIdeal
          (IntegralClosure (HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntermediateField.adjoin (HeightOneSpectrum.adicCompletion ℚ v)
            {τ₁})) := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rw [hMR] at hTm
      obtain ⟨Z, hZ⟩ := Ideal.mem_span_singleton'.mp hTm
      have hτ₁p : τ₁ = toC Z * ((p : ℕ) : AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ v)) := by
        rw [← hToCT]
        simp only [htoCdef]
        rw [← hZ, map_mul, map_mul, map_natCast, map_natCast]
      have hsplit : τ₁ * ∏ a ∈ Hfinᶜ, q a = ((p : ℕ) : AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ v)) := by
        rw [hτ₁def, Finset.prod_mul_prod_compl, hprodfull]
      have hcancel : toC Z * ∏ a ∈ Hfinᶜ, q a = 1 := by
        have h2 : ((p : ℕ) : AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ v)) *
            (toC Z * ∏ a ∈ Hfinᶜ, q a) =
            ((p : ℕ) : AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ v)) * 1 := by
          rw [mul_one]
          calc ((p : ℕ) : AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ v)) *
                (toC Z * ∏ a ∈ Hfinᶜ, q a)
              = (toC Z * ((p : ℕ) : AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ v))) *
                ∏ a ∈ Hfinᶜ, q a := by ring
            _ = τ₁ * ∏ a ∈ Hfinᶜ, q a := by rw [← hτ₁p]
            _ = ((p : ℕ) : AlgebraicClosure
                (HeightOneSpectrum.adicCompletion ℚ v)) := hsplit
        exact mul_left_cancel₀ hp0 h2
      have hu₀c : u₀ ∈ Hfinᶜ := by
        simp only [Finset.mem_compl, hHfindef, Finset.mem_filter]
        intro hcon2
        exact hu₀mem hcon2.2
      refine ⟨toC Z * (∏ a ∈ Hfinᶜ.erase u₀, q a), ?_, ?_⟩
      · exact (hpushint _).mul (Finset.prod_induction q _
          (fun x y hx hy => hx.mul hy) isIntegral_one fun a _ => hqint a)
      · rw [← hcancel, ← Finset.mul_prod_erase Hfinᶜ q hu₀c]
        ring
  -- hence every factor is invertible, hence so is `p` itself
  obtain ⟨y₀, hy₀int, hy₀⟩ := hqu₀inv
  have hinvall : ∀ a : (ZMod (p ^ 1))ˣ, ∃ y,
      _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v) y ∧
      q a * y = 1 := by
    intro a
    obtain ⟨c, hcint, hc⟩ := hdvd a u₀
    exact ⟨c * y₀, hcint.mul hy₀int, by rw [← mul_assoc, ← hc, hy₀]⟩
  choose W hWint hW using hinvall
  have hpW : ((p : ℕ) : AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ v)) *
      ∏ a : (ZMod (p ^ 1))ˣ, W a = 1 := by
    rw [← hprodfull, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => hW a
  have hWprodint : _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (∏ a : (ZMod (p ^ 1))ˣ, W a) :=
    Finset.prod_induction W _ (fun x y hx hy => hx.mul hy) isIntegral_one
      fun a _ => hWint a
  -- so `1/p` is integral over `𝒪ᵥ`, hence lies in `𝒪ᵥ`: contradiction
  have hpKv : ((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hWeq : ∏ a : (ZMod (p ^ 1))ˣ, W a =
      algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
        (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) := by
    have hcast : ((p : ℕ) : AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ v)) =
        algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
          ((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) := by
      rw [map_natCast]
    have h2 : algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
        (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) *
        algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
          ((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hpKv, map_one]
    calc ∏ a : (ZMod (p ^ 1))ˣ, W a
        = (algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
            (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) *
          algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
            ((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)) *
          ∏ a : (ZMod (p ^ 1))ˣ, W a := by rw [h2, one_mul]
      _ = algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
            (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) *
          (((p : ℕ) : AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ v)) *
            ∏ a : (ZMod (p ^ 1))ˣ, W a) := by rw [hcast]; ring
      _ = algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
            (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) := by
            rw [hpW, mul_one]
  have hint : _root_.IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (((p : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹) := by
    rw [← isIntegral_algebraMap_iff
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))).injective,
      ← hWeq]
    exact hWprodint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hpy : ((p : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ v) *
      y = 1 := by
    apply IsFractionRing.injective
      (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (HeightOneSpectrum.adicCompletion ℚ v)
    rw [map_mul, map_natCast, hy, map_one, mul_inv_cancel₀ hpKv]
  have hpmem : ((p : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ v) ∈
      IsLocalRing.maximalIdeal
        (HeightOneSpectrum.adicCompletionIntegers ℚ v) := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpmem
  exact hpmem (IsUnit.of_mul_eq_one _ hpy)

end GaloisRepresentation.Modularity

/-- **`A₀-1` — the mod-`N` cyclotomic character maps the inertia at `N` ONTO
`(ZMod N)ˣ`** (PROVEN 2026-07-28 by the hoist recorded above; this is the
total tame ramification of `ℚ_N(ζ_N)/ℚ_N` in inertia-element form): every
unit `u` of `ZMod N` is `χ̄(σ)` for some `σ` in the local inertia group
at `N`.

**This was never a mathematical leaf — it was a DECLARATION-ORDER leaf**, and
it closed by moving, not by proving.  The identical statement written in
`cyclotomicCharacter` (`ℤ_N`-valued) rather than `cyclotomicCharacterModL`
(`(ZMod N)ˣ`-valued) vocabulary had been PROVEN since 2026-07-24 as
`exists_mem_localInertiaGroup_cyclotomicCharacter_toZModPow_eq` — ~420 lines,
by a Gauss-period argument — but it lived in
`Fermat/FLT/Modularity/Interface.lean`, which `public import`s THIS module, so
Lean's lack of forward references was the ONLY obstruction.  That theorem is
now declared above (see the HOIST note), verbatim and in its original
namespace, and `Interface.lean` cites it from here; the audit that said the
move needed no further dependency work was correct.

The vocabulary change is the two lines of glue below:
`WeilPairing.cyclotomicCharacterModL_eq_toZMod` says `χ̄(σ) = toZMod (χ(σ))`,
and `GaloisRepresentation.toZMod_eq_ringEquivCongr_comp_toZModPow`
(`Chebotarev.lean`) says `toZMod = ringEquivCongr (pow_one N) ∘ toZModPow 1`,
so the only real content is transporting the target unit `u : (ZMod N)ˣ`
across the `ZMod (N ^ 1) ≃+* ZMod N` congruence and back — `ringEquivCongr`
preserves `ZMod.val`, so `ZMod.val_injective` closes it. -/
theorem exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq
    {N : ℕ} (hN : N.Prime) (u : (ZMod N)ˣ) :
    ∃ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
      (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) = u := by
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  obtain ⟨σ, hσ, hval⟩ :=
    GaloisRepresentation.Modularity.exists_mem_localInertiaGroup_cyclotomicCharacter_toZModPow_eq
      (p := N)
      (Units.map (ZMod.ringEquivCongr (pow_one N).symm).toRingHom.toMonoidHom u)
  refine ⟨σ, hσ, Units.ext ?_⟩
  rw [WeilPairing.cyclotomicCharacterModL_eq_toZMod,
    GaloisRepresentation.toZMod_eq_ringEquivCongr_comp_toZModPow,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    hval, Units.coe_map]
  exact ZMod.val_injective _ (by
    rw [ZMod.ringEquivCongr_val]
    exact ZMod.ringEquivCongr_val _ _)

/-- **`A₀-2` — the isogeny character is TAME at `N`: `λ|_{I_N}` is a power of
`χ|_{I_N}`** (**PROVEN 2026-07-28**; Serre, Invent. Math. 15 (1972), §1.3,
§1.7 and §5.4): there is an exponent `a` with `λ(σ) = χ(σ)^a` for every `σ`
in the local inertia group at `N`.

Stated with NO reduction hypothesis, deliberately: this is true at every
prime and for every reduction type, and only the Raynaud leaf below needs
`v_N(j) ≥ 0`.  So it is separately ownable and separately reusable.

**CORRECTION OF THIS DOCSTRING'S OWN ROUTE AUDIT (2026-07-28).**  The
previous version recorded a three-step proof whose step 1 was "`ker lam` is
OPEN", and asserted that the curve data `g`, `hg`, `hlam` are *load-bearing*
because "the same statement for an ARBITRARY `MonoidHom Γ ℚ →* (ZMod N)ˣ` is
FALSE, a discontinuous character having no reason to be tame".

**That is wrong, and the proof below is the refutation: NO CONTINUITY IS USED
ANYWHERE.**  `E`, `_g`, `_hg` and `_hlam` are consumed by nothing — they are
underscore-prefixed so the emptiness is mechanically visible — and the
theorem holds verbatim for an arbitrary monoid homomorphism.  Both places
where continuity was expected to enter turn out to have it already discharged
inside the local-Galois machinery, in a form that quantifies over ELEMENTS
rather than over continuous quotients:

* *Wild inertia dies*, and it dies ABSTRACTLY.  The argument is not "a
  continuous map from a pro-`N` group to a group of order prime to `N` is
  trivial"; it is `exists_pow_eq_of_mem_wildInertiaGroup`
  (`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`), which
  says every element of `P_N` **is** an `(N−1)`-st power *inside* `P_N`,
  because the `n`-th power map is a bijection of a pro-`ℓ` group for `ℓ ∤ n`.
  An `(N−1)`-st power is killed by **any** homomorphism into `(ZMod N)ˣ`,
  continuous or not, since `#(ZMod N)ˣ = N − 1`.
* *The tame quotient is procyclic*, and again abstractly:
  `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker` (same file) says
  every FINITE quotient of `I_v` that kills `P_v` is cyclic with a
  non-negative-exponent generator, and its docstring is explicit that no
  continuity is required and none *can* be, the target carrying no topology.

The general moral is the one this development keeps relearning: an audit is a
dated claim about the tree, and the tree moves.  The step-1 note was written
when the tame-inertia block still lived in `Threeadic.lean` in continuous
form; it was hoisted into `ArtinConductor.lean` on 2026-07-27 and cut along
exactly the seam that removes the continuity hypothesis.  Grepping for
`wildInertiaGroup` was the one-line check that would have refuted it.

THE PROOF, then, is the assembly of three inputs and no analysis:

1. *Wild inertia dies* — `exists_pow_eq_of_mem_wildInertiaGroup` at `n = N−1`
   (prime to the residue characteristic `N` since `0 < N − 1 < N`), applied to
   BOTH `λ` and `χ`.  So the pair character `F = (λ, χ)` on `I_N` kills `P_N`.
2. *Procyclicity* — `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker`
   applied to `F` corestricted to its (finite) range: one `σ₀ ∈ I_N` with
   `F τ = (F σ₀)^k` for every `τ ∈ I_N`, with `k : ℕ`.
3. *`χ(σ₀)` generates* — this is where leaf `A₀-1` above is consumed, and it is
   the ONLY place: surjectivity of `χ` on `I_N` plus step 2 makes every unit a
   power of `χ(res σ₀)`.  Take `a` with `χ(res σ₀)^a = λ(res σ₀)`; then for any
   `σ ∈ I_N`, `λ(res σ) = λ(res σ₀)^k = (χ(res σ₀)^k)^a = χ(res σ)^a`.

Note step 3 is what makes `A₀-1` genuinely necessary rather than decorative:
without surjectivity, `χ(res σ₀)` generates only the image of `χ` on `I_N`,
and `λ` could be nontrivial on inertia where `χ` is trivial. -/
theorem WeierstrassCurve.exists_isogenyTameExponentAt
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (_g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime)
    (_hg : addOrderOf _g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (_hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom _g =
        ((lam σ : ZMod N).val) • _g) :
    ∃ a : ℕ,
      ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ) =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ a := by
  classical
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set vN := hN.toHeightOneSpectrumRingOfIntegersRat with hvNdef
  set res := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ vN)) with hresdef
  set χ : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ :=
    @GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ with hχdef
  -- `#(ZMod N)ˣ = N − 1`
  have hcard : Nat.card (ZMod N)ˣ = N - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hN]
  -- `N − 1` is prime to the residue characteristic `N`, since `0 < N − 1 < N`
  have hNm1 : ((N - 1 : ℕ) : NumberField.RingOfIntegers ℚ) ∉ vN.asIdeal := by
    rw [hvNdef, Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal, map_natCast]
    intro h
    have h2 := hN.two_le
    have h3 : (N : ℤ) ≤ ((N - 1 : ℕ) : ℤ) := Int.le_of_dvd (by omega) h
    omega
  -- STEP 1.  ANY character into `(ZMod N)ˣ` kills the wild inertia, with NO
  -- continuity: every element of `P_N` is an `(N−1)`-st power INSIDE `P_N`
  -- (`P_N` is pro-`N` and `N ∤ N − 1`), and `(ZMod N)ˣ` has order `N − 1`.
  have hkill : ∀ (φ : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
      (w : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ vN)),
      w ∈ wildInertiaGroup vN → φ (res w) = 1 := by
    intro φ w hw
    obtain ⟨θ, -, hθw⟩ := exists_pow_eq_of_mem_wildInertiaGroup vN hNm1 hw
    rw [← hθw, map_pow, map_pow, ← hcard]
    exact pow_card_eq_one'
  -- the PAIR character `(λ, χ)` on the inertia group at `N`
  set F : localInertiaGroup vN →* (ZMod N)ˣ × (ZMod N)ˣ :=
    ((lam.comp res.toMonoidHom).prod (χ.comp res.toMonoidHom)).comp
      (localInertiaGroup vN).subtype with hFdef
  have hFapp : ∀ τ : localInertiaGroup vN,
      F τ = (lam (res (τ : _)), χ (res (τ : _))) := fun _ => rfl
  -- STEP 2.  The tame quotient is PROCYCLIC: `F` factors through a finite
  -- quotient of `I_N` that kills `P_N`, and every such quotient is cyclic.
  obtain ⟨σ₀, hσ₀⟩ := exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker vN
    F.rangeRestrict (MonoidHom.rangeRestrict_surjective F) (by
      intro π hπ
      apply Subtype.ext
      show F π = 1
      rw [hFapp, hkill lam _ hπ, hkill χ _ hπ]
      rfl)
  -- so every value of `F` on `I_N` is a NON-NEGATIVE power of `F σ₀`
  have hgen : ∀ τ : localInertiaGroup vN, ∃ k : ℕ, F σ₀ ^ k = F τ := by
    intro τ
    obtain ⟨k, hk⟩ := hσ₀ (F.rangeRestrict τ)
    exact ⟨k, congrArg Subtype.val hk⟩
  -- STEP 3.  `χ (res σ₀)` GENERATES `(ZMod N)ˣ` — this, and only this, is
  -- where leaf `A₀-1` (surjectivity of `χ` on `I_N`) is consumed.
  have hgenχ : ∀ u : (ZMod N)ˣ, ∃ k : ℕ, χ (res (σ₀ : _)) ^ k = u := by
    intro u
    obtain ⟨σ, hσ, hσu⟩ := exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq hN u
    obtain ⟨k, hk⟩ := hgen ⟨σ, hσ⟩
    rw [hFapp, hFapp] at hk
    refine ⟨k, ?_⟩
    have h2 : χ (res (σ₀ : _)) ^ k = χ (res σ) := congrArg Prod.snd hk
    rw [h2]
    exact hσu
  -- the exponent: `λ (res σ₀)` is a power of `χ (res σ₀)`
  obtain ⟨a, ha⟩ := hgenχ (lam (res (σ₀ : _)))
  refine ⟨a, fun σ hσ => ?_⟩
  obtain ⟨k, hk⟩ := hgen ⟨σ, hσ⟩
  rw [hFapp, hFapp] at hk
  have h1 : lam (res σ) = lam (res (σ₀ : _)) ^ k := (congrArg Prod.fst hk).symm
  have h2 : χ (res (σ₀ : _)) ^ k = χ (res σ) := congrArg Prod.snd hk
  show lam (res σ) = χ (res σ) ^ a
  calc lam (res σ) = lam (res (σ₀ : _)) ^ k := h1
    _ = (χ (res (σ₀ : _)) ^ a) ^ k := by rw [ha]
    _ = (χ (res (σ₀ : _)) ^ k) ^ a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = χ (res σ) ^ a := by rw [h2]

open Polynomial in
/-- **The order of a determinant-one endomorphism of a `2`-dimensional
`𝔽₅`-space divides `4`, `6` or `10`** (PROVEN 2026-07-30; the group-theoretic
core of `A₀-3a-i` below).

THE CONTENT is the element-order list of `SL₂(𝔽₅)`, obtained from
Cayley–Hamilton rather than from a `decide` over the `625` matrices.  In rank
two `f² = t·f − det f` (`GaloisRepresentation.charpoly_eq_quadratic_of_finrank_two`),
so with `det f = 1` the whole computation is the linear recursion
`fⁿ = a·f + b ↦ fⁿ⁺¹ = (a t + b)·f − a` run over the FIVE possible traces:

| `t`  | consequence      | order divides |
|------|------------------|---------------|
| `0`  | `f² = −1`        | `4`           |
| `1`  | `f³ = −1`        | `6`           |
| `2`  | `f⁵ = 1`         | `10`          |
| `3`  | `f⁵ = −1`        | `10`          |
| `4`  | `f³ = 1`         | `6`           |

The two `t = ±2` rows are the NON-SEMISIMPLE ones — there `(f ∓ 1)² = 0` and
`f` is `±`unipotent, of order `1`, `5`, `2` or `10` — which is exactly why the
`10` cannot be improved to `2` here and why the consumer must supply
`5 ∤ [I_N : J]` separately.  That separate hypothesis is `A₀-3a-i-c`
(`not_five_dvd_relIndex_of_padicValRat_j_nonneg`), and it is where potentially
good reduction enters; see its docstring. -/
theorem pow_eq_one_of_det_eq_one_finrank_two_five {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] [Module.Free (ZMod 5) V]
    (hfr : Module.finrank (ZMod 5) V = 2)
    (f : Module.End (ZMod 5) V) (hdet : LinearMap.det f = 1) :
    f ^ 4 = 1 ∨ f ^ 6 = 1 ∨ f ^ 10 = 1 := by
  haveI : Nontrivial (ZMod 5) := ⟨⟨0, 1, by decide⟩⟩
  set t := LinearMap.trace (ZMod 5) V f with ht
  -- Cayley–Hamilton in rank two: `f² = t·f − 1`
  have hCH : f ^ 2 = t • f - 1 := by
    have h := f.aeval_self_charpoly
    rw [GaloisRepresentation.charpoly_eq_quadratic_of_finrank_two hfr f, hdet, ← ht] at h
    simp only [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, one_smul] at h
    have h2 : f ^ 2 = (f ^ 2 - t • f + 1) + (t • f - 1) := by abel
    rw [h, zero_add] at h2
    exact h2
  -- one step of the linear recursion `fⁿ = a·f + b ↦ fⁿ⁺¹ = (a t + b)·f − a`
  have key : ∀ (a b c d : ZMod 5) (n : ℕ), f ^ n = a • f + b • 1 →
      c = a * t + b → d = -a → f ^ (n + 1) = c • f + d • 1 := by
    intro a b c d n hn hc hd
    rw [pow_succ, hn, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two, hCH,
      hc, hd]
    rw [smul_sub, smul_smul]
    module
  have hone : ∀ n : ℕ, f ^ n = (0 : ZMod 5) • f + (1 : ZMod 5) • 1 → f ^ n = 1 := by
    intro n hn; rw [hn, zero_smul, one_smul, zero_add]
  have hneg : ∀ n : ℕ, f ^ n = (0 : ZMod 5) • f + (-1 : ZMod 5) • 1 → f ^ (2 * n) = 1 := by
    intro n hn
    have h1 : f ^ n = -1 := by rw [hn, zero_smul, zero_add, neg_smul, one_smul]
    rw [two_mul, pow_add, h1, neg_mul_neg, one_mul]
  have e2 : f ^ 2 = t • f + (-1 : ZMod 5) • 1 := by rw [hCH, neg_smul, one_smul, sub_eq_add_neg]
  have htv : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
    have : ∀ s : ZMod 5, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by decide
    exact this t
  rcases htv with h | h | h | h | h
  · -- t = 0 : f² = −1
    left
    have h4 := hneg 2 (by rw [e2, h])
    rwa [show 2 * 2 = 4 by norm_num] at h4
  · -- t = 1 : f³ = −1
    right; left
    have e3 : f ^ 3 = (0 : ZMod 5) • f + (-1 : ZMod 5) • 1 :=
      key t (-1) 0 (-1) 2 e2 (by rw [h]; try decide) (by rw [h]; try decide)
    have h6 := hneg 3 e3
    rwa [show 2 * 3 = 6 by norm_num] at h6
  · -- t = 2 : f⁵ = 1
    right; right
    have e3 : f ^ 3 = (3 : ZMod 5) • f + (-2 : ZMod 5) • 1 :=
      key t (-1) 3 (-2) 2 e2 (by rw [h]; try decide) (by rw [h]; try decide)
    have e4 : f ^ 4 = (4 : ZMod 5) • f + (-3 : ZMod 5) • 1 :=
      key 3 (-2) 4 (-3) 3 e3 (by rw [h]; try decide) (by decide)
    have e5 : f ^ 5 = (0 : ZMod 5) • f + (1 : ZMod 5) • 1 :=
      key 4 (-3) 0 1 4 e4 (by rw [h]; try decide) (by decide)
    have h5 : f ^ 5 = 1 := hone 5 e5
    rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, h5, one_pow]
  · -- t = 3 : f⁵ = −1
    right; right
    have e3 : f ^ 3 = (3 : ZMod 5) • f + (2 : ZMod 5) • 1 :=
      key t (-1) 3 2 2 e2 (by rw [h]; try decide) (by rw [h]; try decide)
    have e4 : f ^ 4 = (1 : ZMod 5) • f + (2 : ZMod 5) • 1 :=
      key 3 2 1 2 3 e3 (by rw [h]; try decide) (by decide)
    have e5 : f ^ 5 = (0 : ZMod 5) • f + (-1 : ZMod 5) • 1 :=
      key 1 2 0 (-1) 4 e4 (by rw [h]; try decide) (by decide)
    have h10 := hneg 5 e5
    rwa [show 2 * 5 = 10 by norm_num] at h10
  · -- t = 4 : f³ = 1
    right; left
    have e3 : f ^ 3 = (0 : ZMod 5) • f + (1 : ZMod 5) • 1 :=
      key t (-1) 0 1 2 e2 (by rw [h]; try decide) (by rw [h]; try decide)
    have h3 : f ^ 3 = 1 := hone 3 e3
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]

/-- **THE BRIDGE from the three local inputs to the `{2,4,6}` bound** (PROVEN
2026-07-30): if the image of `A` under a representation on a `2`-dimensional
`𝔽₅`-space is CYCLIC generated by `ρ σ`, if `det (ρ σ) = 1`, and if `5` does
not divide `[A : J]` where `J = A ⊓ ker ρ`, then `[A : J]` divides one of
`2`, `4`, `6`.

Purely group theory over
`pow_eq_one_of_det_eq_one_finrank_two_five`: `[A : J]` is the index of the
kernel of `ρ|_A` corestricted to the UNITS of `Module.End` (`toHomUnits`, so
that `Subgroup.index_ker` applies), hence `Nat.card` of its range, hence
`orderOf (ρ σ)` once the range is `Subgroup.zpowers (ρ σ)`.  The `4/6/10`
trichotomy then gives `e ∣ 4`, `e ∣ 6` or `e ∣ 10`, and in the last case
`5 ∤ e` upgrades `e ∣ 2·5` to `e ∣ 2`.

Note `det` is needed at the GENERATOR ONLY — the whole image is then
determinant one automatically, which is why `A₀-3a-i-b` below is stated for a
single inertia element. -/
theorem relIndex_dvd_of_det_eq_one_five {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] [Module.Free (ZMod 5) V]
    (hfr : Module.finrank (ZMod 5) V = 2)
    {G : Type*} [Group G] (ρ : G →* Module.End (ZMod 5) V)
    {A J : Subgroup G} (hJ : J = A ⊓ ρ.ker)
    {σ : G} (hσA : σ ∈ A)
    (hcyc : ∀ τ ∈ A, ∃ k : ℕ, ρ τ = ρ σ ^ k)
    (hdet : LinearMap.det (ρ σ) = 1)
    (h5 : ¬ (5 ∣ J.relIndex A)) :
    ∃ n : ℕ, (n = 2 ∨ n = 4 ∨ n = 6) ∧ J.relIndex A ∣ n := by
  classical
  set φ : A →* (Module.End (ZMod 5) V)ˣ := ρ.toHomUnits.comp A.subtype with hφ
  have hφval : ∀ τ : A, ((φ τ : (Module.End (ZMod 5) V)ˣ) : Module.End (ZMod 5) V) = ρ τ := by
    intro τ; rfl
  set s : A := ⟨σ, hσA⟩ with hs
  have hkereq : φ.ker = J.subgroupOf A := by
    ext τ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hJ, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨τ.2, MonoidHom.mem_ker.mpr ?_⟩
      have := congrArg (fun u : (Module.End (ZMod 5) V)ˣ => (u : Module.End (ZMod 5) V)) h
      rw [hφval] at this
      simpa using this
    · intro h
      have h1 : ρ (τ : G) = 1 := MonoidHom.mem_ker.mp h.2
      refine Units.ext ?_
      rw [hφval]
      simpa using h1
  have hrange : φ.range = Subgroup.zpowers (φ s) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨τ, rfl⟩
      obtain ⟨k, hk⟩ := hcyc (τ : G) τ.2
      refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), Units.ext ?_⟩
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hφval, hφval, hk]
    · rw [Subgroup.zpowers_le]
      exact ⟨s, rfl⟩
  have he : J.relIndex A = orderOf (ρ σ) := by
    rw [Subgroup.relIndex, ← hkereq, Subgroup.index_ker, hrange, Nat.card_zpowers,
      ← orderOf_units, hφval s]
  obtain h4 | h6 | h10 := pow_eq_one_of_det_eq_one_finrank_two_five hfr (ρ σ) hdet
  · exact ⟨4, Or.inr (Or.inl rfl), by rw [he]; exact orderOf_dvd_of_pow_eq_one h4⟩
  · exact ⟨6, Or.inr (Or.inr rfl), by rw [he]; exact orderOf_dvd_of_pow_eq_one h6⟩
  · refine ⟨2, Or.inl rfl, ?_⟩
    have hd : J.relIndex A ∣ 2 * 5 := by
      rw [show 2 * 5 = 10 by norm_num, he]; exact orderOf_dvd_of_pow_eq_one h10
    have hcop : Nat.Coprime (J.relIndex A) 5 :=
      (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h5 |>.symm
    exact hcop.dvd_of_dvd_mul_right hd

/-- **`#GL₂(𝔽₅) = 480`** (PROVEN 2026-07-30), in the form the tameness argument
needs: the unit group of `Module.End (ZMod 5) V` for `V` of rank two.

Transport along `LinearMap.toMatrixAlgEquiv` (an `AlgEquiv`, so it induces a
`MulEquiv` on units) and then `Matrix.card_GL_field`, which gives
`∏ i : Fin 2, (5² − 5ⁱ) = 24 · 20`.  This is the ONLY reason
`19 < N` is needed for the cyclicity step below: `480 = 2⁵ · 3 · 5`, so a prime
`N > 19` cannot divide it, the wild inertia at `N` therefore has trivial image,
and the image of `I_N` is a quotient of the PROCYCLIC tame quotient.  At
`N = 2` or `3` that fails — `2, 3 ∣ 480` — and the image can be `Q₈` or
`SL₂(𝔽₃)`, which is precisely the falsity witness recorded for `hN19` in
`A₀-3a`'s docstring. -/
theorem card_units_end_finrank_two_five {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] [Module.Free (ZMod 5) V]
    (hfr : Module.finrank (ZMod 5) V = 2) :
    Nat.card (Module.End (ZMod 5) V)ˣ = 480 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  classical
  let b : Module.Basis (Fin 2) (ZMod 5) V := Module.finBasisOfFinrankEq (ZMod 5) V hfr
  have h1 : Nat.card (Module.End (ZMod 5) V)ˣ
      = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) :=
    Nat.card_congr
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toEquiv
  rw [h1, Matrix.card_GL_field 2, ZMod.card]
  norm_num [Fin.prod_univ_two]

/-- **The image of the inertia group at `N` in `Aut(E[5])` is CYCLIC, generated
by one element** (PROVEN 2026-07-30; `A₀-3a-i-a`, the tameness half of
`A₀-3a-i`).

**No curve geometry and no hypothesis on `j`** — this is true of the mod-`5`
representation of ANY elliptic curve over `ℚ` at any prime `N > 19`, good
reduction or not.  It is the exact analogue, one representation up, of the
`(λ, χ)` argument inside `exists_isogenyTameExponentAt` above, and it reuses
that proof's two inputs verbatim:

1. `exists_pow_eq_of_mem_wildInertiaGroup` at `n = #GL₂(𝔽₅) = 480`, prime to
   `N` because `480 = 2⁵ · 3 · 5` and `19 < N` — so the wild inertia `P_N`
   lands in the kernel (`pow_card_eq_one'`);
2. `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker` — procyclicity of
   the tame quotient — applied to the representation corestricted to its
   (finite) range.

The target has to be moved into the UNITS of `Module.End` before step 2, since
`Module.End` is only a monoid and the procyclicity lemma wants a group; that is
what `MonoidHom.toHomUnits` does. -/
theorem WeierstrassCurve.exists_localInertia_generator_galoisRep_five
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : N.Prime) (hN19 : 19 < N) :
    ∃ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
      ∀ τ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat, ∃ k : ℕ,
        E.galoisRep 5 Nat.prime_five.pos (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) τ) =
          E.galoisRep 5 Nat.prime_five.pos (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ k := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set vN := hN.toHeightOneSpectrumRingOfIntegersRat with hvN
  set res := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ vN)) with hres
  set V := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 5 with hV
  haveI hVfin : Finite V :=
    (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_finite (by norm_num)
  haveI : Finite (Module.End (ZMod 5) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 5) V => (f : V → V))
      (fun _ _ h => LinearMap.ext (congrFun h))
  have hfr : Module.finrank (ZMod 5) V = 2 := by
    have hrk := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
      (p := 5) (by norm_num)
    simpa using Module.finrank_eq_of_rank_eq hrk
  set ρ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ vN) →*
      Module.End (ZMod 5) V :=
    { toFun := fun τ => E.galoisRep 5 Nat.prime_five.pos (res τ)
      map_one' := by rw [map_one, map_one]; rfl
      map_mul' := fun a c => by rw [map_mul, map_mul]; rfl } with hρ
  set ρu := ρ.toHomUnits with hρu
  have hcard : Nat.card (Module.End (ZMod 5) V)ˣ = 480 := card_units_end_finrank_two_five hfr
  have hn480 : ((Nat.card (Module.End (ZMod 5) V)ˣ : ℕ) :
      NumberField.RingOfIntegers ℚ) ∉ vN.asIdeal := by
    rw [hcard, hvN, Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal, map_natCast]
    intro h
    have hd : N ∣ 480 := by exact_mod_cast h
    have h2 : N ∣ 2 ^ 5 * (3 * 5) := by norm_num at hd ⊢; exact hd
    rcases (Nat.Prime.dvd_mul hN).mp h2 with h' | h'
    · have h3 := hN.dvd_of_dvd_pow h'
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · rcases (Nat.Prime.dvd_mul hN).mp h' with h'' | h''
      · have := Nat.le_of_dvd (by norm_num) h''; omega
      · have := Nat.le_of_dvd (by norm_num) h''; omega
  have hkill : ∀ w : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ vN),
      w ∈ wildInertiaGroup vN → ρu w = 1 := by
    intro w hw
    obtain ⟨θ, -, hθ⟩ := exists_pow_eq_of_mem_wildInertiaGroup vN hn480 hw
    rw [← hθ, map_pow]
    exact pow_card_eq_one'
  set F : localInertiaGroup vN →* (Module.End (ZMod 5) V)ˣ :=
    ρu.comp (localInertiaGroup vN).subtype with hF
  obtain ⟨σ₀, hσ₀⟩ := exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker vN
    F.rangeRestrict (MonoidHom.rangeRestrict_surjective F)
    (fun π hπ => Subtype.ext (hkill _ hπ))
  refine ⟨(σ₀ : _), σ₀.2, fun τ hτ => ?_⟩
  obtain ⟨k, hk⟩ := hσ₀ (F.rangeRestrict ⟨τ, hτ⟩)
  refine ⟨k, ?_⟩
  have hk' : F σ₀ ^ k = F ⟨τ, hτ⟩ := congrArg Subtype.val hk
  have := congrArg (fun u : (Module.End (ZMod 5) V)ˣ => (u : Module.End (ZMod 5) V)) hk'
  rw [Units.val_pow_eq_pow_val] at this
  exact this.symm

/-- **`A₀-3a-i-b` — the mod-`5` representation has determinant `1` on the
inertia group at `N`** (sorry leaf, cut 2026-07-30; Silverman *AEC* III.8.3 and
the Weil pairing).

THE CONTENT IS THE WEIL PAIRING, and only that: `det ρ̄₅ = χ₅` globally on
`Γ ℚ` (the determinant of the mod-`m` representation is the mod-`m` cyclotomic
character, because `ρ̄` preserves the Weil pairing `e₅ : E[5] × E[5] → μ₅` up
to `χ₅`), together with `χ₅|_{I_N} = 1` because `ℚ_N(μ₅)/ℚ_N` is UNRAMIFIED for
`N ≠ 5`.

**The second half is ALREADY PROVEN IN THIS FILE**, as
`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne` — instantiate it
at `N := 5`, `q := N`, `hqN : N ≠ 5` (immediate from `19 < N`).  It is declared
FURTHER DOWN IN THIS FILE (grep the name; it sits just below `A₀-3b`), which is
the only reason this leaf is stated in the combined form rather than as the pure
identity `det ρ̄₅ = χ₅`.  A prover has two
honest routes: hoist that theorem above this point (it is self-contained), or
state and prove `det ρ̄₅ = χ₅` on all of `Γ ℚ` above this point and consume it
here — the second is strictly more useful, since the determinant identity is
wanted elsewhere too.  **Do not restate the unramifiedness half as a new leaf:
that would duplicate a proven declaration.**

`hN19` is used only through `N ≠ 5`; `hN` only to name the place.  Nothing here
needs `hj`, and nothing here is about good reduction — that is entirely
`A₀-3a-i-c`'s job. -/
theorem WeierstrassCurve.det_galoisRep_five_eq_one_of_mem_localInertiaGroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (τ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat))
    (hτ : τ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat) :
    LinearMap.det (E.galoisRep 5 Nat.prime_five.pos
      (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat)) τ)) = 1 :=
  sorry

/-- **`A₀-3a-i-c` — potentially good reduction: `5` does not divide the
semistability defect** (sorry leaf, cut 2026-07-30; Serre–Tate, Ann. of Math.
88 (1968), Thm. 2 and Cor. 3; Serre, Invent. Math. 15 (1972), §5.6).

**THIS IS WHERE `hj` LIVES, and it is the whole of the Serre–Tate input.**  The
other two inputs of `A₀-3a-i` (`-a` cyclicity, `-b` determinant one) are PROVEN
above and neither uses `hj`; the decomposition was chosen so that the one
remaining leaf is exactly the statement that fails on the refuting curve.

**The refuting witness of `A₀-3a` refutes precisely THIS leaf**, which is the
check that the cut is at the right place.  Take `N = 23` and
`E : y² = x³ − 2x² − 7x + 6` (type `I₁` at `23`, `j = 40000/23`, so
`v₂₃(j) = −1 < 0` and `hj` FAILS).  Over `ℚ₂₃^{nr}` this is the Tate curve with
`v₂₃(q) = 1`, and since `μ₅ ⊂ ℚ₂₃^{nr}` while `5 ∤ v₂₃(q)`, the extension
`ℚ₂₃^{nr}(E[5]) = ℚ₂₃^{nr}(q^{1/5})` is cyclic of degree exactly `5`.  So
`[I₂₃ : J] = 5` there: cyclicity still holds, the determinant is still `1`
(`E[5]` is `⟨μ₅, q^{1/5}⟩`, a `SL₂`-situation), and it is `5 ∤ [I_N : J]` that
fails.  Drop `hj` and this leaf is FALSE with that curve as witness.

THE ROUTE.  `0 ≤ v_N(j)` makes `E` potentially good; `J` acts trivially on
`E[5]` with `5 ≥ 3` prime to `N`, so by Serre–Tate the fixed field
`L = (ℚ̄_N)^J` is the minimal extension of `ℚ_N^{nr}` over which `E` acquires
good reduction, and `Φ = Gal(L/ℚ_N^{nr})` injects into `Aut(Ẽ)` for the good
reduction `Ẽ` over `𝔽̄_N`.  In residue characteristic `≥ 5` that group has
order `2`, `4` or `6`, so `[I_N : J] = #Φ` is prime to `5`.  (A prover who
carries out that argument gets `[I_N : J] ∣ {2,4,6}` directly and may find the
weaker `5 ∤ [I_N : J]` easier only in that it needs no automorphism-order
bookkeeping — but `#Aut(Ẽ) ∈ {2,4,6}` is not in mathlib, in `~/cs/FLT`, or in
this project, re-verified 2026-07-30, while
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`
(`Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`, PROVEN) gives exponent
`12`.  Exponent `12` plus the CYCLICITY already proven in `A₀-3a-i-a` gives
`#Φ = orderOf(generator) ∣ 12`, hence `5 ∤ #Φ`, with NO classification of
`Aut(Ẽ)` at all — note this route consumes `A₀-3a-i-a`, so a prover should cite
it rather than re-derive procyclicity.  That is the cheapest route to this leaf
and it is why this leaf, rather than the `{2,4,6}` bound, is what was cut.)

The good-model input still has to be built UPSTREAM: `PotentiallyGoodModel` is
declared ~1300 lines below and release-12 deliberately rejected hoisting it (see
`A₀-3a-i`'s docstring). -/
theorem WeierstrassCurve.not_five_dvd_relIndex_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hj : 0 ≤ padicValRat N E.j)
    {J : Subgroup (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat))}
    (hJle : J ≤ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat)
    (hJmem : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        (σ ∈ J ↔ ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P)) :
    ¬ (5 ∣ J.relIndex (localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat)) :=
  sorry

/-- **`A₀-3a-i` — Serre–Kraus: the semistability defect embeds in the
automorphism group of the reduction** (DECOMPOSED and PROVEN 2026-07-30 over
`A₀-3a-i-b` `det_galoisRep_five_eq_one_of_mem_localInertiaGroup` and
`A₀-3a-i-c` `not_five_dvd_relIndex_of_padicValRat_j_nonneg`, its third input
`A₀-3a-i-a` `exists_localInertia_generator_galoisRep_five` being PROVEN
outright; Serre–Tate, Ann. of Math.
88 (1968), Thm. 2 and its Cor. 3; Serre, Invent. Math. 15 (1972), §5.6 and
§1.12; Kraus, Manuscripta Math. 69 (1990), Thm. 2): the index `[I_N : J]` of
the pointwise stabiliser of `E[5]` in the inertia group at `N` DIVIDES the
order of the automorphism group of the reduced curve, which in residue
characteristic `≥ 5` is `2`, `4` or `6`.

This is the whole mathematical content of `A₀-3a`; what that leaf adds on top
is four lines of divisor arithmetic (`{d : d ∣ 2} ∪ {d : d ∣ 4} ∪ {d : d ∣ 6}
= {1,2,3,4,6}`), already written.

**Why the DIVISIBILITY form rather than the `{1,2,3,4,6}` list.**  What the
geometry produces is an EMBEDDING `Φ ↪ Aut(Ẽ)`, not an isomorphism, so the
index divides `#Aut(Ẽ)` and nothing sharper is available; and `#Aut(Ẽ)` is
`2` for `j̃ ∉ {0, 1728}`, `4` for `j̃ = 1728` and `6` for `j̃ = 0` (char `≥ 5`,
where the three cases are exactly the CM-by-`ℤ`, `ℤ[i]`, `ℤ[ζ₃]` cases).
Stating the leaf as "`∃ n ∈ {2,4,6}` with `[I_N : J] ∣ n`" keeps the trichotomy
of the `j`-invariant of the reduction visible to whoever proves it, and hands
the consumer a statement it can no longer weaken by accident.

**The route.**  `J` is pinned by `hJmem` to be exactly `{σ ∈ I_N : σ` acts
trivially on `E[5]}`; it is the kernel of a Galois action on a FINITE set, so
it is open in `I_N` and `e := [I_N : J]` is finite.  Put `L = (ℚ̄_N)^J`.  Since
`J ≤ I_N = Gal(ℚ̄_N/ℚ_N^{nr})` we get `L ⊇ ℚ_N^{nr}`, and `I_L = I_N ∩ J = J`,
so `[L : ℚ_N^{nr}] = [I_N : J] = e` and `L/ℚ_N^{nr}` is totally ramified (the
residue field of `ℚ_N^{nr}` is already algebraically closed).  By Serre–Tate's
criterion — this is where `0 ≤ v_N(j)` and `5 ≥ 3` prime to `N` enter — `L` is
the MINIMAL extension of `ℚ_N^{nr}` over which `E` acquires good reduction, so
`Φ := Gal(L/ℚ_N^{nr}) ≅ I_N/J` is the semistability defect; and `Φ` acts
faithfully on the reduction `Ẽ/𝔽̄_N`, i.e. `Φ ↪ Aut(Ẽ)`.

**`hj` IS LOAD-BEARING, and this leaf is FALSE without it — with an EXPLICIT
CURVE.**  Take `N = 23` and `E : y² = x³ − 2x² − 7x + 6`, which has
`v₂₃(Δ) = 1`, Kodaira type `I₁` at `23`, and `j = 40000/23`, so
`v₂₃(j) = −1 < 0` and `hj` fails (checked with PARI/GP: `elllocalred` returns
`kod = 5`, i.e. `I₁`; the witness was then read off by hand, the CAS being a
searcher and not a prover here).  Over `ℚ₂₃^{nr}` this is the Tate curve `E_q`
with `v₂₃(q) = v₂₃(1/j) = 1`.  Now `μ₅ ⊂ ℚ₂₃^{nr}` (the residue field is
`𝔽̄₂₃` and `5 ≠ 23`), so `ℚ₂₃^{nr}(E[5]) = ℚ₂₃^{nr}(q^{1/5})`, and since
`𝒪^×` is `5`-divisible there while `5 ∤ v₂₃(q) = 1`, that extension is cyclic
of degree exactly `5`.  Hence `J = I₂₃ ∩ ker(E[5])` has `[I₂₃ : J] = 5`, and
`5` divides none of `2`, `4`, `6`.  So the conclusion FAILS, not merely the
argument.

**CORRECTION (2026-07-29) to the counterexample recorded in `A₀-3a` below.**
That docstring offers a Tate curve with `5 ∣ v_N(q)` and says the leaf is
"FALSE without `hj`".  The example is real but it does NOT refute anything:
there `E[5]` is unramified, so `J = I_N`, `e = 1`, and `1 ∈ {1,2,3,4,6}` —
the conclusion HOLDS on that instance and only the identification of `J` with
the inertia of a good-reduction extension fails.  The refuting witness needs
`5 ∤ v_N(q)`, which is the curve above.  Both notes have been kept: the
`5 ∣ v_N(q)` curve is the right example for "the `E[m]` criterion has no
unconditional converse", and the `5 ∤ v_N(q)` curve is the right one for
"the statement is false".

**`hN19` IS LOAD-BEARING, and this leaf IS FALSE without it.**  At `N = 2` the
defect can be `Q₈` or `SL₂(𝔽₃)` (`#Aut(Ẽ) = 24`) and at `N = 3` dicyclic of
order `12`, so `e ∈ {8, 12, 24}` occurs and divides no element of `{2,4,6}`.
**This leaf may not be restated for a general prime.**

**Still needed to prove it, and a WARNING about the obvious route.**  The
Serre–Tate step wants a good MODEL over `𝒪_L`, i.e. the interface
`WeierstrassCurve.PotentiallyGoodModel`, which is declared ~1500 lines BELOW
this point.  **Do not plan on hoisting it**: that hoist was performed once, on
the 2026-07-28 branch `b23bab50` (which created
`Fermat/FLT/FreyCurve/PotentiallyGoodModel.lean`), and the release-12
integration REJECTED it and deleted the file — see the note on the
`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` import at the top of this
file, which records the rejection.  The earlier advice in `A₀-3`'s docstring
to "redo the hoist" is therefore STALE and was corrected on 2026-07-29.  A
prover should instead build the good-model input in an UPSTREAM module (which
is what the inertia-subgroup presentation of this cut was designed to leave
possible), or state and consume a local good-model existence lemma above this
point.

**WHAT IS LEFT HERE (2026-07-30): NOTHING — this leaf is now GLUE.**  The
mathematics has been split into three inputs, in ascending order of depth, and
the first is proven:

* `A₀-3a-i-a` `exists_localInertia_generator_galoisRep_five` — **PROVEN**: the
  image of `I_N` in `Aut(E[5])` is cyclic, generated by one `σ₀`.  Pure tame
  inertia: `#GL₂(𝔽₅) = 480 = 2⁵·3·5` is prime to `N > 19`, so wild inertia dies
  and the image is a quotient of the procyclic tame quotient.  This is where
  `hN19` is consumed, and it is exactly why the leaf is false at `N = 2, 3`.
* `A₀-3a-i-b` `det_galoisRep_five_eq_one_of_mem_localInertiaGroup` — the Weil
  pairing: `det ρ̄₅ = χ₅`, trivial on `I_N` since `N ≠ 5`.  Half of it is
  already proven below in this file; see its docstring.
* `A₀-3a-i-c` `not_five_dvd_relIndex_of_padicValRat_j_nonneg` — **the whole of
  the Serre–Tate input, and the only consumer of `hj`.**  The refuting curve
  above (`N = 23`, `y² = x³ − 2x² − 7x + 6`, where `[I₂₃ : J] = 5`) refutes
  THIS statement and no other, which is the check that the cut is in the right
  place.

The `{2,4,6}` arithmetic is then `pow_eq_one_of_det_eq_one_finrank_two_five`
(Cayley–Hamilton over the five traces in `𝔽₅`) plumbed by
`relIndex_dvd_of_det_eq_one_five`; both are PROVEN above.  Note the `{2,4,6}`
bound is NOT `#Aut(Ẽ)`-shaped in this route — it comes from the element orders
of `SL₂(𝔽₅)`, which are `1,2,3,4,5,6,10`, with `5` and `10` excluded exactly by
`A₀-3a-i-c`.  So Raynaud-free, Néron-model-free, and no classification of
`Aut(Ẽ)` is needed anywhere. -/
theorem WeierstrassCurve.exists_relIndex_dvd_reductionAutOrder_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hj : 0 ≤ padicValRat N E.j)
    {J : Subgroup (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat))}
    (hJle : J ≤ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat)
    (hJmem : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        (σ ∈ J ↔ ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P)) :
    ∃ n : ℕ, (n = 2 ∨ n = 4 ∨ n = 6) ∧
      J.relIndex (localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat) ∣ n := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set res := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hN.toHeightOneSpectrumRingOfIntegersRat)) with hres
  set V := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 5 with hV
  haveI hVfin : Finite V :=
    (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_finite (by norm_num)
  haveI : Finite (Module.End (ZMod 5) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 5) V => (f : V → V))
      (fun _ _ h => LinearMap.ext (congrFun h))
  have hfr : Module.finrank (ZMod 5) V = 2 := by
    have hrk := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
      (p := 5) (by norm_num)
    simpa using Module.finrank_eq_of_rank_eq hrk
  set ρ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat) →*
      Module.End (ZMod 5) V :=
    { toFun := fun τ => E.galoisRep 5 Nat.prime_five.pos (res τ)
      map_one' := by rw [map_one, map_one]; rfl
      map_mul' := fun a c => by rw [map_mul, map_mul]; rfl } with hρ
  -- the value of `ρ` on a torsion point IS `Affine.Point.map`
  have hval : ∀ (τ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat))
      (P : (E⁄(AlgebraicClosure ℚ)).Point)
      (hP : P ∈ Submodule.torsionBy ℤ ((E⁄(AlgebraicClosure ℚ)).Point) ((5 : ℕ) : ℤ)),
      (ρ τ (⟨P, hP⟩ : V)).val
        = Affine.Point.map
            ((res τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
            P := fun _ _ _ => rfl
  -- `J` IS the pointwise stabiliser inside `I_N`
  have hJeq : J = localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat ⊓ ρ.ker := by
    refine le_antisymm ?_ ?_
    · intro τ hτ
      refine Subgroup.mem_inf.mpr ⟨hJle hτ, MonoidHom.mem_ker.mpr ?_⟩
      have h := (hJmem τ (hJle hτ)).mp hτ
      refine LinearMap.ext (fun x : V => Subtype.ext ?_)
      have h5 : (5 : ℕ) • x.val = 0 := by
        have h2 : ((5 : ℕ) : ℤ) • x.val = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp x.2
        rwa [natCast_zsmul] at h2
      exact (hval τ x.val x.2).trans (h x.val h5)
    · intro τ hτ
      obtain ⟨hτI, hτk⟩ := Subgroup.mem_inf.mp hτ
      refine (hJmem τ hτI).mpr fun P hP => ?_
      have h1 : ρ τ = 1 := MonoidHom.mem_ker.mp hτk
      have hmem : P ∈ Submodule.torsionBy ℤ ((E⁄(AlgebraicClosure ℚ)).Point) ((5 : ℕ) : ℤ) := by
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
        exact hP
      have hx : ρ τ (⟨P, hmem⟩ : V) = (⟨P, hmem⟩ : V) := by rw [h1]; rfl
      have h3 : (ρ τ (⟨P, hmem⟩ : V)).val = P := congrArg (fun y : V => y.val) hx
      exact (hval τ P hmem).symm.trans h3
  obtain ⟨σ₀, hσ₀mem, hcyc⟩ :=
    E.exists_localInertia_generator_galoisRep_five hN hN19
  exact relIndex_dvd_of_det_eq_one_five hfr ρ hJeq hσ₀mem (fun τ hτ => hcyc τ hτ)
    (E.det_galoisRep_five_eq_one_of_mem_localInertiaGroup hN hN19 σ₀ hσ₀mem)
    (E.not_five_dvd_relIndex_of_padicValRat_j_nonneg hN hN19 hj hJle hJmem)

/-- **`A₀-3a` — Serre's semistability defect at residue characteristic `≥ 5`**
(DECOMPOSED 2026-07-29 over `A₀-3a-i`
`exists_relIndex_dvd_reductionAutOrder_of_padicValRat_j_nonneg`, which now
carries all of its mathematics; Serre, Invent. Math. 15 (1972), §5.6, and
Serre–Tate, Ann. of Math. 88 (1968), §2, Cor. 3; Kraus, Manuscripta Math. 69
(1990)): at
potentially good reduction the inertia group at `N` acts on the `5`-torsion
through a cyclic quotient of order `e ∈ {1,2,3,4,6}`.

**The extension is presented by its INERTIA SUBGROUP, not by a model.**  `J`
is the subgroup of `I_N` acting trivially on `E[5]`; `hJmem` pins it as
exactly that set (`hJle` bounds it inside `I_N`, and the `iff` fixes
membership for every `σ ∈ I_N`), so neither `J` nor `e` can be chosen freely
— `e` is forced to be the order of the image of `I_N` in `Aut(E[5])`.  The
fixed field `L = (ℚ̄_N)^J` then satisfies `L ⊇ ℚ_N^{nr}` and
`[L : ℚ_N^{nr}] = e`, and `L` is the minimal extension of `ℚ_N^{nr}` over
which `E` acquires good reduction — i.e. `Φ = Gal(L/ℚ_N^{nr})` is the
semistability defect.  Presenting the extension this way is what lets this
leaf and `A₀-3b` be stated ABOVE `WeierstrassCurve.PotentiallyGoodModel`,
which is declared ~1500 lines below in this file.

**`hj` IS LOAD-BEARING, and the leaf is FALSE without it.**  Two different
Tate curves are needed to say this precisely, and an earlier version of this
paragraph conflated them (corrected 2026-07-29; the full discussion is in
`A₀-3a-i`'s docstring above).

* *The `E[m]` criterion has no unconditional converse*: a Tate curve
  `E_q/ℚ_N^{nr}` with `5 ∣ v_N(q)` has `E[5]` UNRAMIFIED — `μ_5 ⊂ ℚ_N^{nr}`
  because `5 ≠ N`, and `q^{1/5} ∈ ℚ_N^{nr}` because the residue field is
  algebraically closed, so every unit is a fifth power — while `E` has
  multiplicative, not good, reduction.  There `J = I_N` and `e = 1`, and `E`
  acquires good reduction over no finite extension at all.  So "trivial action
  on `E[5]`" identifies the good-reduction extension only once `0 ≤ v_N(j)` is
  known.  **This instance does NOT refute the statement**: `e = 1` lies in
  `{1,2,3,4,6}`, so the conclusion holds there and only the ARGUMENT fails.
* *The statement itself is false without `hj`*: take `5 ∤ v_N(q)` instead.
  Concretely `N = 23` and `E : y² = x³ − 2x² − 7x + 6` (type `I₁` at `23`,
  `j = 40000/23`, so `v₂₃(q) = 1`); then `ℚ₂₃^{nr}(E[5]) = ℚ₂₃^{nr}(q^{1/5})`
  is cyclic of degree `5`, giving `e = 5 ∉ {1,2,3,4,6}`.

Likewise `19 < N`
is used for `N ≥ 5`: at `q = 2` the defect can be `Q₈` (`e = 8`) or
`SL₂(𝔽₃)` (`e = 24`) and at `q = 3` dicyclic of order `12`, so **this leaf
may not be restated for a general prime**.

`5` is not special: any `m ≥ 3` prime to `N` gives the same `e`, because for
potentially good reduction `ℚ_N^{nr}(E[m])` is independent of such an `m`
(Serre–Tate, Cor. 3 to Thm. 2).  A prover may substitute `3` freely.  What
`m ≥ 3` buys is that `Aut(E)` acts faithfully on `E[m]`, which is what makes
`Φ ↪ Aut(E[m])` and hence pins `e`.

**WHAT IS LEFT HERE (2026-07-29).**  The existential is now WITNESSED: `J` is
built as the honest pointwise stabiliser
`{σ | ∀ P ∈ E[5], (ρ σ) • P = P} ⊓ I_N` — a subgroup because the Galois action
on `(E⁄ℚ̄).Point` is a `DistribMulAction`
(`WeierstrassCurve.galoisRepresentation`) and `ρ` is a monoid hom — and `e` is
taken to be `J.relIndex I_N`, so `hJle`, `hJmem` and `hindex` hold by
construction.  The only remaining input is the bound, isolated as `A₀-3a-i`
above.  Two consequences worth recording: nothing below may read `J` as
anything other than that stabiliser, and the `hindex` clause is now `rfl`, so
it can never be satisfied by a different `e`. -/
theorem WeierstrassCurve.exists_semistabilityDefect_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hj : 0 ≤ padicValRat N E.j) :
    ∃ (e : ℕ) (J : Subgroup (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat))),
      (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧
      J ≤ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat ∧
      (∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        (σ ∈ J ↔ ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P)) ∧
      J.relIndex (localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat) = e := by
  classical
  -- the decomposition-group map into `Γ ℚ`, with its target written as an
  -- explicit `AlgEquiv` type so that the Galois action on points is FOUND by
  -- instance search (`Field.absoluteGaloisGroup` is reducible, but typeclass
  -- resolution does not unfold it)
  set ρ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat) →*
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
  -- the pointwise stabiliser of `E[5]`, a subgroup of the LOCAL Galois group
  set Stab : Subgroup (Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat)) :=
    { carrier := {σ | ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
        ρ σ • P = P}
      one_mem' := by
        intro P _
        rw [map_one]
        exact one_smul _ _
      mul_mem' := by
        intro x y hx hy P hP
        rw [map_mul, mul_smul, hy P hP, hx P hP]
      inv_mem' := by
        intro x hx P hP
        rw [map_inv]
        exact inv_smul_eq_iff.mpr (hx P hP).symm }
  -- the `DistribMulAction` smul IS `Affine.Point.map` of the coerced `AlgHom`
  have hsmul : ∀ (σ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hN.toHeightOneSpectrumRingOfIntegersRat))
      (P : (E⁄(AlgebraicClosure ℚ)).Point),
      ρ σ • P =
        Affine.Point.map
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P :=
    fun _ _ => rfl
  have hmem : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
      (σ ∈ Stab ⊓ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat ↔
        ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P) := by
    intro σ hσ
    constructor
    · intro hσJ P hP
      exact (hsmul σ P) ▸ hσJ.1 P hP
    · intro h
      exact ⟨fun P hP => (hsmul σ P).trans (h P hP), hσ⟩
  -- `A₀-3a-i`: the index divides `#Aut(Ẽ) ∈ {2,4,6}`
  obtain ⟨n, hn, hdvd⟩ :=
    E.exists_relIndex_dvd_reductionAutOrder_of_padicValRat_j_nonneg hN hN19 hj
      (J := Stab ⊓ _) inf_le_right hmem
  -- `{d : d ∣ 2} ∪ {d : d ∣ 4} ∪ {d : d ∣ 6} = {1,2,3,4,6}`
  have key : ∀ m k : ℕ, (k = 2 ∨ k = 4 ∨ k = 6) → m ∣ k →
      (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6) := by
    intro m k hk hd
    rcases hk with rfl | rfl | rfl <;>
      · have hle := Nat.le_of_dvd (by norm_num) hd
        interval_cases m <;> revert hd <;> decide
  exact ⟨_, Stab ⊓ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
    key _ n hn hdvd, inf_le_right, hmem, rfl⟩

/-- **`A₀-3b-i` — the level-one fundamental character of the good-reduction
extension, with Raynaud's exponent attached** (sorry leaf; Raynaud, Bull. SMF
102 (1974), Cor. 3.4.4 and §1.2; Serre, Invent. Math. 15 (1972), §1.7 and
Prop. 9): over `L = (ℚ̄_N)^J` — whose inertia group is `J` and whose absolute
ramification index is `e` — there is a SURJECTIVE character
`ψ : J → 𝔽_N^×` (the level-one fundamental character `ψ_L`) with
`χ|_J = ψ^e` and `λ|_J = ψ^r` for some `r ≤ e`.

This is the whole of the local input of `A₀-3b`; what that leaf adds on top is
the exponent arithmetic that converts the two identities into the congruence
`a·e ≡ r (mod N−1)`, already written.

**The two clauses, and why the argument needs each.**

* `χ|_J = ψ^e`.  The mod-`N` cyclotomic character restricted to `I_{ℚ_N}` IS
  the level-one fundamental character `ψ_{ℚ_N}` (the extension
  `ℚ_N(μ_N)/ℚ_N` is totally tamely ramified of degree `N − 1`), and for a
  subextension of ramification index `e` one has `ψ_{ℚ_N}|_{I_L} = ψ_L^e`.
  Here `e(L/ℚ_N) = e(L/ℚ_N^{nr}) = [I_N : J] = e` because `ℚ_N^{nr}/ℚ_N` is
  unramified — this is exactly what `hJle` and `hindex` are for.  No curve
  data is used in this clause.
* `λ|_J = ψ^r` with `r ≤ e`.  This is Raynaud.  `E` acquires good reduction
  over `L` (`hj` makes it potentially good, `hJmem` says `J` acts trivially on
  `E[5]`, `5 ≥ 3` is prime to `N`); the Galois-stable order-`N` subgroup
  `⟨g⟩ ⊆ E[N]` (which is what `hg` and `hlam` say) has a schematic closure in
  the Néron model over `𝒪_L`, a finite flat group scheme of order `N`; and
  `e ≤ 6 < N − 1` (from `he` and `hN19`) puts that group scheme in the range
  of Raynaud's classification, whose conclusion is precisely that the
  character of its generic fibre is `ψ_L^r` with `0 ≤ r ≤ e`.

**Surjectivity of `ψ` is not decoration — it is the whole force of the leaf.**
`ψ_L` is surjective onto `𝔽_N^×` because the residue field of `L` is
algebraically closed, so the tame quotient of `I_L` surjects onto `μ_{N−1}`.
Without it the pair `(ψ, r)` could be taken trivial and the leaf would be
satisfied by `ψ = 1, r = 0` whenever `λ|_J = χ|_J = 1`, and the consumer's
congruence would not follow.

**AXIS SEARCHED AND CLOSED: `(ψ, r)` MUST STAY IN ONE EXISTENTIAL.**  The
tempting split — one leaf producing `ψ` surjective with `χ|_J = ψ^e` (pure
tame-character theory, no curve), a second taking such a `ψ` as a HYPOTHESIS
and producing `r ≤ e` with `λ|_J = ψ^r` (Raynaud) — does not work, because
those two hypotheses do NOT pin `ψ` to `ψ_L`.  Witness: `N = 29`, `e = 4`,
`ψ' = ψ_L^15`.  Then `gcd(15, 28) = 1` so `ψ'` is surjective, and
`ψ'^4 = ψ_L^{60} = ψ_L^4 = χ|_J` since `60 ≡ 4 (mod 28)`; but `ψ'^r` for
`r ≤ 4` runs through `ψ_L^0, ψ_L^{15}, ψ_L^2, ψ_L^{17}, ψ_L^4` only, so if
`λ|_J = ψ_L^1` or `ψ_L^3` the second leaf is unsatisfiable.  Those two values
of `r` are excluded only by the parity clause ("`e` even ⟹ `r` even"), which
this cut deliberately does not assert at this level (it is derived downstream,
in `exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg`).  Keeping
both clauses under one `∃ ψ` lets the prover choose `ψ = ψ_L` and removes the
dependency entirely. -/
theorem WeierstrassCurve.exists_fundamentalCharacter_of_semistabilityDefect
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hj : 0 ≤ padicValRat N E.j)
    {e : ℕ}
    {J : Subgroup (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat))}
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (hJle : J ≤ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat)
    (hJmem : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        (σ ∈ J ↔ ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P))
    (hindex : J.relIndex (localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat) = e) :
    ∃ (ψ : J →* (ZMod N)ˣ) (r : ℕ), r ≤ e ∧ Function.Surjective ψ ∧
      (∀ σ : J, lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hN.toHeightOneSpectrumRingOfIntegersRat)) (σ : _)) = ψ σ ^ r) ∧
      (∀ σ : J, (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
          (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) (σ : _))) = ψ σ ^ e) :=
  sorry

/-- **`A₀-3b` — Raynaud's exponent, as a congruence between tame exponents**
(DECOMPOSED 2026-07-29 over `A₀-3b-i`
`exists_fundamentalCharacter_of_semistabilityDefect`, which now carries all of
its mathematics; Raynaud, Bull. SMF 102 (1974), Cor. 3.4.4; Serre, Invent.
Math. 15 (1972), §1.7 and Prop. 5): given the semistability-defect datum
`(e, J)` of `A₀-3a` and the tame exponent `a` of `A₀-2`, there is `r ≤ e` with
`a·e ≡ r (mod N−1)`.

**WHAT IS LEFT HERE (2026-07-29): steps 1–3 below are `A₀-3b-i`; step 4 is the
proof written here.**  `A₀-3b-i` delivers `ψ = ψ_L` surjective with
`λ|_J = ψ^r` (`r ≤ e`) and `χ|_J = ψ^e`.  Evaluating both at a `σ ∈ J` with
`ψ(σ)` a GENERATOR of `(ZMod N)ˣ` — which surjectivity supplies — turns
`λ(σ) = χ(σ)^a` into `ψ(σ)^r = ψ(σ)^{e·a}`, and `orderOf ψ(σ) = N − 1` gives
the congruence.  Note it is `hJle` that lets `ha` (a statement about `I_N`) be
read at `σ ∈ J` at all.

**Why the conclusion is a CONGRUENCE and not a character identity.**  This is
the whole of Raynaud's input, transported once and for all into arithmetic.
Write `L = (ℚ̄_N)^J`, so `L ⊇ ℚ_N^{nr}`, `I_L = J`, and the absolute
ramification index of `L` is `e(L/ℚ_N) = e(L/ℚ_N^{nr}) = e` because
`ℚ_N^{nr}/ℚ_N` is unramified.  The steps are:

1. `E` has good reduction over `L`.  `J` acts trivially on `E[5]` (`hJmem`),
   `5 ≥ 3` is prime to `N`, and `0 ≤ v_N(j)` makes `E` potentially good —
   all three are needed; see the falsity note in `A₀-3a` for why `hj` cannot
   be dropped here either.
2. The Galois-stable order-`N` subgroup `⟨g⟩ ⊆ E[N]` (this is what `hlam`
   and `hg` say) has a schematic closure in the `N`-torsion of the Néron
   model of `E` over `𝒪_L`, a finite flat group scheme `G/𝒪_L` of order `N`.
3. `e ≤ 6 < N − 1` since `19 < N`, so **Raynaud's classification applies**
   and gives `λ|_{I_L} = ψ_L^r` with `0 ≤ r ≤ e`, where `ψ_L : I_L → 𝔽_N^×`
   is the level-one fundamental character of `L`.
4. `χ|_{I_L} = ψ_L^e`, again because `e(L/ℚ_N) = e`.  With `λ|_{I_N} = χ^a`
   (hypothesis `ha`, i.e. leaf `A₀-2`) this reads `ψ_L^{a·e} = ψ_L^{r}` on
   `I_L`, and `ψ_L` has EXACT order `N − 1`, so `a·e ≡ r (mod N−1)`.

Step 4 is why the congruence, rather than the identity `λ^e = χ^r`, is the
right interface: the identity on `I_N` follows from the congruence by pure
exponent arithmetic (done in the glue of `A₀-3`, where it costs four lines),
whereas the congruence is exactly what the local theory produces.

Every hypothesis is load-bearing.  Dropping `hg`/`hlam` removes the group
scheme (step 2) and the statement becomes false for a general character —
`a` would be unconstrained.  Dropping `he` removes `e < N − 1` and Raynaud's
hypothesis with it.  Dropping `hJmem`/`hindex` leaves `e` unrelated to `L`
and breaks step 4. -/
theorem WeierstrassCurve.exists_raynaudExponent_modEq_of_semistabilityDefect
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hj : 0 ≤ padicValRat N E.j)
    {a e : ℕ}
    (ha : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hN.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
          (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ a)
    {J : Subgroup (Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hN.toHeightOneSpectrumRingOfIntegersRat))}
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6)
    (hJle : J ≤ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat)
    (hJmem : ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        (σ ∈ J ↔ ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, (5 : ℕ) • P = 0 →
          Affine.Point.map
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P))
    (hindex : J.relIndex (localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat) = e) :
    ∃ r : ℕ, r ≤ e ∧ a * e ≡ r [MOD N - 1] := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  -- `A₀-3b-i`: the level-one fundamental character of `L = (ℚ̄_N)^J`
  obtain ⟨ψ, r, hre, hsurj, hψlam, hψχ⟩ :=
    E.exists_fundamentalCharacter_of_semistabilityDefect g hN hN19 hg lam hlam hj
      he hJle hJmem hindex
  refine ⟨r, hre, ?_⟩
  -- read the two identities at a `σ ∈ J` on which `ψ` takes a GENERATOR of
  -- `(ZMod N)ˣ`; this is where surjectivity of `ψ` is consumed
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod N)ˣ)
  have hcard : Nat.card (ZMod N)ˣ = N - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hN]
  rw [hcard] at hu
  obtain ⟨σ, hσ⟩ := hsurj u
  -- `u ^ r = λ(σ) = χ(σ) ^ a = u ^ (e * a)`
  have h3 := ha (σ : _) (hJle σ.2)
  rw [hψlam σ, hψχ σ, hσ, ← pow_mul] at h3
  have h4 : r ≡ e * a [MOD N - 1] := by
    have h5 := pow_eq_pow_iff_modEq.mp h3
    rwa [hu] at h5
  rw [Nat.mul_comm a e]
  exact h4.symm

/-- **`A₀-3` — the semistability defect and Raynaud's exponent at `N`**
(DECOMPOSED and PROVEN 2026-07-28 from `A₀-2`, `A₀-3a` and `A₀-3b`; Serre,
Invent. Math. 15 (1972), Prop. 5 and §5.4; Raynaud, Bull. SMF 102 (1974),
Cor. 3.4.4): at potentially good reduction there are a
ramification index `e ∈ {1,2,3,4,6}` and an exponent `r ≤ e` with
`λ^e = χ^r` on the inertia group at `N`.

This WAS the deep leaf of the whole cluster; the depth now sits in `A₀-3a`
(Serre's `e ∈ {1,2,3,4,6}` at residue characteristic `≥ 5`) and `A₀-3b`
(Raynaud's classification), and what is left here is exponent arithmetic.
The cut runs along the semistability-defect extension `L/ℚ_N^{nr}`,
presented by its INERTIA SUBGROUP `J = I_L ≤ I_N` — the subgroup acting
trivially on `E[5]` — rather than by a good model.  That presentation is
what lets both halves be stated here at all:
`WeierstrassCurve.PotentiallyGoodModel`, the natural alternative interface,
is declared ~1500 lines BELOW this point and Lean has no forward references.

The three-line assembly:

* `A₀-2` gives `a` with `λ = χ^a` on `I_N`;
* `A₀-3a` gives `e ∈ {1,2,3,4,6}` and the pinned `J` with `[I_N : J] = e`;
* `A₀-3b` gives `r ≤ e` with `a·e ≡ r (mod N−1)`;
* and `χ(σ)^{N−1} = 1` for every `σ` — `(ZMod N)ˣ` has order `N − 1` — turns
  that congruence into `λ(σ)^e = χ(σ)^{a·e} = χ(σ)^r`, which is the
  conclusion.

The congruence, not the character identity, is the right interface to
Raynaud: it is what the local theory literally produces (the level-one
fundamental character `ψ_L` of `L` has exact order `N − 1`, and both
`λ|_{I_L}` and `χ|_{I_L}` are powers of it), and the last step above is the
only place the identity is needed.  See `A₀-3b`'s docstring for the four
steps of the transport, and `A₀-3a`'s for why `0 ≤ v_N(j)` and `19 < N` are
both load-bearing rather than decorative.

WHAT THIS LEAF DELIBERATELY DOES NOT ASSERT.  Serre's statement also carries
`r` even when `e` is even, and the `(e,r) = (4,2) ⟹ N ≡ 3 (mod 4)` side
condition.  Both are CONSEQUENCES of the congruence `a·e ≡ r (mod N−1)` that
`A₀-1` and `A₀-2` supply, and both are proven in the glue of
`exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg` below — see
the section note above this block for the two-line derivations.  Asserting
them here would be asking a prover for content the arithmetic already gives.

FAITHFULNESS CHECK.  Combining this leaf with the derived parity clause gives
`12r/e ∈ {0, 4, 6, 8, 12}` and nothing else, which is exactly Serre's list of
possible exponents in `λ¹² = χ^{12r/e}` at potentially good reduction.  That
the cut reproduces the classical list is the evidence that no clause was lost
in it.

THE NEXT CUTS (updated 2026-07-29: `A₀-3a` and `A₀-3b` are themselves now
DECOMPOSED and PROVEN over `A₀-3a-i`
`exists_relIndex_dvd_reductionAutOrder_of_padicValRat_j_nonneg` and `A₀-3b-i`
`exists_fundamentalCharacter_of_semistabilityDefect`; those two are the live
leaves of this cluster and their docstrings are the specifications).  Neither
Raynaud's classification nor the `{1,2,3,4,6}` bound is in mathlib, in
`~/cs/FLT`, or in this project — RE-VERIFIED by grep on 2026-07-29, the
mathlib hits for "Raynaud" are all fibered-category/étale-descent material —
so both remain theory builds.

* `A₀-3a-i` factors through `WeierstrassCurve.PotentiallyGoodModel` (declared
  ~1500 lines BELOW in this file; its producer from `0 ≤ v_N(j)` is the
  already-open leaf `exists_potentiallyGoodModel_of_jIntegral`, stated for
  `q ≠ 2`).  **DO NOT reach for it by hoisting that block upstream, and note
  that BOTH earlier notes here were stale in opposite directions.**  The hoist
  was attempted in `b23bab50`, which did create
  `Fermat/FLT/FreyCurve/PotentiallyGoodModel.lean` — but it was not "lost in a
  later merge" and must not be redone: the release-12 integration REJECTED it
  and deleted the file deliberately (see the note on the
  `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` import at the top of this
  file), and the merger rejected the same hoist again in `50a73c66` for a
  recorded, still-current reason: two other branches had restructured the same
  region concurrently, so applying the deletion side lost twenty declarations
  that had grown inside it and produced seven duplicates against
  `EllipticCurve/TorsionReduction.lean`, into which part of the block had been
  relocated.  A relocation is mergeable only while its region is quiet, and
  this region is not.  No branch head carries the file.  Build the good-model
  input in an UPSTREAM module instead — which is what the inertia-subgroup
  presentation of this cut (`A₀-3a`) exists to make possible.  What remains
  after that is Serre §5.6 / Kraus: `Φ ↪ Aut(Ẽ)` over the residue field, and
  `Aut` of an elliptic curve in characteristic `≥ 5` is cyclic of order `2`,
  `4` or `6`, whence `[I_N : J] ∣ #Aut(Ẽ) ∈ {2,4,6}` and so `e ∈ {1,2,3,4,6}`.
* `A₀-3b-i` needs two independent things: tame-character theory over `L`
  (`χ|_{I_L} = ψ_L^{e(L)}` with `ψ_L` surjective), and finite flat group
  schemes of order `N` over a base of absolute ramification `e < N − 1`, which
  is a genuinely new theory here.  The `Fermat/FLT/HopfAlgebra` cluster
  (Cartier duality) is the nearest existing material.  They may NOT be split
  into two leaves — see the counterexample recorded in `A₀-3b-i`'s
  docstring. -/
theorem WeierstrassCurve.exists_isogenyRaynaudExponentAt_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hj : 0 ≤ padicValRat N E.j) :
    ∃ e r : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧ r ≤ e ∧
      ∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ e =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ r := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  -- `A₀-2`: the tame exponent of `λ` at `N`
  obtain ⟨a, ha⟩ := E.exists_isogenyTameExponentAt g hN hg lam hlam
  -- `A₀-3a`: Serre's semistability defect, as the inertia subgroup `J = I_L`
  -- of the good-reduction extension together with its index `e`
  obtain ⟨e, J, he, hJle, hJmem, hindex⟩ :=
    E.exists_semistabilityDefect_of_padicValRat_j_nonneg hN hN19 hj
  -- `A₀-3b`: Raynaud's exponent, delivered as a congruence mod `N − 1`
  obtain ⟨r, hre, hmod⟩ :=
    E.exists_raynaudExponent_modEq_of_semistabilityDefect g hN hN19 hg lam hlam hj
      ha he hJle hJmem hindex
  refine ⟨e, r, he, hre, ?_⟩
  intro σ hσ
  -- `λ(σ)^e = (χ(σ)^a)^e = χ(σ)^{a·e}`, and `a·e ≡ r` modulo the order of
  -- `χ(σ)`, which divides `#(ZMod N)ˣ = N − 1`
  rw [ha σ hσ, ← pow_mul]
  refine pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd ?_ hmod)
  have hcard : Fintype.card (ZMod N)ˣ = N - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hN]
  exact hcard ▸ orderOf_dvd_card

/-- **`A₀` — Serre–Raynaud local data at `N`, POTENTIALLY GOOD case**
(DECOMPOSED and PROVEN 2026-07-27 from `A₀-1`, `A₀-2` and `A₀-3` above;
Serre, Invent. Math. 15 (1972), Prop. 5 and §5.4; Raynaud, Bull. SMF 102
(1974), Cor. 3.4.4): leaf `A` under the extra hypothesis `v_N(j) ≥ 0`.

This is `A` with its Tate-curve half removed (that half is leaf `T` above).
Its remaining deep content — tame inertia theory at `N` and Raynaud's
classification of finite flat group schemes over a base of absolute
ramification `e < N − 1` — is now in the three leaves above, and what is left
here is arithmetic, all of it proven:

* the identity `λ¹² = χ^{12r/e}` is `(λ^e)^{12/e} = (χ^r)^{12/e}`, which is
  exact because every `e ∈ {1,2,3,4,6}` divides `12`;
* the parity clause and the `(e,r) = (4,2) ⟹ N ≡ 3 (mod 4)` clause both
  follow from `a·e ≡ r (mod N−1)`, which is what reading `λ^e = χ^r` at an
  inertia element realising a GENERATOR of `(ZMod N)ˣ` gives.  See the
  section note above for the derivations.

Note the conclusion is deliberately quantified over `localInertiaGroup vN`
and not over `Γ ℚ`: widening it would make the leaf false, and globalizing it
is exactly what leaves `B`, `C` and `D` are for. -/
theorem WeierstrassCurve.exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hj : 0 ≤ padicValRat N E.j) :
    ∃ e r : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧ r ≤ e ∧
      (e % 2 = 0 → r % 2 = 0) ∧
      (∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ (12 * r / e)) ∧
      (e = 4 → r = 2 → N % 4 = 3) := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  -- the twelfth-power identity is pure exponent arithmetic once `λ^e = χ^r`:
  -- every admissible `e` divides `12`, so `12 * r / e` is exact
  have key : ∀ (x y : (ZMod N)ˣ) (e r : ℕ),
      (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) → x ^ e = y ^ r →
        x ^ 12 = y ^ (12 * r / e) := by
    rintro x y e r (rfl | rfl | rfl | rfl | rfl) h
    · have hx : x ^ 12 = (x ^ 1) ^ 12 := by rw [← pow_mul]
      rw [hx, h, ← pow_mul]; congr 1; omega
    · have hx : x ^ 12 = (x ^ 2) ^ 6 := by rw [← pow_mul]
      rw [hx, h, ← pow_mul]; congr 1; omega
    · have hx : x ^ 12 = (x ^ 3) ^ 4 := by rw [← pow_mul]
      rw [hx, h, ← pow_mul]; congr 1; omega
    · have hx : x ^ 12 = (x ^ 4) ^ 3 := by rw [← pow_mul]
      rw [hx, h, ← pow_mul]; congr 1; omega
    · have hx : x ^ 12 = (x ^ 6) ^ 2 := by rw [← pow_mul]
      rw [hx, h, ← pow_mul]; congr 1; omega
  -- `N` is an odd prime, so the modulus `N − 1` is EVEN; both derived clauses
  -- below live on that one fact
  have hNodd : N % 2 = 1 := by
    rcases hN.eq_two_or_odd with h | h
    · omega
    · exact h
  have h1N : 1 ≤ N := hN.one_lt.le
  -- `A₀-2`: the tame exponent; `A₀-1`: an inertia element realising a
  -- GENERATOR of `(ZMod N)ˣ` under `χ`
  obtain ⟨a, ha⟩ := E.exists_isogenyTameExponentAt g hN hg lam hlam
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod N)ˣ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq hN u
  have hord : orderOf u = N - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hN]
  -- `A₀-3`: Serre's semistability defect and Raynaud's exponent
  obtain ⟨e, r, he, hre, hchar⟩ :=
    E.exists_isogenyRaynaudExponentAt_of_padicValRat_j_nonneg g hN hN19 hg lam hlam hj
  -- reading `λ^e = χ^r` at `σ₀` and substituting `λ = χ^a` turns the character
  -- identity into a congruence between EXPONENTS, modulo the order `N − 1`
  have hmod : a * e ≡ r [MOD N - 1] := by
    have h2 := hchar σ₀ hσ₀
    rw [ha σ₀ hσ₀, ← pow_mul, hσ₀u] at h2
    rw [← hord]
    exact pow_eq_pow_iff_modEq.mp h2
  have hdvd : ((N : ℤ) - 1) ∣ (r : ℤ) - ((a * e : ℕ) : ℤ) := by
    have h := hmod.dvd
    rwa [Nat.cast_sub h1N, Nat.cast_one] at h
  refine ⟨e, r, he, hre, ?_, fun σ hσ => key _ _ e r he (hchar σ hσ), ?_⟩
  · -- PARITY is a consequence of the congruence, not an extra Raynaud input:
    -- `e` even makes `a * e` even, and `N − 1` is even, so `r` is even
    intro hev
    have h2N : (2 : ℤ) ∣ (N : ℤ) - 1 := by omega
    have hae : 2 ∣ a * e := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hev) a
    have hd : (2 : ℤ) ∣ (r : ℤ) - ((a * e : ℕ) : ℤ) := dvd_trans h2N hdvd
    have hd2 : (2 : ℤ) ∣ ((a * e : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hae
    -- `r = (r − a·e) + a·e`; written out rather than by `simpa`, so that no
    -- ambient simp lemma (some of which are sorried in this tree) is involved
    have hr2 : (2 : ℤ) ∣ (r : ℤ) := by
      obtain ⟨k, hk⟩ := hd
      obtain ⟨m, hm⟩ := hd2
      exact ⟨k + m, by linarith⟩
    have : (2 : ℕ) ∣ r := by exact_mod_cast hr2
    omega
  · -- and so is `N ≡ 3 (mod 4)` in the `(e, r) = (4, 2)` case: `4 ∣ N − 1`
    -- would give `4 ∣ 2 − 4a`, which is absurd
    rintro rfl rfl
    push_cast at hdvd
    have hN4 : N % 4 = 1 ∨ N % 4 = 3 := by omega
    rcases hN4 with h4 | h4
    · exfalso
      have hd4 : (4 : ℤ) ∣ (N : ℤ) - 1 := by omega
      have hfin := dvd_trans hd4 hdvd
      omega
    · exact h4

/-- **`A` — Serre–Raynaud local ramification data at `N`** (DECOMPOSED and
PROVEN 2026-07-27 from `T` and `A₀` above; Serre, Invent. Math. 15 (1972),
Prop. 5 and §5.4; Raynaud, Bull. SMF 102 (1974), Cor. 3.4.4): the LOCAL half
of `exists_isogenyRamificationData`, asserting the existence of the
ramification index `e` and Raynaud exponent `r` together with the identity
`λ¹² = χ^(12r/e)` ON INERTIA AT `N` ONLY.

The proof is the reduction-type dichotomy at `N` — `v_N(j) < 0` is
potentially multiplicative, `v_N(j) ≥ 0` is potentially good (Silverman *AEC*
VII.5.5, which is the encoding this file already uses in
`potentiallyGoodReduction_of_isogenyCharacter`).  The potentially good branch
IS leaf `A₀`.  The potentially multiplicative branch is leaf `T` at `v = N`,
which returns `r ∈ {0, 1}`; taking `e = 1` makes every side condition trivial
(`r ≤ 1`, `1 % 2 ≠ 0` so the parity constraint is vacuous, `1 ≠ 4` so the
`N ≡ 3 (mod 4)` constraint is vacuous, and `12r/1 = 12r`).  That `(e, r)` is
`(1, 0)` or `(1, 1)` is exactly what the old prose proof read off from the
Tate curve.

Note the conclusion is deliberately quantified over
`localInertiaGroup vN` and not over `Γ ℚ`: widening it would make the
leaf false, and globalizing it is exactly what leaves `B`, `C` and `D`
are for. -/
theorem WeierstrassCurve.exists_isogenyLocalRamificationDataAt
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g) :
    ∃ e r : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧ r ≤ e ∧
      (e % 2 = 0 → r % 2 = 0) ∧
      (∀ σ ∈ localInertiaGroup hN.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hN.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hN.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ (12 * r / e)) ∧
      (e = 4 → r = 2 → N % 4 = 3) := by
  by_cases hj : 0 ≤ padicValRat N E.j
  · -- potentially good reduction at `N`: this IS leaf `A₀`
    exact E.exists_isogenyLocalRamificationDataAt_of_padicValRat_j_nonneg
      g hN hN19 hg lam hlam hj
  · -- potentially multiplicative reduction at `N`: leaf `T` at `v = N`,
    -- with `e = 1`, which makes every side condition trivial
    obtain ⟨r, hr1, hloc⟩ := E.exists_isogenyTateExponent_of_padicValRat_j_neg
      g hN hN19 hg lam hlam hN (not_le.mp hj)
    refine ⟨1, r, Or.inl rfl, hr1, by omega, ?_, by omega⟩
    simpa using hloc

/-- **The ring-theoretic core of leaf `D`** (PROVEN 2026-07-27): in a local
ring `R` in which `N` is a UNIT, let `x` be an `N`-th root of unity whose
geometric sum `1 + x + … + x^{N−1}` vanishes (the two identities an
`N`-th primitive root satisfies, transported from wherever it lives).  If
`x^i ≡ x` modulo the maximal ideal for some `i < N`, then `i = 1`.

This is what makes leaf `D` a `ℓ`-uniform statement rather than a
`3`-specific one.  The whole argument happens in the residue field `κ`,
and needs no product formula:

* `x̄^i = x̄` with `x̄` a unit gives `x̄^{i−1} = 1` (for `i ≥ 1`; `i = 0`
  gives `x̄ = 1` outright), so `orderOf x̄` divides both `i − 1` and `N`.
  `N` is prime and `0 < i − 1 < N`, so the order is `1`, i.e. `x̄ = 1`.
* Then the geometric sum reads `0 = ∑_{j<N} x̄^j = N` in `κ`, i.e.
  `N ∈ 𝔪` — contradicting that `N` is a unit.

Stated over an arbitrary `CommRing` + `IsLocalRing` so that leaf `D` need
only supply the two identities and the unit hypothesis; in `D` the ring is
the integral closure of `𝒪ᵥ` in `ℚ̄ᵥ`, whose maximal ideal is what defines
`localInertiaGroup`. -/
theorem rootOfUnity_index_eq_one_of_sub_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {N : ℕ} (hN : N.Prime)
    {x : R} (hgeom : ∑ j ∈ Finset.range N, x ^ j = 0)
    (hxN : x ^ N = 1) (hNunit : IsUnit ((N : ℕ) : R))
    {i : ℕ} (hiN : i < N) (hxi : x ^ i - x ∈ IsLocalRing.maximalIdeal R) :
    i = 1 := by
  classical
  by_contra hne
  -- pass to the residue field
  have hres : IsLocalRing.residue R x ^ i = IsLocalRing.residue R x := by
    have h0 : IsLocalRing.residue R (x ^ i - x) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hxi
    rw [map_sub, map_pow] at h0
    exact sub_eq_zero.mp h0
  have hxNres : IsLocalRing.residue R x ^ N = 1 := by
    rw [← map_pow, hxN, map_one]
  have hxu : IsUnit (IsLocalRing.residue R x) :=
    IsUnit.of_pow_eq_one hxNres hN.ne_zero
  -- the residue of `x` is `1`
  have hx1 : IsLocalRing.residue R x = 1 := by
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [pow_zero] at hres; exact hres.symm
    · -- `i ≥ 2`, so `0 < i - 1 < N`
      have hk : 0 < i - 1 := by omega
      have hkN : i - 1 < N := by omega
      have hpow : IsLocalRing.residue R x ^ (i - 1) = 1 := by
        have h1 : IsLocalRing.residue R x ^ (i - 1) * IsLocalRing.residue R x
            = 1 * IsLocalRing.residue R x := by
          rw [one_mul, ← pow_succ, Nat.sub_add_cancel hipos]
          exact hres
        exact hxu.mul_right_cancel h1
      have hd1 : orderOf (IsLocalRing.residue R x) ∣ (i - 1) :=
        orderOf_dvd_of_pow_eq_one hpow
      have hd2 : orderOf (IsLocalRing.residue R x) ∣ N :=
        orderOf_dvd_of_pow_eq_one hxNres
      rcases hN.eq_one_or_self_of_dvd _ hd2 with h1 | hNo
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (hNo ▸ hd1) (Nat.not_dvd_of_pos_of_lt hk hkN)
  -- the geometric sum then reads `N = 0` in the residue field
  have hNzero : ((N : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    have h := congrArg (IsLocalRing.residue R) hgeom
    rw [map_sum, map_zero] at h
    simp_rw [map_pow, hx1, one_pow] at h
    simpa using h
  have hNmem : ((N : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact hNzero
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hNmem)) hNunit

/-- **`D` — the mod-`N` cyclotomic character is unramified away from `N`**
(PROVEN 2026-07-27, by generalizing the `ℓ = 3` proof to every prime `ℓ`):
for primes `q ≠ N`, `χ_N` kills the inertia group at `q`.

This is the general-`ℓ` form of
`GaloisRepresentation.cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup`
(`HardlyRamified/Threeadic.lean`), which exists only at `ℓ = 3` and is
DOWNSTREAM of this module, so it cannot be reused here.

Proof, transcribing the `ℓ = 3` proof: let `ι` be the embedding of
algebraic closures underlying `absoluteGaloisGroup.map`, and `ζ` a
primitive `N`-th root of unity in `ℚ̄`.  Then `ι ζ` is a primitive `N`-th
root of unity, integral over `𝒪ᵥ`, and `σ` permutes the `N`-th roots, so
`σ (ι ζ) = (ι ζ)^i` for some `i < N`; the inertia congruence puts
`(ι ζ)^i − ι ζ` in `𝔪`.  The ring-theoretic core
`rootOfUnity_index_eq_one_of_sub_mem_maximalIdeal` (just above) then
forces `i = 1`, so `σ` fixes `ι ζ`, so `map σ` fixes `ζ`, and
`modularCyclotomicCharacter.unique` evaluates the character to `1`
(compare `cyclotomicCharacterModL_eq_one` in `Chebotarev.lean`).

WHAT THE GENERALIZATION NEEDED, against the `ℓ = 3` proof and against the
route this docstring originally drafted.  At `ℓ = 3` the index `i` ranges
over `{0, 1, 2}` and `interval_cases` disposes of it; the only unit
statement required is the special factorisation `(1 − ζ)(1 − ζ²) = 3`.
The draft proposed replacing that by `∏_{j=1}^{N−1} (1 − ζ^j) = N` and
peeling off the relevant factor.  That is correct mathematics but is NOT
the cheapest route in Lean: it needs the whole product identity, and then
a divisibility argument to extract `1 − ζ^{i−1}`.  What replaced it works
entirely in the RESIDUE FIELD and needs no product at all — see the core
lemma's own docstring. -/
theorem cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne
    {N : ℕ} (hN : N.Prime) {q : ℕ} (hq : q.Prime) (hqN : q ≠ N) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ)) = 1 := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  haveI : Fact (1 < N) := ⟨hN.one_lt⟩
  set v := hq.toHeightOneSpectrumRingOfIntegersRat
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v :=
    algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f
  intro σ hσ
  -- a primitive `N`-th root of unity in `ℚ̄` and its image downstairs
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hη : IsPrimitiveRoot (ι ζ) N := hζ.map_of_injective ι.injective
  -- the inertia element fixes `ζ`
  have hfix : Field.absoluteGaloisGroup.map f σ ζ = ζ := by
    have hmapζN : (Field.absoluteGaloisGroup.map f σ ζ) ^ N = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, hiN, hiζ⟩ := hζ.eq_pow_of_pow_eq_one hmapζN
    haveI hVR : ValuationRing (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
      valuationRing_integralClosure v
    haveI hLoc : IsLocalRing (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
      inferInstance
    have hση : σ (ι ζ) = (ι ζ) ^ i := by
      have hL := Field.absoluteGaloisGroup.lift_map f σ ζ
      rw [← hiζ] at hL
      rw [← hL, map_pow]
    -- move into the integral closure of `𝒪ᵥ`
    have hint : IsIntegral
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (ι ζ) := by
      refine ⟨Polynomial.X ^ N - Polynomial.C 1,
        Polynomial.monic_X_pow_sub_C 1 hN.ne_zero, ?_⟩
      simp [hη.pow_eq_one]
    set x : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
      ⟨ι ζ, hint⟩ with hx
    set j := algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) with hj
    have hjinj : Function.Injective j := fun a b h => Subtype.ext h
    have hjx : j x = ι ζ := rfl
    -- the two identities of a primitive `N`-th root, transported to `IC`
    have hxN : x ^ N = 1 := by
      apply hjinj
      rw [map_pow, map_one, hjx]
      exact hη.pow_eq_one
    have hgeom : ∑ k ∈ Finset.range N, x ^ k = 0 := by
      apply hjinj
      rw [map_sum, map_zero]
      simp_rw [map_pow, hjx]
      exact hη.geom_sum_eq_zero hN.one_lt
    -- `N` is a unit of the integral closure, since `q ≠ N`
    have hNunit : IsUnit ((N : ℕ) : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
      have h1 := GaloisRepresentation.isUnit_natCast_adicCompletionIntegers
        hN hq (Ne.symm hqN)
      have h2 := h1.map (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      rwa [map_natCast] at h2
    -- the inertia congruence: `σ • x - x = x^i - x ∈ 𝔪`
    have hxi : x ^ i - x ∈ IsLocalRing.maximalIdeal
        (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
      have h2 : σ • x - x ∈ IsLocalRing.maximalIdeal
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
        (AddSubgroup.mem_inertia.mp hσ) x
      have hsmul : σ • x = x ^ i := by
        apply hjinj
        have h1 : j (σ • x) = σ (ι ζ) := by
          show (σ • x).1 = σ (ι ζ)
          rw [IntegralClosure.coe_smul]
          rfl
        rw [h1, hση, map_pow, hjx]
      rwa [hsmul] at h2
    have hi1 : i = 1 :=
      rootOfUnity_index_eq_one_of_sub_mem_maximalIdeal hN hgeom hxN hNunit hiN hxi
    subst hi1
    rw [pow_one] at hiζ
    exact hiζ.symm
  -- `map f σ` fixes every `N`-th root of unity, so the character is `1`
  have hone : (1 : ZMod N) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) (Field.absoluteGaloisGroup.map f σ)) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) _ _
      fun t ht => ?_
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    obtain ⟨i, hiN, hiζ⟩ := hζ.eq_pow_of_pow_eq_one htN
    show Field.absoluteGaloisGroup.map f σ
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [← hiζ, map_pow, hfix]
  have hid : modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) (Field.absoluteGaloisGroup.map f σ))
      = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (Field.absoluteGaloisGroup.map f σ) : (ZMod N)ˣ) := rfl
  refine Units.ext ?_
  rw [← hid, ← hone]
  rfl

/-!
##### The resultant elimination, in kernel-checked arithmetic form
(PROVEN 2026-07-26)

The four lemmas below are the FINITE COMPUTATION of [MJ, §4.2], stated
and proved over `ℤ` and `ZMod N` with no elliptic curve in sight. They
are what turns `not_isogenyCharacter_of_isogenySignature_ne_six` from a
deep leaf into a thin wrapper around ONE Galois-theoretic input
(`exists_frobeniusTrace_of_potentiallyGoodReduction`, below).

Mazur's classical step is `N ∣ Res(X² − aX + q, X¹² − q^s)`. Forming the
resultant is unnecessary. If `x ∈ ZMod N` is a common root of the two
polynomials, put `y := a − x`. Then `y` is the second root of the
quadratic, so `x + y = a` and `x · y = q`; since `N ≥ 23` makes `q`
invertible, `x¹² = q^s` forces `y¹² = q^{12−s}`. Newton's identities
express the power sum `x¹² + y¹²` as an explicit integer polynomial in
`x + y` and `x · y`, namely

  `P₁₂(A, B) = A¹² − 12A¹⁰B + 54A⁸B² − 112A⁶B³ + 105A⁴B⁴ − 36A²B⁵ + 2B⁶`,

so `N ∣ q^s + q^{12−s} − P₁₂(a, q)`. That integer is `Res / q^s` up to
sign, and it is the form actually used below.

Two economies follow from this form, and together they cut the
computation from the six resultants printed in [MJ, §4.2] to three
integers per prime:

* the value depends on `s` only through `q^s + q^{12−s}`, which is
  INVARIANT under `s ↦ 12 − s`. So `s = 0` and `s = 12` give literally
  the same integers, as do `s = 4` and `s = 8`;
* `P₁₂(−a, q) = P₁₂(a, q)`, so only `|a|` matters.

Concretely, with `|a| ≤ 3` at `q = 3` and `|b| ≤ 4` at `q = 5`:

* `s ∈ {4, 8}`, `q = 3`: the values are `5184 = 2⁶·3⁴`,
  `5984 = 2⁵·11·17`, `8000 = 2⁶·5³` — all `19`-smooth, so a prime
  `N ≥ 23` divides none of them and `q = 5` is not even needed;
* `s ∈ {0, 12}`, `q = 3`: the values are `529984 = 2⁶·7²·13²`,
  `530784 = 2⁵·3²·19·97`, `532800 = 2⁶·3²·5²·37`. A prime `N ≥ 23`
  dividing one of them is `37` or `97`; `hN37` kills `37`, so `N = 97`;
* `s ∈ {0, 12}`, `q = 5`: the values are `244109376`, `244117120`,
  `244166400`, `244168960`, and `97` divides none of them.

So the second prime `q = 5` is used for exactly one thing: refuting
`N = 97`. (Cross-check against the section note above: `R(q, s)` there is
`q^s` times the lcm of the values here — e.g. `81 · lcm(5184, 5984,
8000) = 81 · 121176000 = 9815256000 = R(3, 4)`.)
-/

/-- **The power-sum divisibility** (PROVEN): if `x ∈ ZMod N` is a root of
`X² − aX + q` with `a ∈ ℤ`, and `x¹² = q^s` with `s ≤ 12` and `q`
invertible, then `N` divides the integer `q^s + q^{12−s} − P₁₂(a, q)`.

This is Mazur's resultant divisibility with the resultant replaced by a
power sum; see the section note above for why the two are equivalent. -/
theorem mazurIsogeny_powerSum_dvd {N : ℕ} [Fact N.Prime] {q : ℕ}
    (hq : ((q : ℕ) : ZMod N) ≠ 0)
    {s : ℕ} (hs12 : s ≤ 12) {x : ZMod N} {a : ℤ}
    (hx : x ^ 2 - (a : ZMod N) * x + ((q : ℕ) : ZMod N) = 0)
    (hp : x ^ 12 = ((q : ℕ) : ZMod N) ^ s) :
    (N : ℤ) ∣ (q : ℤ) ^ s + (q : ℤ) ^ (12 - s) -
      (a ^ 12 - 12 * a ^ 10 * (q : ℤ) + 54 * a ^ 8 * (q : ℤ) ^ 2
        - 112 * a ^ 6 * (q : ℤ) ^ 3 + 105 * a ^ 4 * (q : ℤ) ^ 4
        - 36 * a ^ 2 * (q : ℤ) ^ 5 + 2 * (q : ℤ) ^ 6) := by
  -- The conjugate root of the quadratic.
  set y : ZMod N := (a : ZMod N) - x with hy
  have hsum : x + y = (a : ZMod N) := by rw [hy]; ring
  have hprod : x * y = ((q : ℕ) : ZMod N) := by rw [hy]; linear_combination -hx
  -- `x¹² · y¹² = q¹²` and `x¹² = q^s`, so `y¹² = q^{12−s}`.
  have hy12 : y ^ 12 = ((q : ℕ) : ZMod N) ^ (12 - s) := by
    refine mul_left_cancel₀ (pow_ne_zero s hq) ?_
    rw [← pow_add]
    have hsplit : s + (12 - s) = 12 := by omega
    rw [hsplit, ← hp, ← mul_pow, hprod]
  -- Newton's identity for the twelfth power sum.
  have key : x ^ 12 + y ^ 12 =
      (x + y) ^ 12 - 12 * (x + y) ^ 10 * (x * y) + 54 * (x + y) ^ 8 * (x * y) ^ 2
        - 112 * (x + y) ^ 6 * (x * y) ^ 3 + 105 * (x + y) ^ 4 * (x * y) ^ 4
        - 36 * (x + y) ^ 2 * (x * y) ^ 5 + 2 * (x * y) ^ 6 := by ring
  rw [hsum, hprod, hp, hy12] at key
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  linear_combination key

/-- **Endgame at `s ∈ {4, 8}`** (PROVEN): the three `q = 3` values are
`19`-smooth, so no prime `N ≥ 23` divides any of them. -/
theorem mazurIsogeny_not_dvd_smooth {N : ℕ} (hN : N.Prime) (hN23 : 23 ≤ N)
    (h : N ∣ 5184 ∨ N ∣ 5984 ∨ N ∣ 8000) : False := by
  have cop : ∀ p k : ℕ, p.Prime → p < 23 → Nat.Coprime N (p ^ k) := fun p k hp hp23 =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes hN hp).mpr (by omega))
  have hone : N = 1 := by
    rcases h with h | h | h
    · have e : (5184 : ℕ) = 2 ^ 6 * 3 ^ 4 := by norm_num
      rw [e] at h
      exact Nat.eq_one_of_dvd_coprimes
        ((cop 2 6 Nat.prime_two (by norm_num)).mul_right
          (cop 3 4 Nat.prime_three (by norm_num))) dvd_rfl h
    · have e : (5984 : ℕ) = 2 ^ 5 * (11 ^ 1 * 17 ^ 1) := by norm_num
      rw [e] at h
      exact Nat.eq_one_of_dvd_coprimes
        ((cop 2 5 Nat.prime_two (by norm_num)).mul_right
          ((cop 11 1 (by norm_num) (by norm_num)).mul_right
            (cop 17 1 (by norm_num) (by norm_num)))) dvd_rfl h
    · have e : (8000 : ℕ) = 2 ^ 6 * 5 ^ 3 := by norm_num
      rw [e] at h
      exact Nat.eq_one_of_dvd_coprimes
        ((cop 2 6 Nat.prime_two (by norm_num)).mul_right
          (cop 5 3 (by norm_num) (by norm_num))) dvd_rfl h
  omega

/-- **Endgame at `s ∈ {0, 12}`, first half** (PROVEN): a prime `N ≥ 23`
with `N ≠ 37` dividing one of the three `q = 3` values must be `97`.
The three large prime factors available are `37` (from `532800`) and
`97` (from `530784`); `529984` is `19`-smooth. -/
theorem mazurIsogeny_eq_ninetySeven {N : ℕ} (hN : N.Prime) (hN23 : 23 ≤ N) (hN37 : N ≠ 37)
    (h : N ∣ 529984 ∨ N ∣ 530784 ∨ N ∣ 532800) : N = 97 := by
  have cop : ∀ p k : ℕ, p.Prime → p < 23 → Nat.Coprime N (p ^ k) := fun p k hp hp23 =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes hN hp).mpr (by omega))
  rcases h with h | h | h
  · exfalso
    have e : (529984 : ℕ) = 2 ^ 6 * (7 ^ 2 * 13 ^ 2) := by norm_num
    rw [e] at h
    have hone := Nat.eq_one_of_dvd_coprimes
      ((cop 2 6 Nat.prime_two (by norm_num)).mul_right
        ((cop 7 2 (by norm_num) (by norm_num)).mul_right
          (cop 13 2 (by norm_num) (by norm_num)))) dvd_rfl h
    omega
  · have e : (530784 : ℕ) = (2 ^ 5 * (3 ^ 2 * 19 ^ 1)) * 97 := by norm_num
    rw [e] at h
    have hd : N ∣ 97 := Nat.Coprime.dvd_of_dvd_mul_left
      ((cop 2 5 Nat.prime_two (by norm_num)).mul_right
        ((cop 3 2 Nat.prime_three (by norm_num)).mul_right
          (cop 19 1 (by norm_num) (by norm_num)))) h
    exact (Nat.prime_dvd_prime_iff_eq hN (by norm_num)).mp hd
  · exfalso
    have e : (532800 : ℕ) = (2 ^ 6 * (3 ^ 2 * 5 ^ 2)) * 37 := by norm_num
    rw [e] at h
    have hd : N ∣ 37 := Nat.Coprime.dvd_of_dvd_mul_left
      ((cop 2 6 Nat.prime_two (by norm_num)).mul_right
        ((cop 3 2 Nat.prime_three (by norm_num)).mul_right
          (cop 5 2 (by norm_num) (by norm_num)))) h
    exact hN37 ((Nat.prime_dvd_prime_iff_eq hN (by norm_num)).mp hd)

/-- **The resultant elimination** (PROVEN): a prime `N ≥ 23` with
`N ≠ 37` admits no simultaneous solution, at `q = 3` and `q = 5`, of the
two conditions that Mazur's argument produces from a Frobenius element —
being a root of `X² − aX + q` for an integer `a` with `a² ≤ 4q`, and
having twelfth power `q^s` — for any signature `s ∈ {0, 4, 8, 12}`.

This is the whole of [MJ, Prop. 4.3] except its input. Every case is
discharged by the compiler: `interval_cases` over the seven admissible
`a` at `q = 3` and the nine at `q = 5`, then `norm_num` on the resulting
integer divisibilities. -/
theorem mazurIsogeny_resultantElimination {N : ℕ} [Fact N.Prime]
    (hN23 : 23 ≤ N) (hN37 : N ≠ 37)
    {s : ℕ} (hs : s = 0 ∨ s = 4 ∨ s = 8 ∨ s = 12)
    {x3 x5 : ZMod N} {a3 a5 : ℤ}
    (ha3 : a3 ^ 2 ≤ 12) (ha5 : a5 ^ 2 ≤ 20)
    (hx3 : x3 ^ 2 - (a3 : ZMod N) * x3 + ((3 : ℕ) : ZMod N) = 0)
    (hx5 : x5 ^ 2 - (a5 : ZMod N) * x5 + ((5 : ℕ) : ZMod N) = 0)
    (hp3 : x3 ^ 12 = ((3 : ℕ) : ZMod N) ^ s)
    (hp5 : x5 ^ 12 = ((5 : ℕ) : ZMod N) ^ s) :
    False := by
  have hN : N.Prime := Fact.out
  have hqne : ∀ q : ℕ, 0 < q → q < 23 → ((q : ℕ) : ZMod N) ≠ 0 := by
    intro q hq0 hq23
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hq0 hdvd
    omega
  have hs12 : s ≤ 12 := by rcases hs with rfl | rfl | rfl | rfl <;> norm_num
  have d3 := mazurIsogeny_powerSum_dvd (hqne 3 (by norm_num) (by norm_num)) hs12 hx3 hp3
  have d5 := mazurIsogeny_powerSum_dvd (hqne 5 (by norm_num) (by norm_num)) hs12 hx5 hp5
  have hb3l : -3 ≤ a3 := by nlinarith
  have hb3r : a3 ≤ 3 := by nlinarith
  have hb5l : -4 ≤ a5 := by nlinarith
  have hb5r : a5 ≤ 4 := by nlinarith
  clear hx3 hx5 hp3 hp5 ha3 ha5 hs12 hqne
  rcases hs with rfl | rfl | rfl | rfl
  · -- `s = 0`: `q = 3` gives `N = 97`, and `q = 5` refutes it.
    have h3 : N ∣ 529984 ∨ N ∣ 530784 ∨ N ∣ 532800 := by
      clear d5 hb5l hb5r
      interval_cases a3 <;> norm_num at d3
      exacts [Or.inl (by exact_mod_cast d3), Or.inr (Or.inl (by exact_mod_cast d3)),
        Or.inr (Or.inr (by exact_mod_cast d3)), Or.inl (by exact_mod_cast d3),
        Or.inr (Or.inr (by exact_mod_cast d3)), Or.inr (Or.inl (by exact_mod_cast d3)),
        Or.inl (by exact_mod_cast d3)]
    have h97 : N = 97 := mazurIsogeny_eq_ninetySeven hN hN23 hN37 h3
    subst h97
    interval_cases a5 <;> norm_num at d5
  · -- `s = 4`: the `q = 3` values are already `19`-smooth.
    refine mazurIsogeny_not_dvd_smooth hN hN23 ?_
    clear d5 hb5l hb5r
    interval_cases a3 <;> norm_num at d3
    exacts [Or.inl (by exact_mod_cast d3), Or.inr (Or.inl (by exact_mod_cast d3)),
      Or.inr (Or.inr (by exact_mod_cast d3)), Or.inl (by exact_mod_cast d3),
      Or.inr (Or.inr (by exact_mod_cast d3)), Or.inr (Or.inl (by exact_mod_cast d3)),
      Or.inl (by exact_mod_cast d3)]
  · -- `s = 8`: the same three integers as `s = 4`.
    refine mazurIsogeny_not_dvd_smooth hN hN23 ?_
    clear d5 hb5l hb5r
    interval_cases a3 <;> norm_num at d3
    exacts [Or.inl (by exact_mod_cast d3), Or.inr (Or.inl (by exact_mod_cast d3)),
      Or.inr (Or.inr (by exact_mod_cast d3)), Or.inl (by exact_mod_cast d3),
      Or.inr (Or.inr (by exact_mod_cast d3)), Or.inr (Or.inl (by exact_mod_cast d3)),
      Or.inl (by exact_mod_cast d3)]
  · -- `s = 12`: the same three integers as `s = 0`.
    have h3 : N ∣ 529984 ∨ N ∣ 530784 ∨ N ∣ 532800 := by
      clear d5 hb5l hb5r
      interval_cases a3 <;> norm_num at d3
      exacts [Or.inl (by exact_mod_cast d3), Or.inr (Or.inl (by exact_mod_cast d3)),
        Or.inr (Or.inr (by exact_mod_cast d3)), Or.inl (by exact_mod_cast d3),
        Or.inr (Or.inr (by exact_mod_cast d3)), Or.inr (Or.inl (by exact_mod_cast d3)),
        Or.inl (by exact_mod_cast d3)]
    have h97 : N = 97 := mazurIsogeny_eq_ninetySeven hN hN23 hN37 h3
    subst h97
    interval_cases a5 <;> norm_num at d5

/-- **Eigenvalue relation in rank two** (PROVEN 2026-07-27): on a
`2`-dimensional space over a field, an eigenvalue `c` of `f` — witnessed
by a NONZERO eigenvector — satisfies the characteristic quadratic
`c² − (tr f)·c + det f = 0`.

Pure linear algebra: Cayley–Hamilton (`LinearMap.aeval_self_charpoly`)
against `GaloisRepresentation.charpoly_eq_quadratic_of_finrank_two`
(`charpoly f = X² − (tr f)X + det f` in rank two), applied to the
eigenvector and then divided by it. This is step 1 of
`exists_frobeniusTrace_of_potentiallyGoodReduction`, isolated so that the
elliptic-curve leaf below carries no linear algebra at all. -/
theorem mazurIsogeny_eigenvalue_quadratic_of_finrank_two
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] [Module.Free F V]
    (hfr : Module.finrank F V = 2) (f : V →ₗ[F] V)
    {v : V} (hv : v ≠ 0) {c : F} (hfv : f v = c • v) :
    c ^ 2 - LinearMap.trace F V f * c + LinearMap.det f = 0 := by
  classical
  have hCH := f.aeval_self_charpoly
  rw [GaloisRepresentation.charpoly_eq_quadratic_of_finrank_two hfr f] at hCH
  -- Cayley–Hamilton, applied to the eigenvector
  have h0 : f (f v) - (LinearMap.trace F V f) • (f v) + (LinearMap.det f) • v = 0 := by
    have happ := congrArg (fun e : Module.End F V => e v) hCH
    simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Module.End.mul_apply, Module.End.pow_apply,
      Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      Module.algebraMap_end_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] using happ
  -- rewrite the eigenvector relation twice, then cancel the eigenvector
  have hsmul : (c ^ 2 - LinearMap.trace F V f * c + LinearMap.det f) • v = 0 := by
    rw [hfv, map_smul, hfv, smul_smul, smul_smul, ← pow_two] at h0
    rw [add_smul, sub_smul]
    exact h0
  rcases smul_eq_zero.mp hsmul with h | h
  · exact h
  · exact absurd h hv

/-- **The endomorphism of the `N`-torsion induced by an automorphism of a
Weierstrass curve.**

An automorphism of `W` over `F` — as an elliptic curve, i.e. fixing the origin
— is exactly an admissible change of variables `C` with `C • W⁄F = W⁄F`
(Silverman *AEC* III.3.1(b): the isomorphisms between Weierstrass equations are
precisely the variable changes). The point-level transport of a
`VariableChange` then turns it into an additive automorphism of the point
group, which restricts to the `N`-torsion and is `ZMod N`-linear there. The
construction mirrors `WeilPairing.frobeniusTorsionEnd` line for line, with
`Point.equivVariableChange` in place of `Point.map (frobAlgHom q)`.

THE POINT-LEVEL API THIS RESTS ON, AND WHERE THE SAME LESSON WAS LEARNED
TWICE. `WeierstrassCurve.Affine.Point.equivVariableChange`, together with
`equivVariableChangeBaseChange` and `equivVariableChangeBaseChange_galois`,
lives in the project shim
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`. It is
absent from mathlib, which is exactly why the shim exists — and
`EllipticCurve/TorsionReduction.lean` independently recorded, then RETIRED
("it was never missing"), an audit item claiming this map had to be built,
after an earlier grep had covered only mathlib's copy. Both files now depend
on it. The reusable moral is the standing one: grep `Fermat/`,
`.lake/packages/mathlib/` and `~/cs/FLT/`, not mathlib alone. -/
noncomputable def WeierstrassCurve.autTorsionEnd {F : Type*} [Field F]
    [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F)
    (hC : C • (W.map (algebraMap F F)) = W.map (algebraMap F F)) (N : ℕ) :
    Module.End (ZMod N) (W.nTorsion N) :=
  AddMonoidHom.toZModLinearMap N
    (TorsionCounting.endRestrict
      ((((WeierstrassCurve.Affine.Point.equivOfEq hC.symm).trans
        (WeierstrassCurve.Affine.Point.equivVariableChange
          (W.map (algebraMap F F)) C)) : _ ≃+ _).toAddMonoidHom) N)

/-- **A potentially-good-reduction datum for `E` at `q`, with residue degree
one** (interface opened 2026-07-27 while decomposing
`exists_frobeniusAut_of_potentiallyGoodReduction` below into its ARITHMETIC and
its GALOIS halves).

THE CONTENT. A `PotentiallyGoodModel E q` is exactly the sentence "`E` acquires
good reduction over a finite extension of `ℚ` at a prime above `q` whose residue
field is the PRIME field `𝔽_q`", written as data:

* `K` — a number field (`FiniteDimensional ℚ K` is field `instFin`);
* `R` — a DVR with fraction field `K`, i.e. the local ring of a prime of `K`.
  No hypothesis says `R` lies above `q`: `resEquiv` already forces it, since a
  residue field of characteristic `q` forces `q ∈ 𝔪`;
* `resEquiv : ResidueField R ≃+* ZMod q` — **this is where TOTAL RAMIFICATION
  is encoded**, exactly as `TameGoodModel.res` encodes it in
  `EllipticCurve/TorsionReduction.lean`: landing in the PRIME field rather than
  in an extension of it says the residue degree is `1`, hence
  `e = [K_𝔮 : ℚ_q]`;
* `V` — the good model, with mathlib's `HasGoodReduction R` (which extends
  `IsMinimal R`, so `V` is a minimal integral equation whose discriminant is a
  unit), and `V_eq` pinning `V` as a model OF `E` rather than an unrelated
  curve.

WHY THIS IS THE RIGHT CUT, and it is the standing rule that a cut may need a
theory only STATED rather than PROVEN. The old single leaf mixed two
difficulties that share no technique:

1. *Arithmetic*: `0 ≤ v_q(j)` ⟹ such a datum exists. Reduction theory of
   Weierstrass equations, Kummer/wild extensions of `ℚ_q`, and a Krasner-style
   descent to a number field. Nothing Galois-theoretic appears.
2. *Galois*: given the datum, `ρ(σ_q)` is an automorphism composed with the
   `q`-power Frobenius of the reduction. Néron–Ogg–Shafarevich and Serre–Tate.
   No reduction theory appears — the model is handed over.

They are now `exists_potentiallyGoodModel_of_jIntegral` and
`exists_frobeniusAut_of_potentiallyGoodModel`, separately ownable.

RELATION TO `TameGoodModel` (`EllipticCurve/TorsionReduction.lean`), whose
existence leaf `exists_tameGoodModel_of_jIntegral` is ALREADY OPEN and being
worked: the two structures say the same thing in different vocabularies —
`TameGoodModel` carries a `ValuationSubring L` with a residue map to `ZMod ℓ`
and an abstract injection of points, this one carries a DVR with mathlib's
`HasGoodReduction`. Neither subsumes the other as written and NEITHER SHOULD BE
DUPLICATED: whoever proves one should expect to write the (routine, but not
free) translation rather than reprove the arithmetic. The two differences that
matter are that `TameGoodModel` assumes `5 ≤ ℓ` at its producer — so it does
NOT cover `q = 3`, which the consumers of this file need — and that it does not
ask `L` to be a NUMBER field, which is what makes `Γ K ≤ Γ ℚ` available to the
Galois half here.

NOT VACUOUS, and `V_eq` is what prevents it: `V` is pinned to `C • E_K`, so no
choice of an unrelated good curve satisfies the structure. `resEquiv` cannot be
degenerate either — `ZMod q` is a field of `q` elements, so a residue field of
any other size (in particular any nontrivial extension of `𝔽_q`, which is what
a prime of residue degree `> 1` would give) simply admits no such equivalence.
-/
structure WeierstrassCurve.PotentiallyGoodModel (E : WeierstrassCurve ℚ)
    (q : ℕ) [Fact q.Prime] where
  /-- The number field over which `E` acquires good reduction. -/
  K : Type
  [instField : Field K]
  [instDec : DecidableEq K]
  [instAlgebra : Algebra ℚ K]
  [instFin : FiniteDimensional ℚ K]
  /-- The local ring of the chosen prime of `K` above `q`. -/
  R : Type
  [instCommRing : CommRing R]
  [instDomain : IsDomain R]
  [instDVR : IsDiscreteValuationRing R]
  [instAlgRK : Algebra R K]
  [instFrac : IsFractionRing R K]
  /-- **Residue degree one.** Landing in the PRIME field `ZMod q` rather than in
  an extension of it is where total ramification is encoded. -/
  resEquiv : IsLocalRing.ResidueField R ≃+* ZMod q
  /-- The good model itself. -/
  V : WeierstrassCurve K
  [V_elliptic : V.IsElliptic]
  [V_good : V.HasGoodReduction R]
  /-- The variable change carrying `E` over `K` to that model. -/
  C : WeierstrassCurve.VariableChange K
  /-- `V` is genuinely a model of `E`, not an unrelated curve. -/
  V_eq : V = C • (E.baseChange K)

attribute [instance] WeierstrassCurve.PotentiallyGoodModel.instField
  WeierstrassCurve.PotentiallyGoodModel.instDec
  WeierstrassCurve.PotentiallyGoodModel.instAlgebra
  WeierstrassCurve.PotentiallyGoodModel.instFin
  WeierstrassCurve.PotentiallyGoodModel.instCommRing
  WeierstrassCurve.PotentiallyGoodModel.instDomain
  WeierstrassCurve.PotentiallyGoodModel.instDVR
  WeierstrassCurve.PotentiallyGoodModel.instAlgRK
  WeierstrassCurve.PotentiallyGoodModel.instFrac
  WeierstrassCurve.PotentiallyGoodModel.V_elliptic
  WeierstrassCurve.PotentiallyGoodModel.V_good

/-! ### The tame valuation subring is a DVR — RELOCATED 2026-07-28

The five `TameBaseAux` declarations upgrading `tameSubring ℓ` to a discrete valuation
ring (`exists_valuation_eq_zpow`, `unif_mem`, `valuation_zpow_inj`,
`exists_valuation_eq_pow`, `tameSubring_hasUnitMulPow`, and the resulting
`instIsDiscreteValuationRingTameSubring`), together with `algebraMap_eq_ofQ` and the
finite-dimensionality of `ℚ(ℓ^{1/12})`, now live in
`Fermat/FLT/EllipticCurve/TorsionReduction.lean`, inside the `TameBaseAux` namespace
they belong to. They remain visible here through the `public import` of that module,
under the same names.

The move is not tidiness. `TameBase` and `TameGoodModel` now RECORD
`IsDiscreteValuationRing A` and `FiniteDimensional ℚ L` as fields, and a field of a
structure declared in `TorsionReduction.lean` has to be dischargeable there. That is
exactly what previously stopped a `TameGoodModel` from being transported into
`PotentiallyGoodModel` — see the note on `exists_potentiallyGoodModel_of_tameBase`
below. -/

/-- `ℓ`-integrality of a rational is exactly `ℓ ∤ den`. The argument is the one inside
`TameBaseAux.exists_intCast_sub_valuation_lt_one`, isolated so that both phrasings of
`j`-integrality — `0 ≤ padicValRat q j` here, `¬ q ∣ j.den` in
`padicValRat_Δ_le_of_jIntegral` — can be used interchangeably. -/
theorem WeierstrassCurve.TameBaseAux.not_dvd_den_of_padicValRat_nonneg {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] {x : ℚ} (hx : 0 ≤ padicValRat ℓ x) : ¬ (ℓ ∣ x.den) := by
  intro hdvd
  have hd1 : 1 ≤ padicValNat ℓ x.den := one_le_padicValNat_of_dvd x.den_nz hdvd
  have hnum1 : 1 ≤ padicValInt ℓ x.num := by
    have h := hx; rw [padicValRat_def] at h; omega
  have hnum0 : ℓ ∣ x.num.natAbs := by
    by_contra h
    have : padicValInt ℓ x.num = 0 := padicValNat.eq_zero_of_not_dvd h
    omega
  have h1 : ℓ = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left hnum0 x.reduced) hdvd
  exact hℓ.out.one_lt.ne' h1

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing in
/-- **An integral Weierstrass equation with unit discriminant is already minimal**
(PROVEN 2026-07-27). `valuation_Δ_aux` takes values in `{v // v ≤ 1}` by construction,
so an equation attaining `1` attains the maximum and no minimisation is needed. This is
the `Δ`-analogue of the project's `isMinimal_of_valuation_c₄_eq_one`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`) and is strictly
easier — good reduction is the one case where minimality is free. -/
theorem WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
  simpa [← integralModel_Δ_eq R (C • W)] using valuation_le_one (maximalIdeal R) _

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing in
/-- **An integral Weierstrass equation whose discriminant is a UNIT of `R` has good
reduction** (PROVEN 2026-07-27). Both fields of mathlib's `HasGoodReduction` come out of
the single hypothesis: `valuation_eq_one_iff_notMem` turns "unit of `R`" into
`valuation Δ = 1`, which is the `goodReduction` field, and minimality is then free by the
lemma above. This is the bridge that lets any explicit scaling argument — the tame one
below, and whatever the wild `q = 3` case eventually uses — hand over a
`PotentiallyGoodModel` without ever touching `IsMinimal`. -/
theorem WeierstrassCurve.hasGoodReduction_of_isUnit_Δ {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [IsIntegral R W] {r : R} (hr : algebraMap R K r = W.Δ)
    (hu : IsUnit r) : W.HasGoodReduction R := by
  have hΔ : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [← hr]
    refine (valuation_eq_one_iff_notMem (K := K) (v := maximalIdeal R)).mpr ?_
    simpa [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      using hu
  exact { toIsMinimal := WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one W hΔ,
          goodReduction := hΔ }

/-- **A local ring hom onto `ZMod q` identifies the residue field with `ZMod q`**
(PROVEN 2026-07-27). Injectivity is automatic (a ring hom out of a field), and
surjectivity is automatic too (`ZMod q` is generated by `1`), so `IsLocalHom` alone
upgrades `TameBaseAux.exists_tameResidueHom`'s hom into the `resEquiv` that
`PotentiallyGoodModel` asks for. Residue degree one is thereby carried across from the
`TameGoodModel` vocabulary to this one at no mathematical cost. -/
noncomputable def WeierstrassCurve.residueFieldEquivZModOfLocalHom {A : Type*} [CommRing A]
    [IsLocalRing A] {q : ℕ} [Fact q.Prime] (f : A →+* ZMod q) [IsLocalHom f] :
    IsLocalRing.ResidueField A ≃+* ZMod q := by
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, f a = 0 := by
    intro a ha
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal a).mp ha
      (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))
  refine RingEquiv.ofBijective (Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) f hker)
    ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := q) y
  exact ⟨(n : IsLocalRing.ResidueField A), by simp⟩

/-- **The assembly: a variable change with integral coefficients and INVERTIBLE
discriminant produces the datum** (PROVEN 2026-07-27). Everything about
`PotentiallyGoodModel` that is not arithmetic lives here, and nothing arithmetic does:
the caller supplies the number field, the DVR, the residue identification and the
variable change, and this turns them into the structure.

**THIS IS THE ENTRY POINT FOR THE WILD CASE `q = 3`.** Whoever attacks
`nonempty_translationDatum_three` should aim at exactly these six hypotheses over
whatever base that case needs; no part of the `HasGoodReduction` / `IsMinimal`
bookkeeping has to be redone. (For a curve already in short normal form the six
collapse to the four fields of `TranslationDatum` below, since `s = t = 0` is no loss
of generality — see that structure's docstring.)

Note `Δ ∈ A` is NOT a hypothesis — it follows from the five coefficient memberships,
since `Δ` is a polynomial in them — and `Δ ≠ 0` is not either, since `C • E_K` is
elliptic whenever `E` is. Only INVERTIBILITY of `Δ` in `A` is a real condition, and it
is the whole content of "good reduction". -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_integral
    {q : ℕ} [Fact q.Prime] (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    (C : VariableChange K)
    (ha₁ : (C • E.baseChange K).a₁ ∈ A) (ha₂ : (C • E.baseChange K).a₂ ∈ A)
    (ha₃ : (C • E.baseChange K).a₃ ∈ A) (ha₄ : (C • E.baseChange K).a₄ ∈ A)
    (ha₆ : (C • E.baseChange K).a₆ ∈ A)
    (haΔinv : ((C • E.baseChange K).Δ)⁻¹ ∈ A) :
    Nonempty (E.PotentiallyGoodModel q) := by
  classical
  set V : WeierstrassCurve K := C • (E.baseChange K) with hV
  haveI : (E.baseChange K).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ K)).IsElliptic
  haveI hVell : V.IsElliptic := by rw [hV]; infer_instance
  have hVΔne : V.Δ ≠ 0 := V.isUnit_Δ.ne_zero
  set ι : A →+* K := SubringClass.subtype A with hι
  set VA : WeierstrassCurve A :=
    ⟨⟨V.a₁, ha₁⟩, ⟨V.a₂, ha₂⟩, ⟨V.a₃, ha₃⟩, ⟨V.a₄, ha₄⟩, ⟨V.a₆, ha₆⟩⟩ with hVA
  have hVAmap : VA.map ι = V := rfl
  have hVAΔ : (VA.Δ : K) = V.Δ := by rw [← hVAmap, map_Δ]; rfl
  have hVAΔunit : IsUnit VA.Δ := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(V.Δ)⁻¹, haΔinv⟩, Subtype.ext ?_⟩
    show (VA.Δ : K) * (V.Δ)⁻¹ = 1
    rw [hVAΔ]
    exact mul_inv_cancel₀ hVΔne
  haveI hVint : IsIntegral A V := ⟨VA, hVAmap.symm⟩
  haveI hVgood : V.HasGoodReduction A :=
    WeierstrassCurve.hasGoodReduction_of_isUnit_Δ V (r := VA.Δ) hVAΔ hVAΔunit
  exact ⟨{ K := K
           R := A
           resEquiv := resEquiv
           V := V
           C := C
           V_eq := hV }⟩

/-- **The tame scaling** (PROVEN 2026-07-27): over a base of ramification index `12`,
a curve already in short Weierstrass form needs only the single variable change
`u = π^{v_q(Δ)}`, `r = s = t = 0`.

This is the same computation as `exists_tameGoodModel_of_isShortNF`
(`EllipticCurve/TorsionReduction.lean`) — deliberately so, and see
`PotentiallyGoodModel`'s docstring, which asks that the two structures NOT be
duplicated. What is not duplicated is the arithmetic: the base, the residue-degree-one
theorem and the two valuation inequalities are all TAKEN from
`EllipticCurve/TorsionReduction.lean`, and this file adds only the DVR upgrade and the
`HasGoodReduction` translation. Rewriting the eight-line scaling is what the
`TameGoodModel` docstring calls "the routine, but not free, translation"; the reason it
cannot be avoided is that `TameGoodModel` is stated with a `ValuationSubring` and an
abstract `IsReductionAlong`, and exposes neither the discreteness nor the
finite-dimensionality of its field, so its conclusion cannot be transported.

    v(V.a₄) = −4d + 12a ≥ 0  ⟺  3a ≥ d      (the `j`-integrality hypothesis)
    v(V.a₆) = −6d + 12b ≥ 0  ⟺  2b ≥ d      (free, by ultrametricity)
    v(V.Δ)  = −12d + 12d = 0                (always, by the CHOICE of `d`) -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_tameBase
    {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    (L : Type) [Field L] [DecidableEq L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    (π : L) (hπ0 : π ≠ 0)
    (hmem : ∀ (m : ℤ) {x : ℚ}, x ≠ 0 →
      (π ^ m * algebraMap ℚ L x ∈ A ↔ 0 ≤ m + 12 * padicValRat q x))
    (h4 : W.a₄ ≠ 0 → padicValRat q W.Δ ≤ 3 * padicValRat q W.a₄)
    (h6 : W.a₆ ≠ 0 → padicValRat q W.Δ ≤ 2 * padicValRat q W.a₆) :
    Nonempty (W.PotentiallyGoodModel q) := by
  classical
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set d : ℤ := padicValRat q W.Δ with hd
  have hπd : (π ^ d) ≠ 0 := zpow_ne_zero _ hπ0
  set u : Lˣ := Units.mk0 (π ^ d) hπd with hu
  set C : VariableChange L := ⟨u, 0, 0, 0⟩ with hC
  set V : WeierstrassCurve L := C • (W.baseChange L) with hV
  have hui : ∀ k : ℕ, ((u⁻¹ : Lˣ) : L) ^ k = π ^ (-(k : ℤ) * d) := by
    intro k
    rw [hu]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← zpow_natCast (π ^ d)⁻¹ k, ← zpow_neg, ← zpow_mul]
    ring_nf
  have hVa₁ : V.a₁ = 0 := by
    rw [hV, variableChange_a₁, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₂ : V.a₂ = 0 := by
    rw [hV, variableChange_a₂, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₃ : V.a₃ = 0 := by
    rw [hV, variableChange_a₃, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₄ : V.a₄ = π ^ (-4 * d) * algebraMap ℚ L W.a₄ := by
    rw [hV, variableChange_a₄, hC]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄,
      W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF, map_zero]
    rw [hui 4]; push_cast; ring
  have hVa₆ : V.a₆ = π ^ (-6 * d) * algebraMap ℚ L W.a₆ := by
    rw [hV, variableChange_a₆, hC]
    simp only [WeierstrassCurve.baseChange, map_a₂, map_a₃, map_a₄, map_a₆]
    rw [hui 6]; push_cast; ring
  have hVΔ : V.Δ = π ^ (-12 * d) * algebraMap ℚ L W.Δ := by
    rw [hV, variableChange_Δ, hC]
    simp only [WeierstrassCurve.baseChange, map_Δ]
    rw [hui 12]; push_cast; ring
  have hzero : (0 : L) ∈ A := zero_mem _
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_integral W L A resEquiv C
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hV, hVa₁]; exact hzero
  · rw [← hV, hVa₂]; exact hzero
  · rw [← hV, hVa₃]; exact hzero
  · rw [← hV]
    rcases eq_or_ne W.a₄ 0 with h0 | h0
    · rw [hVa₄, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₄, hmem _ h0]; have := h4 h0; omega
  · rw [← hV]
    rcases eq_or_ne W.a₆ 0 with h0 | h0
    · rw [hVa₆, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₆, hmem _ h0]; have := h6 h0; omega
  · rw [← hV]
    have hrw : (V.Δ)⁻¹ = π ^ (12 * d) * algebraMap ℚ L (W.Δ)⁻¹ := by
      rw [hVΔ, mul_inv, ← zpow_neg, map_inv₀]; ring_nf
    rw [hrw, hmem _ (inv_ne_zero hΔ0), padicValRat.inv]
    omega

/-- **The tame case at a curve in short Weierstrass form** (PROVEN 2026-07-27), obtained
by instantiating the scaling above at the concrete base `ℚ(q^{1/12})` of
`EllipticCurve/TorsionReduction.lean`. Three obligations are discharged here and nowhere
else:

* `FiniteDimensional ℚ L` — `TameBaseAux.instFiniteDimensional`. It comes from
  `TameBaseAux.exists_repr`: the twelve powers `1, π, …, π¹¹` span, so `⊤` is finitely
  generated. (No `PowerBasis` is used, for the same reason `exists_tameResidueHom`
  avoids one — the `Algebra ℚ` instance clash.) **As of 2026-07-28 both `TameBase` and
  `TameGoodModel` RECORD this**, so it no longer has to be reproved inline here, and the
  reason those two structures could not be transported into `PotentiallyGoodModel` is
  gone;
* the DVR structure — `TameBaseAux.instIsDiscreteValuationRingTameSubring`, likewise now
  a field of `TameBase`/`TameGoodModel`;
* residue degree one as a RING EQUIVALENCE —
  `residueFieldEquivZModOfLocalHom` applied to `TameBaseAux.exists_tameResidueHom`. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_isShortNF (W : WeierstrassCurve ℚ)
    [W.IsElliptic] [W.IsShortNF] {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q)
    (hj : ¬ (q ∣ W.j.den)) : Nonempty (W.PotentiallyGoodModel q) := by
  classical
  obtain ⟨h4, h6⟩ := WeierstrassCurve.padicValRat_Δ_le_of_jIntegral W hq5 hj
  obtain ⟨res, hres⟩ := TameBaseAux.exists_tameResidueHom q
  letI : DecidableEq (AdjoinRoot (TameBaseAux.qpoly q)) := Classical.decEq _
  haveI := hres
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_tameBase W
    (AdjoinRoot (TameBaseAux.qpoly q)) (TameBaseAux.tameSubring q)
    (WeierstrassCurve.residueFieldEquivZModOfLocalHom res) (TameBaseAux.unif q)
    (TameBaseAux.unif_ne_zero q) ?_ h4 h6
  intro m x hx
  rw [TameBaseAux.algebraMap_eq_ofQ]
  exact TameBaseAux.tame_mem_iff q m hx

/-- **The TAME half of the arithmetic leaf: `5 ≤ q` is PROVEN** (2026-07-27). The
reduction to short Weierstrass form is `E.toShortNF` (mathlib's `toShortNF_spec`;
`Invertible 2` and `Invertible 3` are free over `ℚ`), `variableChange_j` carries
`j`-integrality across, and the two variable changes compose by `mul_smul` and
`map_variableChange` — exactly as in `exists_tameGoodModel_of_jIntegral`, but with no
`emb` field to transport, so the composition is shorter here.

`5 ≤ q` is load-bearing exactly once, inside `padicValRat_Δ_le_of_jIntegral`: a prime
`≥ 5` divides no power of `2` and no power of `3`, hence kills the valuations of `4`,
`16`, `27` and `6912 = 2⁸·3³`. That is the ONLY use, and it is also exactly what fails
at `q = 3` — see the wild leaf below. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_five_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q)
    (hj : 0 ≤ padicValRat q E.j) : Nonempty (E.PotentiallyGoodModel q) := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  have hj0 : ¬ (q ∣ E.j.den) := TameBaseAux.not_dvd_den_of_padicValRat_nonneg hj
  have hj' : ¬ (q ∣ (E.toShortNF • E).j.den) := by rwa [variableChange_j]
  obtain ⟨N⟩ := WeierstrassCurve.exists_potentiallyGoodModel_of_isShortNF
    (E.toShortNF • E) hq5 hj'
  refine ⟨{
    K := N.K
    R := N.R
    resEquiv := N.resEquiv
    V := N.V
    C := N.C * (E.toShortNF.map (algebraMap ℚ N.K))
    V_eq := by
      have hmv : (E.toShortNF.map (algebraMap ℚ N.K)) • (E.baseChange N.K)
          = (E.toShortNF • E).baseChange N.K := map_variableChange _ _ _
      rw [N.V_eq, mul_smul, hmv] }⟩

/-- **The obligation the wild case `q = 3` owes, with every trace of reduction theory
removed** (opened 2026-07-27, when `exists_potentiallyGoodModel_of_jIntegral_three` was
decomposed). A `TranslationDatum W q` is: a number field `L`, a DVR valuation subring
`A ⊆ L` with residue field `ZMod q`, and **two field elements** `u ∈ Lˣ`, `r ∈ L` such
that the curve `y² = x³ + a₄x + a₆` becomes integral with invertible discriminant after
the variable change `(u, r, 0, 0)`. Nothing else: no `IsMinimal`, no `HasGoodReduction`,
no `IsIntegral`, no residue-field bookkeeping. Those all live in
`exists_potentiallyGoodModel_of_translationDatum` below, which is PROVEN.

The three membership conditions are literally the transformed coefficients

    a₂' = u⁻²·(3r),   a₄' = u⁻⁴·(a₄ + 3r²),   a₆' = u⁻⁶·(a₆ + r·a₄ + r³),

with `a₁' = a₃' = 0` free because `W` is in short normal form and `s = t = 0`, and
`hΔ` is `(Δ')⁻¹ ∈ A` for `Δ' = u⁻¹²·Δ`.

**WHY `s = t = 0` LOSES NOTHING — this is what makes the cut FAITHFUL, and it is not
obvious.** One direction is the theorem below. For the converse, suppose `W` (short)
acquires good reduction over `A` by some `C = (u, r, s, t)`, giving an integral `V` with
unit `Δ`. Complete the square: `C' = (1, 0, -V.a₁/2, -V.a₃/2)` is an integral change
(`2` is a unit of `A`, the residue characteristic being `3`), it preserves `Δ`, and
`C' • V` is still integral. Reading off `(C' * C) • W`: its `a₁` is `u''⁻¹·(0 + 2s'')`
and its `a₃` is `u''⁻³·(0 + 2t'')`, both zero, so `s'' = t'' = 0`. Hence
`Nonempty (TranslationDatum W q)` and `Nonempty (W.PotentiallyGoodModel q)` are
EQUIVALENT for `W` in short normal form — the structure is a faithful repackaging, not a
strengthening. In particular it is exactly as non-vacuous as `PotentiallyGoodModel`. -/
structure WeierstrassCurve.TranslationDatum (W : WeierstrassCurve ℚ)
    (q : ℕ) [Fact q.Prime] where
  /-- The number field over which `W` acquires good reduction. -/
  L : Type
  [instField : Field L]
  [instDec : DecidableEq L]
  [instAlgebra : Algebra ℚ L]
  [instFin : FiniteDimensional ℚ L]
  /-- The local ring at the chosen prime of `L` above `q`. -/
  A : ValuationSubring L
  [instDVR : IsDiscreteValuationRing A]
  /-- **Residue degree one**, exactly as in `PotentiallyGoodModel`. -/
  resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q
  /-- The scaling. `hΔ` forces `v(u) = v(Δ)/12`. -/
  u : Lˣ
  /-- The translation `x ↦ x + r`. It is what the tame case did not need and the wild
  case cannot avoid: over `𝔽₃` a curve with `a₁ = a₂ = a₃ = 0` has `c₄ = -48a₄ ≡ 0`,
  hence `j = 0`, so a good model of `j ≢ 0 (mod 3)` must move `a₂` off zero. -/
  r : L
  /-- `a₂'` is integral. -/
  ha₂ : ((u⁻¹ : Lˣ) : L) ^ 2 * (3 * r) ∈ A
  /-- `a₄'` is integral. -/
  ha₄ : ((u⁻¹ : Lˣ) : L) ^ 4 * (algebraMap ℚ L W.a₄ + 3 * r ^ 2) ∈ A
  /-- `a₆'` is integral. -/
  ha₆ : ((u⁻¹ : Lˣ) : L) ^ 6 *
    (algebraMap ℚ L W.a₆ + r * algebraMap ℚ L W.a₄ + r ^ 3) ∈ A
  /-- `Δ'` is a unit. -/
  hΔ : ((u : L)) ^ 12 * (algebraMap ℚ L W.Δ)⁻¹ ∈ A

attribute [instance] WeierstrassCurve.TranslationDatum.instField
  WeierstrassCurve.TranslationDatum.instDec
  WeierstrassCurve.TranslationDatum.instAlgebra
  WeierstrassCurve.TranslationDatum.instFin
  WeierstrassCurve.TranslationDatum.instDVR

/-- **A translation datum produces the good model** (PROVEN 2026-07-27). This is the
`q`-uniform half of the wild case, and it is pure bookkeeping over
`exists_potentiallyGoodModel_of_integral`: the variable change is `(u, r, 0, 0)`, the
`a₁` and `a₃` obligations are discharged by `IsShortNF`, and the other four are the
structure's own fields.

Nothing here is specific to `q = 3`; the statement is uniform in `q`. What is specific
to `q = 3` is that the datum is HARD TO BUILD — see
`nonempty_translationDatum_three`. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_translationDatum
    {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    (D : W.TranslationDatum q) : Nonempty (W.PotentiallyGoodModel q) := by
  classical
  set C : VariableChange D.L := ⟨D.u, D.r, 0, 0⟩ with hC
  have hb₁ : (W.baseChange D.L).a₁ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₂ : (W.baseChange D.L).a₂ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₃ : (W.baseChange D.L).a₃ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₄ : (W.baseChange D.L).a₄ = algebraMap ℚ D.L W.a₄ := rfl
  have hb₆ : (W.baseChange D.L).a₆ = algebraMap ℚ D.L W.a₆ := rfl
  have hbΔ : (W.baseChange D.L).Δ = algebraMap ℚ D.L W.Δ := by
    simp [WeierstrassCurve.baseChange, map_Δ]
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_integral W D.L D.A D.resEquiv C
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [variableChange_a₁, hC, hb₁]; simp
  · rw [variableChange_a₂, hC, hb₁, hb₂]
    simpa using D.ha₂
  · rw [variableChange_a₃, hC, hb₁, hb₃]; simp
  · rw [variableChange_a₄, hC, hb₁, hb₂, hb₃, hb₄]
    simpa using D.ha₄
  · rw [variableChange_a₆, hC, hb₁, hb₂, hb₃, hb₄, hb₆]
    simpa using D.ha₆
  · rw [variableChange_Δ, hC, hbΔ]
    simpa [mul_comm] using D.hΔ

/-! ### The wild case `q = 3`: two of the four conditions are FORCED, not owed

`TranslationDatum` asks for four things — integrality of `a₂'`, of `a₄'`, of `a₆'`, and
invertibility of `Δ'`. Two of them are not independent arithmetic demands at all: given
the OTHER two together with `0 ≤ v₃(j)`, they are THEOREMS.
`WeierstrassCurve.PreTranslationDatum` below drops them,
`WeierstrassCurve.translationDatum_of_pre` puts them back, and
`WeierstrassCurve.preTranslationDatum_of_translationDatum` proves the converse — so the
two structures are EQUIVALENT and the cut narrows nothing. Both directions are PROVEN
(2026-07-28); what remains open is `nonempty_preTranslationDatum_three_of_intCoeff_pos`,
the wild leaf that survives after the free rational scaling and the `d = 0` branch have
been peeled off (both PROVEN 2026-07-28, below).

The only bridge any of this needs between `padicValRat q` on `ℚ` and the valuation of the
big field `L` is the first lemma below: a rational whose denominator is prime to `q` is
integral at `A`. No comparison of value groups, no restriction of `v` to `ℚ`. -/

/-- **A natural number prime to `q` is a unit of any local ring whose residue field is
`ZMod q`** (PROVEN 2026-07-28). If it were not a unit it would lie in the maximal ideal,
so its residue would be `0`, so its image in `ZMod q` would be `0`, i.e. `q ∣ n`. -/
theorem WeierstrassCurve.TranslationAux.isUnit_natCast_of_not_dvd {q : ℕ} {L : Type*}
    [Field L] (A : ValuationSubring L) (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    {n : ℕ} (hn : ¬ (q ∣ n)) : IsUnit ((n : A)) := by
  by_contra h
  have hmem : (n : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h1 : IsLocalRing.residue A (n : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h2 : resEquiv (IsLocalRing.residue A (n : A)) = 0 := by rw [h1, map_zero]
  simp only [map_natCast] at h2
  exact hn ((ZMod.natCast_eq_zero_iff _ _).mp h2)

/-- **The reciprocal of a natural number prime to `q` is integral** (PROVEN 2026-07-28):
the inverse of the unit produced above, read back in `L`. -/
theorem WeierstrassCurve.TranslationAux.inv_natCast_mem {q : ℕ} {L : Type*} [Field L]
    (A : ValuationSubring L) (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    {n : ℕ} (hn : ¬ (q ∣ n)) : ((n : L))⁻¹ ∈ A := by
  obtain ⟨y, hy⟩ := WeierstrassCurve.TranslationAux.isUnit_natCast_of_not_dvd A resEquiv hn
  have h1 : (((y : Aˣ) : A) : L) = (n : L) := by rw [hy]; push_cast; ring
  have hmul : (((y⁻¹ : Aˣ) : A) : L) * ((n : L)) = 1 := by
    rw [← h1]
    have hyy : ((y⁻¹ : Aˣ) : A) * ((y : Aˣ) : A) = 1 := y.inv_mul
    calc (((y⁻¹ : Aˣ) : A) : L) * (((y : Aˣ) : A) : L)
        = (((y⁻¹ : Aˣ) * (y : Aˣ) : A) : L) := by push_cast; ring
      _ = 1 := by rw [hyy]; push_cast; ring
  rw [inv_eq_of_mul_eq_one_left hmul]
  exact SetLike.coe_mem _

/-- **`q`-integrality of a RATIONAL is membership of `A`** (PROVEN 2026-07-28). This is
the whole of the arithmetic input `0 ≤ padicValRat q x` contributes downstream: written as
`¬ q ∣ x.den` (which is what `TameBaseAux.not_dvd_den_of_padicValRat_nonneg` supplies), it
says `x = x.num · x.den⁻¹` with `x.num` integral and `x.den` a unit. -/
theorem WeierstrassCurve.TranslationAux.algebraMap_mem_of_not_dvd_den {q : ℕ} {L : Type*}
    [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q) {x : ℚ} (hx : ¬ (q ∣ x.den)) :
    algebraMap ℚ L x ∈ A := by
  have hnum : ((x.num : L)) ∈ A := intCast_mem A x.num
  have hden := WeierstrassCurve.TranslationAux.inv_natCast_mem A resEquiv hx
  have hx' : algebraMap ℚ L x = (x.num : L) * ((x.den : L))⁻¹ := by
    rw [eq_ratCast (algebraMap ℚ L) x, Rat.cast_def, div_eq_mul_inv]
  rw [hx']
  exact mul_mem hnum hden

/-- **`TranslationDatum` with the two forced conditions removed** (opened 2026-07-28).
The data are the same — a number field `L`, a DVR valuation subring `A ⊆ L` with residue
field `ZMod q`, a scaling `u ∈ Lˣ` and a translation `r ∈ L` — but only TWO of the four
conditions are asked for, and the `Δ`-condition is strengthened from an inequality to the
equality it always is:

* `hu`  : `v(u)¹² = v(Δ)`, i.e. `v(u) = v(Δ)/12` exactly;
* `ha₄` : `v(f'(r)) ≤ v(u)⁴` where `f = X³ + a₄X + a₆` (note `f'(r) = a₄ + 3r²`);
* `ha₆` : `v(f(r)) ≤ v(u)⁶`.

(Valuations are multiplicative here, so `≤` is the direction of INTEGRALITY: `v x ≤ 1`
means `x ∈ A`. Additively the two read `v(f'(r)) ≥ d/3` and `v(f(r)) ≥ d/2` for
`d = v₃(Δ)`.)

Dropped are `ha₂` — the integrality of `a₂' = u⁻²(3r)` — and `hΔ`. Both come back for
free: see `translationDatum_of_pre`, which is where `0 ≤ v₃(j)` is consumed, exactly
once. **The cut is faithful, not a narrowing**: the converse
`preTranslationDatum_of_translationDatum` is PROVEN, so `Nonempty (PreTranslationDatum W q)`
and `Nonempty (TranslationDatum W q)` are equivalent for `W` in short normal form (and the
latter is in turn equivalent to `Nonempty (W.PotentiallyGoodModel q)`, by that structure's
own docstring). -/
structure WeierstrassCurve.PreTranslationDatum (W : WeierstrassCurve ℚ)
    (q : ℕ) [Fact q.Prime] where
  /-- The number field over which `W` acquires good reduction. -/
  L : Type
  [instField : Field L]
  [instDec : DecidableEq L]
  [instAlgebra : Algebra ℚ L]
  [instFin : FiniteDimensional ℚ L]
  /-- The local ring at the chosen prime of `L` above `q`. -/
  A : ValuationSubring L
  [instDVR : IsDiscreteValuationRing A]
  /-- **Residue degree one**, exactly as in `TranslationDatum`. -/
  resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q
  /-- The scaling. -/
  u : Lˣ
  /-- The translation `x ↦ x + r`. -/
  r : L
  /-- `v(u) = v(Δ)/12`, on the nose. -/
  hu : A.valuation ((u : L)) ^ 12 = A.valuation (algebraMap ℚ L W.Δ)
  /-- `v(f'(r)) ≥ d/3`. -/
  ha₄ : A.valuation (algebraMap ℚ L W.a₄ + 3 * r ^ 2) ≤ A.valuation ((u : L)) ^ 4
  /-- `v(f(r)) ≥ d/2`. -/
  ha₆ : A.valuation (algebraMap ℚ L W.a₆ + r * algebraMap ℚ L W.a₄ + r ^ 3)
    ≤ A.valuation ((u : L)) ^ 6

attribute [instance] WeierstrassCurve.PreTranslationDatum.instField
  WeierstrassCurve.PreTranslationDatum.instDec
  WeierstrassCurve.PreTranslationDatum.instAlgebra
  WeierstrassCurve.PreTranslationDatum.instFin
  WeierstrassCurve.PreTranslationDatum.instDVR

/-- **The two dropped conditions come back for free, and this is the ONLY place
`0 ≤ v₃(j)` is used** (PROVEN 2026-07-28).

`hΔ` is immediate from `hu`. For `ha₂` the argument is the one sketched in the old
docstring of `nonempty_translationDatum_three`, made exact. Write `v` multiplicatively
(so `v x ≤ 1` is integrality) and `w = v(u)`; then:

* `j`-integrality is the single membership `27a₄³/Δ ∈ A`. Indeed `c₄ = -48a₄` for a short
  model, so `j = c₄³/Δ = -2¹²·27a₄³/Δ`, i.e. `27a₄³/Δ = -j/4096`; and `j ∈ A` because
  `¬ 3 ∣ j.den`, while `4096⁻¹ ∈ A` because `¬ 3 ∣ 4096`. Multiplicatively that reads
  `v(3)³·v(a₄)³ ≤ v(Δ)`.
* With `v(Δ) = w¹²` this gives `(v(3)·v(a₄))³ ≤ (w⁴)³`, hence `v(3)·v(a₄) ≤ w⁴` (cubing is
  order-reflecting in a linearly ordered group with zero).
* `3r² = (a₄ + 3r²) - a₄`, so `v(3r²) ≤ max(w⁴, v(a₄))` by the ultrametric inequality, and
  therefore `v(3r)² = v(3)·v(3r²) ≤ max(v(3)·w⁴, v(3)·v(a₄)) ≤ w⁴ = (w²)²`, using
  `v(3) ≤ 1` on the left branch and the previous bullet on the right.
* Squaring is order-reflecting too, so `v(3r) ≤ w²`, which is `ha₂`.

Additively: `v₃(j) ≥ 0` says `v(a₄) ≥ d/3 − 1` (because `v₃(48) = 1`), and combined with
`v(f'(r)) ≥ d/3` that forces `v(3r) ≥ d/6`. -/
theorem WeierstrassCurve.translationDatum_of_pre (W : WeierstrassCurve ℚ) [W.IsElliptic]
    [W.IsShortNF] {q : ℕ} [Fact q.Prime] (hq3 : q = 3) (hj : 0 ≤ padicValRat q W.j)
    (D : W.PreTranslationDatum q) : Nonempty (W.TranslationDatum q) := by
  subst hq3
  classical
  have hjden : ¬ (3 ∣ W.j.den) := TameBaseAux.not_dvd_den_of_padicValRat_nonneg hj
  set v := D.A.valuation with hvdef
  set w := v ((D.u : D.L)) with hwdef
  have hu0 : ((D.u : D.L)) ≠ 0 := D.u.ne_zero
  have hw0 : w ≠ 0 := by rw [hwdef]; exact (Valuation.ne_zero_iff v).mpr hu0
  have hinv : v (((D.u⁻¹ : D.Lˣ) : D.L)) = w⁻¹ := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [hwdef, ← Valuation.map_mul]
    have h1 : ((D.u⁻¹ : D.Lˣ) : D.L) * ((D.u : D.Lˣ) : D.L) = 1 := D.u.inv_mul
    rw [h1, Valuation.map_one]
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hΔL : algebraMap ℚ D.L W.Δ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ D.L).injective).mpr hΔ0
  have hvΔ0 : v (algebraMap ℚ D.L W.Δ) ≠ 0 := (Valuation.ne_zero_iff v).mpr hΔL
  have hinvΔ : v ((algebraMap ℚ D.L W.Δ)⁻¹) = (v (algebraMap ℚ D.L W.Δ))⁻¹ := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← Valuation.map_mul, inv_mul_cancel₀ hΔL, Valuation.map_one]
  have h3mem : (3 : D.L) ∈ D.A := by simp
  have h3 : v (3 : D.L) ≤ 1 := (D.A.valuation_le_one_iff _).mpr h3mem
  have hjmem : algebraMap ℚ D.L W.j ∈ D.A :=
    WeierstrassCurve.TranslationAux.algebraMap_mem_of_not_dvd_den D.A D.resEquiv hjden
  have h4096 : ((4096 : ℕ) : D.L)⁻¹ ∈ D.A :=
    WeierstrassCurve.TranslationAux.inv_natCast_mem D.A D.resEquiv (n := 4096) (by decide)
  have hjq : W.j = W.Δ⁻¹ * W.c₄ ^ 3 := by
    simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  have hid : (27 * W.a₄ ^ 3 / W.Δ : ℚ) = -W.j / 4096 := by
    rw [hjq, WeierstrassCurve.c₄_of_isShortNF]
    field_simp
    ring
  have hmem : algebraMap ℚ D.L (27 * W.a₄ ^ 3 / W.Δ) ∈ D.A := by
    rw [hid]
    have hc : ((4096 : ℕ) : D.L) = algebraMap ℚ D.L (4096 : ℚ) := by
      rw [map_ofNat]
      norm_num
    have he : algebraMap ℚ D.L (-W.j / 4096)
        = -(algebraMap ℚ D.L W.j) * (((4096 : ℕ) : D.L))⁻¹ := by
      rw [map_div₀, map_neg, hc, div_eq_mul_inv]
    rw [he]
    exact mul_mem (neg_mem hjmem) h4096
  have hkey : v (3 : D.L) ^ 3 * v (algebraMap ℚ D.L W.a₄) ^ 3
      ≤ v (algebraMap ℚ D.L W.Δ) := by
    have e : (27 * W.a₄ ^ 3 : ℚ) = (27 * W.a₄ ^ 3 / W.Δ) * W.Δ := by field_simp
    have e2 : v (algebraMap ℚ D.L (27 * W.a₄ ^ 3))
        = v (3 : D.L) ^ 3 * v (algebraMap ℚ D.L W.a₄) ^ 3 := by
      have e3 : algebraMap ℚ D.L (27 * W.a₄ ^ 3)
          = (3 : D.L) ^ 3 * (algebraMap ℚ D.L W.a₄) ^ 3 := by
        rw [map_mul, map_pow]
        norm_num
      rw [e3, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
    rw [← e2]
    calc v (algebraMap ℚ D.L (27 * W.a₄ ^ 3))
        = v (algebraMap ℚ D.L ((27 * W.a₄ ^ 3 / W.Δ) * W.Δ)) := by rw [← e]
      _ = v (algebraMap ℚ D.L (27 * W.a₄ ^ 3 / W.Δ)) * v (algebraMap ℚ D.L W.Δ) := by
          rw [map_mul, Valuation.map_mul]
      _ ≤ 1 * v (algebraMap ℚ D.L W.Δ) := by
          gcongr
          exact (D.A.valuation_le_one_iff _).mpr hmem
      _ = v (algebraMap ℚ D.L W.Δ) := one_mul _
  have hstep : v (3 : D.L) * v (algebraMap ℚ D.L W.a₄) ≤ w ^ 4 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) zero_le ?_
    calc (v (3 : D.L) * v (algebraMap ℚ D.L W.a₄)) ^ 3
        = v (3 : D.L) ^ 3 * v (algebraMap ℚ D.L W.a₄) ^ 3 := by rw [mul_pow]
      _ ≤ v (algebraMap ℚ D.L W.Δ) := hkey
      _ = w ^ 12 := D.hu.symm
      _ = (w ^ 4) ^ 3 := by rw [← pow_mul]
  have hsub : v ((3 : D.L) * D.r ^ 2)
      ≤ max (w ^ 4) (v (algebraMap ℚ D.L W.a₄)) := by
    have e : (3 : D.L) * D.r ^ 2
        = (algebraMap ℚ D.L W.a₄ + 3 * D.r ^ 2) - algebraMap ℚ D.L W.a₄ := by ring
    rw [e]
    exact le_trans (Valuation.map_sub _ _ _) (max_le_max D.ha₄ le_rfl)
  have hmain : v ((3 : D.L) * D.r) ≤ w ^ 2 := by
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) zero_le ?_
    have e : v ((3 : D.L) * D.r) ^ 2 = v (3 : D.L) * v ((3 : D.L) * D.r ^ 2) := by
      rw [← Valuation.map_pow, ← Valuation.map_mul]
      congr 1
      ring
    rw [e, show (w ^ 2) ^ 2 = w ^ 4 by rw [← pow_mul]]
    calc v (3 : D.L) * v ((3 : D.L) * D.r ^ 2)
        ≤ v (3 : D.L) * max (w ^ 4) (v (algebraMap ℚ D.L W.a₄)) := by gcongr
      _ ≤ w ^ 4 := by
          rcases max_cases (w ^ 4) (v (algebraMap ℚ D.L W.a₄)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
          · exact le_trans (by gcongr) (le_of_eq (one_mul (w ^ 4)))
          · exact hstep
  refine ⟨{
    L := D.L
    instField := D.instField
    instDec := D.instDec
    instAlgebra := D.instAlgebra
    instFin := D.instFin
    A := D.A
    instDVR := D.instDVR
    resEquiv := D.resEquiv
    u := D.u
    r := D.r
    ha₂ := ?_
    ha₄ := ?_
    ha₆ := ?_
    hΔ := ?_ }⟩
  · rw [← D.A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_pow, hinv, inv_pow]
    calc (w ^ 2)⁻¹ * v ((3 : D.L) * D.r) ≤ (w ^ 2)⁻¹ * w ^ 2 := by gcongr
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hw0)
  · rw [← D.A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_pow, hinv, inv_pow]
    calc (w ^ 4)⁻¹ * v (algebraMap ℚ D.L W.a₄ + 3 * D.r ^ 2)
        ≤ (w ^ 4)⁻¹ * w ^ 4 := by gcongr; exact D.ha₄
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hw0)
  · rw [← D.A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_pow, hinv, inv_pow]
    calc (w ^ 6)⁻¹ * v (algebraMap ℚ D.L W.a₆ + D.r * algebraMap ℚ D.L W.a₄ + D.r ^ 3)
        ≤ (w ^ 6)⁻¹ * w ^ 6 := by gcongr; exact D.ha₆
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hw0)
  · rw [← D.A.valuation_le_one_iff, Valuation.map_mul, Valuation.map_pow, hinvΔ, ← hwdef,
      D.hu]
    exact le_of_eq (mul_inv_cancel₀ hvΔ0)

/-- **THE CUT IS FAITHFUL: the converse holds, with no hypothesis at all** (PROVEN
2026-07-28, and uniform in `q`). Given a `TranslationDatum`, the discriminant of the
transformed curve, `Δ' = u⁻¹²Δ`, is the `ℤ`-polynomial

    Δ' = -64a₂'³a₆' + 16a₂'²a₄'² - 64a₄'³ - 432a₆'² + 288a₂'a₄'a₆'

in the three transformed coefficients (mathlib's `Δ_of_isCharNeTwoNF`, valid because
`a₁' = a₃' = 0`), so `Δ' ∈ A` follows from `ha₂`, `ha₄`, `ha₆` alone — no minimality, no
reduction theory. That gives `v(Δ) ≤ v(u)¹²`, while `hΔ` gives `v(u)¹² ≤ v(Δ)`; hence the
EQUALITY that `PreTranslationDatum.hu` asks for. Its `ha₄` and `ha₆` are then just `hΔ`'s
siblings rewritten as valuation inequalities.

So `Nonempty (W.PreTranslationDatum q) ↔ Nonempty (W.TranslationDatum q)` for `W` in short
normal form: dropping `ha₂` and weakening `hΔ` to an equality on `v(u)` LOSES NOTHING, and
the residual leaf below is exactly as strong (and exactly as non-vacuous) as the one it
replaces. -/
theorem WeierstrassCurve.preTranslationDatum_of_translationDatum (W : WeierstrassCurve ℚ)
    [W.IsElliptic] [W.IsShortNF] {q : ℕ} [Fact q.Prime] (D : W.TranslationDatum q) :
    Nonempty (W.PreTranslationDatum q) := by
  classical
  set v := D.A.valuation with hvdef
  set X := ((D.u⁻¹ : D.Lˣ) : D.L) with hXdef
  set w := v ((D.u : D.L)) with hwdef
  have hu0 : ((D.u : D.L)) ≠ 0 := D.u.ne_zero
  have hw0 : w ≠ 0 := by rw [hwdef]; exact (Valuation.ne_zero_iff v).mpr hu0
  have hinv : v X = w⁻¹ := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [hwdef, ← Valuation.map_mul, hXdef, D.u.inv_mul, Valuation.map_one]
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hΔL : algebraMap ℚ D.L W.Δ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ D.L).injective).mpr hΔ0
  have hvΔ0 : v (algebraMap ℚ D.L W.Δ) ≠ 0 := (Valuation.ne_zero_iff v).mpr hΔL
  have hinvΔ : v ((algebraMap ℚ D.L W.Δ)⁻¹) = (v (algebraMap ℚ D.L W.Δ))⁻¹ := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← Valuation.map_mul, inv_mul_cancel₀ hΔL, Valuation.map_one]
  have hcancel : ∀ a b : D.A.ValueGroup, b ≠ 0 → a * b⁻¹ ≤ 1 → a ≤ b := by
    intro a b hb h
    calc a = a * b⁻¹ * b := by rw [inv_mul_cancel_right₀ hb]
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
  have hΔeq : algebraMap ℚ D.L W.Δ
      = -16 * (4 * (algebraMap ℚ D.L W.a₄) ^ 3 + 27 * (algebraMap ℚ D.L W.a₆) ^ 2) := by
    rw [WeierstrassCurve.Δ_of_isShortNF]
    simp only [map_mul, map_add, map_pow, map_neg, map_ofNat]
  have hmemΔ : X ^ 12 * (algebraMap ℚ D.L W.Δ) ∈ D.A := by
    have h64 : ((64 : D.L)) ∈ D.A := by simp
    have h16 : ((16 : D.L)) ∈ D.A := by simp
    have h432 : ((432 : D.L)) ∈ D.A := by simp
    have h288 : ((288 : D.L)) ∈ D.A := by simp
    have key : X ^ 12 * (algebraMap ℚ D.L W.Δ)
        = -(64 * (X ^ 2 * (3 * D.r)) ^ 3
              * (X ^ 6 * (algebraMap ℚ D.L W.a₆ + D.r * algebraMap ℚ D.L W.a₄ + D.r ^ 3)))
          + 16 * (X ^ 2 * (3 * D.r)) ^ 2
              * (X ^ 4 * (algebraMap ℚ D.L W.a₄ + 3 * D.r ^ 2)) ^ 2
          - 64 * (X ^ 4 * (algebraMap ℚ D.L W.a₄ + 3 * D.r ^ 2)) ^ 3
          - 432 * (X ^ 6 * (algebraMap ℚ D.L W.a₆ + D.r * algebraMap ℚ D.L W.a₄ + D.r ^ 3)) ^ 2
          + 288 * ((X ^ 2 * (3 * D.r))
              * (X ^ 4 * (algebraMap ℚ D.L W.a₄ + 3 * D.r ^ 2))
              * (X ^ 6 * (algebraMap ℚ D.L W.a₆ + D.r * algebraMap ℚ D.L W.a₄ + D.r ^ 3))) := by
      rw [hΔeq]
      ring
    rw [key]
    exact add_mem (sub_mem (sub_mem
      (add_mem (neg_mem (mul_mem (mul_mem h64 (pow_mem D.ha₂ 3)) D.ha₆))
        (mul_mem (mul_mem h16 (pow_mem D.ha₂ 2)) (pow_mem D.ha₄ 2)))
      (mul_mem h64 (pow_mem D.ha₄ 3))) (mul_mem h432 (pow_mem D.ha₆ 2)))
      (mul_mem h288 (mul_mem (mul_mem D.ha₂ D.ha₄) D.ha₆))
  refine ⟨{
    L := D.L
    instField := D.instField
    instDec := D.instDec
    instAlgebra := D.instAlgebra
    instFin := D.instFin
    A := D.A
    instDVR := D.instDVR
    resEquiv := D.resEquiv
    u := D.u
    r := D.r
    hu := ?_
    ha₄ := ?_
    ha₆ := ?_ }⟩
  · refine le_antisymm ?_ ?_
    · refine hcancel _ _ hvΔ0 ?_
      have h := (D.A.valuation_le_one_iff _).mpr D.hΔ
      rwa [Valuation.map_mul, Valuation.map_pow, hinvΔ, ← hwdef] at h
    · refine hcancel _ _ (pow_ne_zero 12 hw0) ?_
      have h := (D.A.valuation_le_one_iff _).mpr hmemΔ
      rw [Valuation.map_mul, Valuation.map_pow, hinv, inv_pow] at h
      rwa [mul_comm] at h
  · refine hcancel _ _ (pow_ne_zero 4 hw0) ?_
    have h := (D.A.valuation_le_one_iff _).mpr D.ha₄
    rw [Valuation.map_mul, Valuation.map_pow, hinv, inv_pow] at h
    rwa [mul_comm] at h
  · refine hcancel _ _ (pow_ne_zero 6 hw0) ?_
    have h := (D.A.valuation_le_one_iff _).mpr D.ha₆
    rw [Valuation.map_mul, Valuation.map_pow, hinv, inv_pow] at h
    rwa [mul_comm] at h

/-- **THE LEAF IS INVARIANT UNDER RATIONAL SCALING** (PROVEN 2026-07-28). For `c ∈ ℚˣ`
let `W'` be the short curve with `a₄ ↦ c⁴a₄`, `a₆ ↦ c⁶a₆` (so `Δ ↦ c¹²Δ`, and `j` is
unchanged). A `PreTranslationDatum` for `W'` with data `(u', r')` produces one for `W`
over the SAME base, with `(u, r) = (u'/c, r'/c²)`: each of `hu`, `ha₄`, `ha₆` is
homogeneous of the matching weight, so the three transform by the single factors
`v(c)¹²`, `v(c)⁴`, `v(c)⁶` respectively and the two inequalities are untouched.

`hΔ : W'.Δ = c¹²Δ` is taken as a HYPOTHESIS rather than derived, which makes the lemma
instance-free; the caller discharges it from `Δ_of_isShortNF` with one `ring`.

This is what reduces the wild leaf to `a₄, a₆ ∈ ℤ` — take `c = a₄.den · a₆.den`. See
`nonempty_preTranslationDatum_three` below. -/
theorem WeierstrassCurve.preTranslationDatum_of_scale {q : ℕ} [Fact q.Prime]
    (W W' : WeierstrassCurve ℚ) {c : ℚ} (hc : c ≠ 0)
    (h4 : W'.a₄ = c ^ 4 * W.a₄) (h6 : W'.a₆ = c ^ 6 * W.a₆) (hΔ : W'.Δ = c ^ 12 * W.Δ)
    (D : W'.PreTranslationDatum q) : Nonempty (W.PreTranslationDatum q) := by
  classical
  have hγ0 : algebraMap ℚ D.L c ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ D.L).injective).mpr hc
  set γ : D.L := algebraMap ℚ D.L c with hγdef
  set v := D.A.valuation with hvdef
  set g := v γ with hgdef
  set w := v ((D.u : D.L)) with hwdef
  have hg0 : g ≠ 0 := by rw [hgdef]; exact (Valuation.ne_zero_iff v).mpr hγ0
  have hinvg : v (γ⁻¹) = g⁻¹ := by
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [hgdef, ← Valuation.map_mul, inv_mul_cancel₀ hγ0, Valuation.map_one]
  have h4L : algebraMap ℚ D.L W'.a₄ = γ ^ 4 * algebraMap ℚ D.L W.a₄ := by
    rw [h4, map_mul, map_pow, hγdef]
  have h6L : algebraMap ℚ D.L W'.a₆ = γ ^ 6 * algebraMap ℚ D.L W.a₆ := by
    rw [h6, map_mul, map_pow, hγdef]
  have hΔL : algebraMap ℚ D.L W'.Δ = γ ^ 12 * algebraMap ℚ D.L W.Δ := by
    rw [hΔ, map_mul, map_pow, hγdef]
  have hcoe : ((D.u * (Units.mk0 γ hγ0)⁻¹ : D.Lˣ) : D.L) = (D.u : D.L) * γ⁻¹ := by
    simp
  refine ⟨{
    L := D.L
    instField := D.instField
    instDec := D.instDec
    instAlgebra := D.instAlgebra
    instFin := D.instFin
    A := D.A
    instDVR := D.instDVR
    resEquiv := D.resEquiv
    u := D.u * (Units.mk0 γ hγ0)⁻¹
    r := D.r / γ ^ 2
    hu := ?_
    ha₄ := ?_
    ha₆ := ?_ }⟩
  · rw [hcoe, Valuation.map_mul, hinvg, ← hwdef, mul_pow, inv_pow]
    calc w ^ 12 * (g ^ 12)⁻¹ = v (algebraMap ℚ D.L W'.Δ) * (g ^ 12)⁻¹ := by rw [D.hu]
      _ = g ^ 12 * v (algebraMap ℚ D.L W.Δ) * (g ^ 12)⁻¹ := by
          rw [hΔL, Valuation.map_mul, Valuation.map_pow, ← hgdef]
      _ = v (algebraMap ℚ D.L W.Δ) := by
          rw [mul_comm (g ^ 12) _, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 12 hg0), mul_one]
  · have hid : algebraMap ℚ D.L W.a₄ + 3 * (D.r / γ ^ 2) ^ 2
        = (γ ^ 4)⁻¹ * (algebraMap ℚ D.L W'.a₄ + 3 * D.r ^ 2) := by
      rw [h4L]; field_simp
    rw [hid, hcoe, Valuation.map_mul, Valuation.map_mul, hinvg, ← hwdef, mul_pow, inv_pow]
    have hvinv : v ((γ ^ 4)⁻¹) = (g ^ 4)⁻¹ := by
      rw [← inv_pow, Valuation.map_pow, hinvg, inv_pow]
    rw [hvinv]
    calc (g ^ 4)⁻¹ * v (algebraMap ℚ D.L W'.a₄ + 3 * D.r ^ 2)
        ≤ (g ^ 4)⁻¹ * w ^ 4 := by gcongr; exact D.ha₄
      _ = w ^ 4 * (g ^ 4)⁻¹ := mul_comm _ _
  · have hid : algebraMap ℚ D.L W.a₆ + (D.r / γ ^ 2) * algebraMap ℚ D.L W.a₄
          + (D.r / γ ^ 2) ^ 3
        = (γ ^ 6)⁻¹ * (algebraMap ℚ D.L W'.a₆ + D.r * algebraMap ℚ D.L W'.a₄ + D.r ^ 3) := by
      rw [h4L, h6L]; field_simp
    rw [hid, hcoe, Valuation.map_mul, Valuation.map_mul, hinvg, ← hwdef, mul_pow, inv_pow]
    have hvinv : v ((γ ^ 6)⁻¹) = (g ^ 6)⁻¹ := by
      rw [← inv_pow, Valuation.map_pow, hinvg, inv_pow]
    rw [hvinv]
    calc (g ^ 6)⁻¹ * v (algebraMap ℚ D.L W'.a₆ + D.r * algebraMap ℚ D.L W'.a₄ + D.r ^ 3)
        ≤ (g ^ 6)⁻¹ * w ^ 6 := by gcongr; exact D.ha₆
      _ = w ^ 6 * (g ^ 6)⁻¹ := mul_comm _ _

/-- **The tame base produces the datum whenever `r = 0` already works** (PROVEN
2026-07-28), and it is the exact analogue of `exists_potentiallyGoodModel_of_tameBase`
one level down. Over a base of ramification index `12` at `q`, take `u = π^{v_q(Δ)}` and
`r = 0`; the four MEMBERSHIP conditions of `TranslationDatum` then read

    a₂' = u⁻²·(3·0) = 0                    (always, since `r = 0`)
    v(a₄') = −4d + 12a ≥ 0  ⟺  3a ≥ d      (hypothesis `h4`)
    v(a₆') = −6d + 12b ≥ 0  ⟺  2b ≥ d      (hypothesis `h6`)
    v(Δ')  = −12d + 12d = 0                (always, by the CHOICE of `d`)

and `preTranslationDatum_of_translationDatum` — PROVEN above, hypothesis-free and uniform
in `q` — converts the result. So this route needs no valuation-group equality anywhere:
every obligation is `∈ A`, which is exactly what `TameBaseAux.tame_mem_iff` decides.

Nothing here is specific to `q = 3`. At `5 ≤ q` the two hypotheses are FREE from
`0 ≤ v_q(j)` (that is `padicValRat_Δ_le_of_jIntegral`); at `q = 3` they are not, and the
case where they FAIL is the whole of what is left open. -/
theorem WeierstrassCurve.preTranslationDatum_of_tameBase {q : ℕ} [Fact q.Prime]
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    (L : Type) [Field L] [DecidableEq L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    (π : L) (hπ0 : π ≠ 0)
    (hmem : ∀ (m : ℤ) {x : ℚ}, x ≠ 0 →
      (π ^ m * algebraMap ℚ L x ∈ A ↔ 0 ≤ m + 12 * padicValRat q x))
    (h4 : W.a₄ ≠ 0 → padicValRat q W.Δ ≤ 3 * padicValRat q W.a₄)
    (h6 : W.a₆ ≠ 0 → padicValRat q W.Δ ≤ 2 * padicValRat q W.a₆) :
    Nonempty (W.PreTranslationDatum q) := by
  classical
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set d : ℤ := padicValRat q W.Δ with hd
  have hπd : (π ^ d) ≠ 0 := zpow_ne_zero _ hπ0
  set u : Lˣ := Units.mk0 (π ^ d) hπd with hu
  have hui : ∀ k : ℕ, ((u⁻¹ : Lˣ) : L) ^ k = π ^ (-(k : ℤ) * d) := by
    intro k
    rw [hu]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← zpow_natCast (π ^ d)⁻¹ k, ← zpow_neg, ← zpow_mul]
    ring_nf
  have huk : ∀ k : ℕ, ((u : Lˣ) : L) ^ k = π ^ ((k : ℤ) * d) := by
    intro k
    rw [hu]
    simp only [Units.val_mk0]
    rw [← zpow_natCast (π ^ d) k, ← zpow_mul]
    ring_nf
  refine WeierstrassCurve.preTranslationDatum_of_translationDatum W
    { L := L
      A := A
      resEquiv := resEquiv
      u := u
      r := 0
      ha₂ := ?_
      ha₄ := ?_
      ha₆ := ?_
      hΔ := ?_ }
  · simp
  · rcases eq_or_ne W.a₄ 0 with h0 | h0
    · simp [h0]
    · have e : ((u⁻¹ : Lˣ) : L) ^ 4 * (algebraMap ℚ L W.a₄ + 3 * (0 : L) ^ 2)
          = π ^ (-4 * d) * algebraMap ℚ L W.a₄ := by
        rw [hui 4]; push_cast; ring
      rw [e, hmem _ h0]
      have := h4 h0
      omega
  · rcases eq_or_ne W.a₆ 0 with h0 | h0
    · simp [h0]
    · have e : ((u⁻¹ : Lˣ) : L) ^ 6
            * (algebraMap ℚ L W.a₆ + (0 : L) * algebraMap ℚ L W.a₄ + (0 : L) ^ 3)
          = π ^ (-6 * d) * algebraMap ℚ L W.a₆ := by
        rw [hui 6]; push_cast; ring
      rw [e, hmem _ h0]
      have := h6 h0
      omega
  · have e : ((u : Lˣ) : L) ^ 12 * (algebraMap ℚ L W.Δ)⁻¹
        = π ^ (12 * d) * algebraMap ℚ L (W.Δ)⁻¹ := by
      rw [huk 12, map_inv₀]; push_cast; ring
    rw [e, hmem _ (inv_ne_zero hΔ0), padicValRat.inv]
    omega

/-- **The concrete tame instantiation, at the level of `PreTranslationDatum`** (PROVEN
2026-07-28). The base is `ℚ(q^{1/12})`, exactly as in
`exists_potentiallyGoodModel_of_isShortNF`, and the three non-arithmetic obligations —
`FiniteDimensional ℚ L`, the DVR structure, and residue degree one AS A RING EQUIVALENCE —
are discharged by the same three `TameBaseAux` facts that theorem uses. -/
theorem WeierstrassCurve.nonempty_preTranslationDatum_of_padicValRat_le
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF] {q : ℕ} [Fact q.Prime]
    (h4 : W.a₄ ≠ 0 → padicValRat q W.Δ ≤ 3 * padicValRat q W.a₄)
    (h6 : W.a₆ ≠ 0 → padicValRat q W.Δ ≤ 2 * padicValRat q W.a₆) :
    Nonempty (W.PreTranslationDatum q) := by
  classical
  obtain ⟨res, hres⟩ := TameBaseAux.exists_tameResidueHom q
  letI : DecidableEq (AdjoinRoot (TameBaseAux.qpoly q)) := Classical.decEq _
  haveI := hres
  refine WeierstrassCurve.preTranslationDatum_of_tameBase W
    (AdjoinRoot (TameBaseAux.qpoly q)) (TameBaseAux.tameSubring q)
    (WeierstrassCurve.residueFieldEquivZModOfLocalHom res) (TameBaseAux.unif q)
    (TameBaseAux.unif_ne_zero q) ?_ h4 h6
  intro m x hx
  rw [TameBaseAux.algebraMap_eq_ofQ]
  exact TameBaseAux.tame_mem_iff q m hx

/-- **THE ARITHMETIC OF THE WILD CASE `q = 3`** (sorry leaf; opened 2026-07-27 by
decomposing `exists_potentiallyGoodModel_of_jIntegral_three`, RESTATED 2026-07-28 over
`PreTranslationDatum` once the two forced conditions were discharged, and RESTATED AGAIN
2026-07-28 with the two free reductions below taken). What is owed is a
base `L` with a residue-degree-`1` DVR at `3`, plus **two elements** `u, r` of `L`
satisfying just TWO valuation inequalities. Write `A = W.a₄`, `B = W.a₆`,
`f(X) = X³ + AX + B`, `d = v₃(Δ)`. Since `hu` pins `v(u) = d/12`, they are

    (ii)  v(f'(r)) = v(A + 3r²)  ≥ d/3,
    (iii) v(f(r))               ≥ d/2.

The third condition of the older statement, `(i) v(3r) ≥ d/6`, is **no longer owed**: it
follows from (ii) and `0 ≤ v₃(j)`, and that derivation is
`WeierstrassCurve.translationDatum_of_pre`, PROVEN above. So is the invertibility of `Δ'`.
Nothing is lost by the cut — `preTranslationDatum_of_translationDatum` is the converse.

**OBSTRUCTION 3 OF THE ORIGINAL DOCSTRING IS SETTLED, AND IT IS A REFUTATION.**
`TameBaseAux`'s base `ℚ(3^{1/12})` is NOT large enough at `q = 3`. The old text called
this "an open question, not a counterexample" and offered `y² = x³ + 3` as evidence for
the optimistic side. That evidence was misleading, and here is why, plus the witness
that settles it.

*Why `y² = x³ + 3` worked.* `Δ = -16·3⁵`, so `d = 5` and `v(u) = 5/12`: `u = π⁵` with
`π¹² = 3`. Its cubic `f = X³ + 3` has the root `r = -3^{1/3} = -π⁴`, which lies in
`ℚ(3^{1/12})` **because `f` is Eisenstein for `3` in the Kummer direction**. With
`s = t = 0` one gets `(a₁,a₂,a₃,a₄,a₆) = (0, -√3, 0, 1, 0)` and `Δ' = -16`, reducing to
`y² = x³ + x` over `𝔽₃`. So that curve is an instance of the recipe below, not evidence
about the base.

*The refutation: `E : y² = x³ + 4`* (`v₃(j) ≥ 0` vacuously, `j = 0`). `Δ = -6912`,
`v₃ = 3`, so `d = 3` and `v(u) = 1/4`. By (iii), `v(r³ + 4) ≥ 3/2`. The roots of
`X³ + 4` are `-4^{1/3}ζ₃ⁱ`, pairwise at distance `v(ρᵢ - ρⱼ) = v(ζ₃ - 1) = 1/2`, so
`v(r³+4) = Σᵢ v(r - ρᵢ) ≥ 3/2` forces `v(r - ρ) ≥ 1/2` for some root `ρ`. Now work over
`L̃ = ℚ̆₃(3^{1/12})`, which is the largest thing the tame base can give (residue degree
`1` only makes it smaller): `√-1 ∈ ℚ̆₃` and `√3 ∈ L̃`, so `ζ₃ ∈ L̃`, and dividing by a
power of `ζ₃` we may take `ρ = -4^{1/3}`. Put `4^{1/3} = 1 + y₀`; then
`y₀³ + 3y₀² + 3y₀ - 3 = 0` is EISENSTEIN, so `v(y₀) = 1/3`, and writing
`y₀ = 3^{1/3}(1 + δ)` the equation becomes `δ³ + 3δ² + 3δ + 3^{2/3}(1 + δ)² +
3^{1/3}(1 + δ) = 0`, whose Newton polygon has the unique break `v(δ) = 1/9`. Hence

    v(y₀ - 3^{1/3}) = 1/3 + 1/9 = 4/9.

If some `y ∈ L̃` had `v(y - y₀) ≥ 1/2 > 4/9`, then `v(y - 3^{1/3}) = 4/9`; but
`y - 3^{1/3} ∈ L̃` and `v(L̃ˣ) = (1/12)ℤ ∌ 4/9`. Contradiction. So **`y² = x³ + 4`
acquires good reduction over no subfield of `ℚ̆₃(3^{1/12})`**, and a fortiori over no
completion of `ℚ(3^{1/12})`. Cross-check with PARI: `elllocalred` gives conductor
exponent `3` and Kodaira type `II` at `3`, i.e. wild part `δ = 1`, consistent with
semistability defect `e = 12`; the minimal base is `ℚ̆₃(4^{1/3}, 3^{1/4})`, and
`ℚ₃(4^{1/3})` has different exponent `3` against `5` for `ℚ₃(3^{1/3})`, so the two wild
cubics are not isomorphic. **Do not attempt this leaf over `TameBaseAux`.**

**THE RECIPE THAT DOES WORK, AND WHERE IT STOPS.** Take `r` to be a ROOT of `f`, i.e. an
`x`-coordinate of a `2`-torsion point. Then:

* (iii) is free, `f(r) = 0`;
* (ii) holds for a suitable root, by max ≥ average: for a monic cubic
  `Πᵢ f'(rᵢ) = -disc f = 4A³ + 27B² = -Δ/16`, so `Σᵢ v(f'(rᵢ)) = d` and some root has
  `v(f'(r)) ≥ d/3`.

So the base to aim at is `ℚ(E[2], Δ^{1/12})` — the `2`-division field of the short model
together with a twelfth root of the discriminant — NOT a Kummer extension of `ℚ`. (For
`y² = x³ + 4` that is `ℚ(4^{1/3}, 3^{1/4})`, in which `3` is totally ramified of degree
`12` with residue degree `1`, exactly as required.)

**THE ONE REMAINING GAP: residue degree `1`.** The recipe above produces `u` and `r`,
but `ℚ(r)` can have every prime above `3` of residue degree `> 1` — `f mod 3` is
`X³ + ĀX + B̄`, which for `Ā = -1` is an Artin–Schreier polynomial and irreducible over
`𝔽₃`. Dropping the unramified layer is a genuine theorem, and it is the whole of what
is left: if `E/ℚ₃` has good reduction over `L` then `I_L ⊆ N := ker(I → Aut T_ℓE)`, and
`G/N` is an extension of `Ẑ` by the finite `Φ = I/N`; a procyclic group surjecting onto
`Ẑ` with finite kernel IS `Ẑ`, so the closure of a Frobenius lift is a complement, its
preimage `H` has `H ∩ I = N` and index `|Φ| = e`, and the fixed field of `H` is TOTALLY
RAMIFIED of degree `e` with good reduction. Formalising that needs local Galois theory
we do not have; a purely Weierstrass-level substitute would be worth much more.

**BEWARE: THE ROOT RECIPE CANNOT BE MADE INTO A SUB-LEAF AS IT STANDS — that leaf would
be FALSE** (checked 2026-07-28). "There is a residue-degree-`1` base in which `f` SPLITS"
is refuted by `y² = x³ - 9x + 27`: substituting `X = 3Y` turns its cubic into
`27(Y³ - Y + 1)`, and `Y³ - Y + 1` is Artin–Schreier irreducible over `𝔽₃`, so every root
of `f` generates the UNRAMIFIED cubic extension and every prime above `3` in any field
containing them has residue degree divisible by `3`. Yet that curve DOES have a datum:
`d = 6`, `r = 0`, `u = √3` over `ℚ(√3)` satisfies (ii) (`v(A) = 2 ≥ 2`) and (iii)
(`v(B) = 3 ≥ 3`). So the recipe is sufficient but NOT canonical, and any decomposition
must keep `r` a NEAR-root (the two inequalities) rather than an exact one. An argument
that always finds such an `r` over a totally ramified base would close this leaf outright.

**TWO FREE REDUCTIONS, NOW FORMALISED AND ALREADY APPLIED TO THIS STATEMENT**
(2026-07-28; the previous version of this paragraph recorded them as available but not
taken). They are the reason the hypotheses `h4`, `h6` and `hd` appear below, and neither
of them narrows the leaf.

1. *Rational scaling.* `preTranslationDatum_of_scale` (PROVEN above): for `c ∈ ℚˣ` let
   `W_c` be the short curve with `a₄ ↦ c⁴a₄`, `a₆ ↦ c⁶a₆` (so `Δ ↦ c¹²Δ`, `j`
   unchanged). A datum for `W_c` with data `(u', r')` gives `(u'/c, r'/c²)` for `W`, all
   three conditions being homogeneous of matching weight. Taking `c = a₄.den · a₆.den`
   reduces to `a₄, a₆ ∈ ℤ`, which is `h4`/`h6`.
2. *The `d = 0` branch is TAME.* With `a₄, a₆ ∈ ℤ` their `3`-adic valuations are `≥ 0`,
   so `v₃(Δ) ≤ 0` makes both hypotheses of
   `nonempty_preTranslationDatum_of_padicValRat_le` vacuous and `r = 0` over `ℚ(3^{1/12})`
   already works. Since integrality also forces `v₃(Δ) ≥ 0`, that branch is exactly
   `d = 0` — good reduction with no translation at all. Hence `hd : 0 < v₃(Δ)`.

What `hd` buys, and it is exactly the setting a Newton-polygon argument wants: `d > 0`
forces `3 ∣ a₄` for an integral model (else `4a₄³ + 27a₆² ≢ 0 mod 3`), so
`f ≡ (X + a₆)³ mod 3`, every root of `f` is congruent to `-a₆`, and `d ≥ 3` (writing
`a₄ = 3a₁`, `Δ = -16·27(4a₁³ + a₆²)`). **The interesting case always has a triple root
mod `3`.**

**THE CHECK THAT WOULD REFUTE THIS LEAF**: exhibit `E/ℚ` with `0 ≤ v₃(j(E))` acquiring
good reduction over NO finite extension of `ℚ₃` of residue degree `1`. Silverman *AEC*
VII.5.5 gives good reduction over some finite `L/ℚ₃`, and the group-theoretic argument
just quoted removes the unramified layer, so such a witness would have to break that
step. -/
theorem WeierstrassCurve.nonempty_preTranslationDatum_three_of_intCoeff_pos
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {q : ℕ} [Fact q.Prime] (hq3 : q = 3) (hj : 0 ≤ padicValRat q W.j)
    (h4 : ∃ m : ℤ, W.a₄ = (m : ℚ)) (h6 : ∃ n : ℤ, W.a₆ = (n : ℚ))
    (hd : 0 < padicValRat q W.Δ) :
    Nonempty (W.PreTranslationDatum q) :=
  sorry

/-- **The `d = 0` case of the wild leaf is not wild at all** (PROVEN 2026-07-28). With
`a₄, a₆ ∈ ℤ` both `v₃(a₄)` and `v₃(a₆)` are `≥ 0`, so `v₃(Δ) ≤ 0` makes the two
hypotheses of `nonempty_preTranslationDatum_of_padicValRat_le` vacuously true and the
tame base `ℚ(3^{1/12})` with `r = 0` produces the datum. (Integrality also forces
`v₃(Δ) ≥ 0`, so this branch is exactly `d = 0`, i.e. good reduction already.)

Note `hj` and `hq3` are not used in this branch — they are passed straight through to
`nonempty_preTranslationDatum_three_of_intCoeff_pos`, where the arithmetic lives. -/
theorem WeierstrassCurve.nonempty_preTranslationDatum_three_of_intCoeff
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {q : ℕ} [Fact q.Prime] (hq3 : q = 3) (hj : 0 ≤ padicValRat q W.j)
    (h4 : ∃ m : ℤ, W.a₄ = (m : ℚ)) (h6 : ∃ n : ℤ, W.a₆ = (n : ℚ)) :
    Nonempty (W.PreTranslationDatum q) := by
  rcases lt_or_ge 0 (padicValRat q W.Δ) with hd | hd
  · exact WeierstrassCurve.nonempty_preTranslationDatum_three_of_intCoeff_pos
      W hq3 hj h4 h6 hd
  · refine WeierstrassCurve.nonempty_preTranslationDatum_of_padicValRat_le
      W (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨m, hm⟩ := h4
      have hnn : (0 : ℤ) ≤ padicValRat q W.a₄ := by
        rw [hm, padicValRat.of_int]; exact Int.natCast_nonneg _
      omega
    · obtain ⟨n, hn⟩ := h6
      have hnn : (0 : ℤ) ≤ padicValRat q W.a₆ := by
        rw [hn, padicValRat.of_int]; exact Int.natCast_nonneg _
      omega

/-- **The wild case, reduced to INTEGRAL coefficients** (PROVEN 2026-07-28 modulo
`nonempty_preTranslationDatum_three_of_intCoeff_pos`). Scale by `c = a₄.den · a₆.den`:
`W' = (0, 0, 0, c⁴a₄, c⁶a₆)` has integral coefficients, `Δ' = c¹²Δ`, `c₄' = c⁴c₄` and
hence `j' = j`, so the hypothesis `0 ≤ v₃(j)` transports verbatim; and
`preTranslationDatum_of_scale` carries the resulting datum back to `W`. -/
theorem WeierstrassCurve.nonempty_preTranslationDatum_three
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {q : ℕ} [Fact q.Prime] (hq3 : q = 3) (hj : 0 ≤ padicValRat q W.j) :
    Nonempty (W.PreTranslationDatum q) := by
  classical
  have hd4 : ((W.a₄.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr W.a₄.den_nz
  have hd6 : ((W.a₆.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr W.a₆.den_nz
  set c : ℚ := (W.a₄.den : ℚ) * (W.a₆.den : ℚ) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero hd4 hd6
  set W' : WeierstrassCurve ℚ := ⟨0, 0, 0, c ^ 4 * W.a₄, c ^ 6 * W.a₆⟩ with hW'def
  have h4' : W'.a₄ = c ^ 4 * W.a₄ := rfl
  have h6' : W'.a₆ = c ^ 6 * W.a₆ := rfl
  haveI hshort : W'.IsShortNF := ⟨rfl, rfl, rfl⟩
  have hΔ' : W'.Δ = c ^ 12 * W.Δ := by
    rw [WeierstrassCurve.Δ_of_isShortNF, WeierstrassCurve.Δ_of_isShortNF, h4', h6']
    ring
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  haveI hell : W'.IsElliptic := by
    refine ⟨?_⟩
    rw [hΔ']
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hc0) hΔ0)
  have hc4' : W'.c₄ = c ^ 4 * W.c₄ := by
    rw [WeierstrassCurve.c₄_of_isShortNF, WeierstrassCurve.c₄_of_isShortNF, h4']; ring
  have hjW : W.j = W.Δ⁻¹ * W.c₄ ^ 3 := by
    simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  have hjW' : W'.j = W'.Δ⁻¹ * W'.c₄ ^ 3 := by
    simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  have hjeq : W'.j = W.j := by
    rw [hjW', hjW, hΔ', hc4']
    field_simp
  have hint4 : ∃ m : ℤ, W'.a₄ = (m : ℚ) := by
    refine ⟨W.a₄.num * (W.a₄.den : ℤ) ^ 3 * (W.a₆.den : ℤ) ^ 4, ?_⟩
    have hnum : W.a₄ * (W.a₄.den : ℚ) = (W.a₄.num : ℚ) := Rat.mul_den_eq_num _
    rw [h4', hcdef]
    push_cast
    rw [← hnum]
    ring
  have hint6 : ∃ n : ℤ, W'.a₆ = (n : ℚ) := by
    refine ⟨W.a₆.num * (W.a₄.den : ℤ) ^ 6 * (W.a₆.den : ℤ) ^ 5, ?_⟩
    have hnum : W.a₆ * (W.a₆.den : ℚ) = (W.a₆.num : ℚ) := Rat.mul_den_eq_num _
    rw [h6', hcdef]
    push_cast
    rw [← hnum]
    ring
  obtain ⟨D⟩ := WeierstrassCurve.nonempty_preTranslationDatum_three_of_intCoeff W' hq3
    (by rw [hjeq]; exact hj) hint4 hint6
  exact WeierstrassCurve.preTranslationDatum_of_scale W W' hc0 h4' h6' hΔ' D

/-- **The wild-case datum, assembled** (PROVEN 2026-07-28, modulo
`nonempty_preTranslationDatum_three_of_intCoeff_pos`). All the arithmetic now sits in that
leaf; this step is `translationDatum_of_pre`, i.e. the derivation of `ha₂` and `hΔ` from
`ha₄` and `0 ≤ v₃(j)`. See the leaf's docstring for the refutation of the tame base, the
root recipe, and the residue-degree-`1` gap. -/
theorem WeierstrassCurve.nonempty_translationDatum_three
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {q : ℕ} [Fact q.Prime] (hq3 : q = 3) (hj : 0 ≤ padicValRat q W.j) :
    Nonempty (W.TranslationDatum q) := by
  obtain ⟨D⟩ := WeierstrassCurve.nonempty_preTranslationDatum_three W hq3 hj
  exact WeierstrassCurve.translationDatum_of_pre W hq3 hj D

/-- **The WILD half of the arithmetic leaf: `q = 3`** (**PROVEN 2026-07-27** modulo
`nonempty_translationDatum_three`, which carries all the remaining arithmetic; opened
2026-07-27 when the `5 ≤ q` half above was PROVEN). This is the genuinely missing part of
`exists_potentiallyGoodModel_of_jIntegral`, and the consumers of this file need it —
they take `q ∈ {3, 5}`, so it cannot be dodged by assuming `5 ≤ q`.

**WHY THE TAME ROUTE DOES NOT EXTEND, in three independent ways.** Each is a concrete
obstruction rather than a difficulty of degree, and each has to be dealt with:

1. *The valuation inequality is FALSE at `3`.* `padicValRat_Δ_le_of_jIntegral` proves
   `3a ≥ d` and `2b ≥ d` from `v_q(j) ≥ 0` using `v_q(27) = v_q(6912) = 0`, which needs
   `q ≥ 5`. At `q = 3`, `j = 6912·A³/(4A³ + 27B²)` gives `v₃(j) = 3 + 3a − d`, so
   `j`-integrality only says `3a ≥ d − 3`. **Explicit witness that the conclusion itself
   fails**: `y² = x³ + 3` has `A = 0`, `B = 3`, `Δ = −16·27·9`, so `d = v₃(Δ) = 5` while
   `2b = 2`; the scaled `a₆` would have valuation `−6d + 12b = −18 < 0`.
2. *Short Weierstrass form cannot reduce to a good curve of nonzero `j`.* Over `𝔽₃` a
   curve with `a₁ = a₂ = a₃ = 0` has `c₄ = −48A ≡ 0`, hence `j = c₄³/Δ = 0`. So for any
   `E/ℚ` with `j ≢ 0 (mod 3)` the good model must have `a₁` or `a₂` nonzero, i.e. the
   `r, s, t` part of the variable change is genuinely needed — unlike the tame case,
   where `u` alone suffices. (The `u`-only scaling is not merely suboptimal here; it
   cannot produce the answer.)
3. *`ℚ(3^{1/12})` is NOT a large enough base* — **SETTLED 2026-07-27, in the negative.**
   At `q = 3` the semistability defect can be `3`, `6` or `12`, all divisible by `p = 3`,
   so the extension is WILDLY ramified, and the wild cubic it needs is generally not the
   one inside `X¹² − 3`. The explicit witness is `y² = x³ + 4`, whose good models require
   `ℚ̆₃(4^{1/3}, 3^{1/4})`; the full computation, including why the old optimistic
   witness `y² = x³ + 3` was an instance of the recipe rather than evidence about the
   base, is in the docstring of `nonempty_translationDatum_three` above.

**THE PROOF BELOW** is now only the reduction to short normal form, exactly as in the
`5 ≤ q` half: `E.toShortNF` puts `E` in short form (`Invertible 2` and `Invertible 3`
are free over `ℚ`), `variableChange_j` carries `j`-integrality across, and the two
variable changes compose by `mul_smul` and `map_variableChange`. All the arithmetic sits
in `nonempty_translationDatum_three`, and all the reduction theory in
`exists_potentiallyGoodModel_of_translationDatum`.

**WHAT IS ALREADY BUILT AND MUST NOT BE REBUILT.** The entire non-arithmetic half of
this leaf is proven above and is uniform in `q`:
`exists_potentiallyGoodModel_of_integral` turns *(number field, DVR, residue
equivalence, variable change, five integrality memberships, invertible `Δ`)* into the
`PotentiallyGoodModel` datum; `hasGoodReduction_of_isUnit_Δ` and
`isMinimal_of_valuation_Δ_eq_one` discharge mathlib's `IsMinimal`/`HasGoodReduction`
bookkeeping; `residueFieldEquivZModOfLocalHom` upgrades any local hom onto `ZMod 3` to
the required `resEquiv`; and `TameBaseAux.instIsDiscreteValuationRingTameSubring` shows
how to get a DVR out of a valuation subring whose value group is `ℤ` (the pattern
generalises: `exists_valuation_eq_zpow` is the only step that mentions the specific
base). So a prover here owes exactly ONE thing, and it is now stated as its own leaf: a
base with residue degree `1` at `3` together with the two elements `u`, `r` of a
`TranslationDatum`. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq3 : q = 3)
    (hj : 0 ≤ padicValRat q E.j) : Nonempty (E.PotentiallyGoodModel q) := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  have hj' : 0 ≤ padicValRat q (E.toShortNF • E).j := by rwa [variableChange_j]
  obtain ⟨D⟩ := WeierstrassCurve.nonempty_translationDatum_three
    (E.toShortNF • E) hq3 hj'
  obtain ⟨N⟩ := WeierstrassCurve.exists_potentiallyGoodModel_of_translationDatum
    (E.toShortNF • E) D
  exact ⟨{
    K := N.K
    R := N.R
    resEquiv := N.resEquiv
    V := N.V
    C := N.C * (E.toShortNF.map (algebraMap ℚ N.K))
    V_eq := by
      have hmv : (E.toShortNF.map (algebraMap ℚ N.K)) • (E.baseChange N.K)
          = (E.toShortNF • E).baseChange N.K := map_variableChange _ _ _
      rw [N.V_eq, mul_smul, hmv] }⟩

/-! ### The wild case `q = 2`: the FULL variable change is not optional

`TranslationDatum` above fixes `s = t = 0`, and its docstring proves that this loses
nothing **at `q = 3`** — the completing-the-square change `(1, 0, -a₁/2, -a₃/2)` is
integral there because `2` is a unit of the residue characteristic `3`. At `q = 2` that
step is exactly what fails, and the failure is not technical: **`TranslationDatum W 2` is
EMPTY for every `W`.**

For a Weierstrass equation with `a₁ = a₃ = 0` one has `b₂ = 4a₂`, `b₄ = 2a₄`, `b₆ = 4a₆`,
`b₈ = 4a₂a₆ − a₄²`, hence

    Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆
      = −64a₂³a₆ + 16a₂²a₄² − 64a₄³ − 432a₆² + 288a₂a₄a₆,

every coefficient of which is divisible by `16`. So `16 ∣ Δ` whenever the `aᵢ` are
integral, and `Δ` is never a unit at a place above `2`. (Conceptually: in residue
characteristic `2` the equation `y² = cubic` is inseparable in `y`, so its reduction is
singular at the point where the cubic's derivative vanishes.) A good model at `2`
therefore has `a₁ ≠ 0` or `a₃ ≠ 0`, i.e. **both `s` and `t` are genuinely needed**, and
the datum below carries all four components of the variable change.

Everything else is unchanged, and in particular
`exists_potentiallyGoodModel_of_fullTranslationDatum` below is uniform in `q` — nothing
in it mentions `2`. -/

/-- **The obligation the wild case `q = 2` owes, with every trace of reduction theory
removed** (interface opened 2026-07-28 while extending
`exists_potentiallyGoodModel_of_jIntegral` to `q = 2`). A `FullTranslationDatum W q` is: a
number field `L`, a DVR valuation subring `A ⊆ L` with residue field `ZMod q`, and **four
field elements** `u ∈ Lˣ`, `r, s, t ∈ L` such that the curve `y² = x³ + a₄x + a₆` becomes
integral with invertible discriminant after the variable change `(u, r, s, t)`. Nothing
else: no `IsMinimal`, no `HasGoodReduction`, no `IsIntegral`, no residue-field
bookkeeping. Those all live in
`exists_potentiallyGoodModel_of_fullTranslationDatum` below, which is PROVEN and is
uniform in `q`.

The five membership conditions are literally the transformed coefficients of a curve in
short normal form (`a₁ = a₂ = a₃ = 0`), read off mathlib's `variableChange_aᵢ`:

    a₁' = u⁻¹·(2s),                     a₂' = u⁻²·(3r − s²),
    a₃' = u⁻³·(2t),                     a₄' = u⁻⁴·(a₄ + 3r² − 2st),
    a₆' = u⁻⁶·(a₆ + r·a₄ + r³ − t²),

and `hΔ` is `(Δ')⁻¹ ∈ A` for `Δ' = u⁻¹²·Δ`.

**RELATION TO `TranslationDatum`.** Setting `s = t = 0` recovers it exactly, so this
structure is weaker as a hypothesis and stronger as a conclusion — a `TranslationDatum`
yields a `FullTranslationDatum` for the same `W` and `q`. The converse fails at `q = 2`
by the computation in the section header above, and holds at every odd `q` by the
completing-the-square argument in `TranslationDatum`'s docstring. Nothing here is
specific to `2`.

**NOT VACUOUS, and it is exactly as non-vacuous as `PotentiallyGoodModel`.** One
direction is the theorem below. For the converse, a `PotentiallyGoodModel` of a `W` in
short normal form comes with an integral `V = C • W_L` with unit `Δ`, and reading off the
four components of that `C` gives back the five memberships verbatim — there is no
normalisation step to lose, precisely because `s` and `t` are no longer being forced to
`0`. So `Nonempty (W.FullTranslationDatum q)` and `Nonempty (W.PotentiallyGoodModel q)`
are EQUIVALENT for `W` in short normal form: the structure is a faithful repackaging. -/
structure WeierstrassCurve.FullTranslationDatum (W : WeierstrassCurve ℚ)
    (q : ℕ) [Fact q.Prime] where
  /-- The number field over which `W` acquires good reduction. -/
  L : Type
  [instField : Field L]
  [instDec : DecidableEq L]
  [instAlgebra : Algebra ℚ L]
  [instFin : FiniteDimensional ℚ L]
  /-- The local ring at the chosen prime of `L` above `q`. -/
  A : ValuationSubring L
  [instDVR : IsDiscreteValuationRing A]
  /-- **Residue degree one**, exactly as in `PotentiallyGoodModel`. -/
  resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q
  /-- The scaling. `hΔ` forces `v(u) = v(Δ)/12`. -/
  u : Lˣ
  /-- The translation `x ↦ x + r`. -/
  r : L
  /-- The shear `y ↦ y + sx`. It is what `TranslationDatum` sets to `0` and what a good
  model at `2` cannot do without: in residue characteristic `2` a curve with `a₁ = 0` has
  `Δ ≡ a₃⁴`, so a nonsingular reduction needs `a₁' ≠ 0` or `a₃' ≠ 0`. -/
  s : L
  /-- The translation `y ↦ y + t`. -/
  t : L
  /-- `a₁'` is integral. -/
  ha₁ : ((u⁻¹ : Lˣ) : L) * (2 * s) ∈ A
  /-- `a₂'` is integral. -/
  ha₂ : ((u⁻¹ : Lˣ) : L) ^ 2 * (3 * r - s ^ 2) ∈ A
  /-- `a₃'` is integral. -/
  ha₃ : ((u⁻¹ : Lˣ) : L) ^ 3 * (2 * t) ∈ A
  /-- `a₄'` is integral. -/
  ha₄ : ((u⁻¹ : Lˣ) : L) ^ 4 *
    (algebraMap ℚ L W.a₄ + 3 * r ^ 2 - 2 * s * t) ∈ A
  /-- `a₆'` is integral. -/
  ha₆ : ((u⁻¹ : Lˣ) : L) ^ 6 *
    (algebraMap ℚ L W.a₆ + r * algebraMap ℚ L W.a₄ + r ^ 3 - t ^ 2) ∈ A
  /-- `Δ'` is a unit. -/
  hΔ : ((u : L)) ^ 12 * (algebraMap ℚ L W.Δ)⁻¹ ∈ A

attribute [instance] WeierstrassCurve.FullTranslationDatum.instField
  WeierstrassCurve.FullTranslationDatum.instDec
  WeierstrassCurve.FullTranslationDatum.instAlgebra
  WeierstrassCurve.FullTranslationDatum.instFin
  WeierstrassCurve.FullTranslationDatum.instDVR

/-- **A full translation datum produces the good model** (PROVEN 2026-07-28). This is the
`q`-uniform half of the wild case at `2`, and it is pure bookkeeping over
`exists_potentiallyGoodModel_of_integral`: the variable change is `(u, r, s, t)`, the
`a₁`, `a₂`, `a₃` obligations are the structure's own fields once `IsShortNF` has killed
`W`'s `a₁, a₂, a₃`, and so are the other three.

Nothing here is specific to `q = 2`; the statement is uniform in `q`, and it subsumes
`exists_potentiallyGoodModel_of_translationDatum` (take `s = t = 0`). What is specific to
`q = 2` is that the datum is HARD TO BUILD — see `nonempty_fullTranslationDatum_two`. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_fullTranslationDatum
    {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    (D : W.FullTranslationDatum q) : Nonempty (W.PotentiallyGoodModel q) := by
  classical
  set C : VariableChange D.L := ⟨D.u, D.r, D.s, D.t⟩ with hC
  have hb₁ : (W.baseChange D.L).a₁ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₂ : (W.baseChange D.L).a₂ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₃ : (W.baseChange D.L).a₃ = 0 := by simp [WeierstrassCurve.baseChange]
  have hb₄ : (W.baseChange D.L).a₄ = algebraMap ℚ D.L W.a₄ := rfl
  have hb₆ : (W.baseChange D.L).a₆ = algebraMap ℚ D.L W.a₆ := rfl
  have hbΔ : (W.baseChange D.L).Δ = algebraMap ℚ D.L W.Δ := by
    simp [WeierstrassCurve.baseChange, map_Δ]
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_integral W D.L D.A D.resEquiv C
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [variableChange_a₁, hC, hb₁]
    simpa using D.ha₁
  · rw [variableChange_a₂, hC, hb₁, hb₂]
    simpa using D.ha₂
  · rw [variableChange_a₃, hC, hb₁, hb₃]
    simpa using D.ha₃
  · rw [variableChange_a₄, hC, hb₁, hb₂, hb₃, hb₄]
    simpa using D.ha₄
  · rw [variableChange_a₆, hC, hb₁, hb₂, hb₃, hb₄, hb₆]
    simpa using D.ha₆
  · rw [variableChange_Δ, hC, hbΔ]
    simpa [mul_comm] using D.hΔ

/-- **THE ARITHMETIC OF THE WILD CASE `q = 2`** (sorry leaf, opened 2026-07-28 while
extending `exists_potentiallyGoodModel_of_jIntegral` to `q = 2`). What is owed is a base
`L` with a residue-degree-`1` DVR at `2`, plus **four elements** `u, r, s, t` of `L`
making the five transformed coefficients integral and `Δ'` a unit. Write `A = W.a₄`,
`B = W.a₆`, `d = v₂(Δ)`; `hΔ` pins `v(u) = d/12`.

**WHY THIS CASE EXISTS AT ALL.** The producer was stated with `hq2 : q ≠ 2` from the day
it was written, on the grounds that its tame Kummer base `ℚ_q(π^{1/e})` "does not reach
the wild prime `2`". That is a statement about the ROUTE, not about the theorem: the
conclusion is true at `2` for the same reason as everywhere else (Silverman *AEC* VII.5.5
plus the removal of the unramified layer), and the `q ≠ 2` hypothesis was propagating
into consumers as a real restriction — notably it is what forced
`map_pow_twentyFour_eq_self_of_padicValRat_j_nonneg` to be split into a `q ≠ 2` half and
a separate `q = 2` leaf. With this leaf in place the producer is uniform in `q` and that
split is unnecessary.

**THE TAME BASE IS TOO SMALL AT `2`, AND HERE THE OBSTRUCTION IS EXACT.** If `E/ℚ₂`
acquires good reduction over a finite `L/ℚ₂` then `I_L ⊆ N := ker(I → Aut T_ℓE)`
(Néron–Ogg–Shafarevich), so with `Φ := I/N` the semistability defect,

    |Φ| = [I : N]  divides  [I : I_L] = e(L/ℚ₂).

At `p = 2` Kraus's classification gives `e ∈ {1, 2, 3, 4, 6, 8, 24}`, and `ℚ₂(2^{1/12})`
has `e = 12`. So **every curve with `e ∈ {8, 24}` is out of reach of the tame base**,
since neither `8` nor `24` divides `12`. Concrete witness, found with PARI and stated
here as reconnaissance rather than as a Lean fact: `E : y² = x³ − 2x` has `j = 1728` with
`v₂(j) = 6 ≥ 0`, and `elllocalred(E, 2)` returns Kodaira type `III` with conductor
exponent `8` — the maximum possible at `2` — i.e. wild part `δ = 6`, which is Kraus's
`e = 24` case. So, exactly as at `q = 3`, **do not attempt this leaf over
`TameBaseAux`**; the base has to be built out of the curve.

Two further curves worth knowing, both with `v₂(j) ≥ 0` and `j ∉ {0, 1728}`, so that the
difficulty is not confined to the CM values: `y² = x³ + x + 1` has `j = 6912/31`,
`v₂(j) = 8`, Kodaira `II`, conductor exponent `4` at `2` (wild, `δ = 2`); and
`y² = x³ − x + 1` has `j = −6912/23`, `v₂(j) = 8`, Kodaira `IV`, conductor exponent `2`
(tame).

**WHAT IS FORCED, AND IT IS THE ORDINARY/SUPERSINGULAR DICHOTOMY.** Since `hΔ` makes `Δ'`
a unit, the reduction is nonsingular; in residue characteristic `2` a Weierstrass
equation has

    Δ ≡ a₁⁶a₆ + a₁⁵a₃a₄ + a₁⁴a₂a₃² + a₁⁴a₄² + a₁³a₃³ + a₃⁴   (mod 2),

which for `a₁ = 0` is `a₃⁴`. So `v(a₁') = 0` or `v(a₃') = 0`, i.e.

    v(s) = v(u) − v(2)      (ordinary reduction)   or
    v(t) = 3v(u) − v(2)     (supersingular reduction).

Neither `s` nor `t` is free, and a prover should expect to split on this dichotomy rather
than to find a single uniform formula. Note `v(2) = e(L/ℚ₂) > 0` here, which is exactly
why the `ha₁`/`ha₃` conditions are satisfiable at all.

**A REDUCTION THAT IS AVAILABLE AND COSTS NOTHING** (the same one recorded on
`nonempty_preTranslationDatum_three`, and it applies verbatim here). The statement is
invariant under rational scaling: for `c ∈ ℚˣ` let `W_c` be the short curve with
`a₄ ↦ c⁴a₄`, `a₆ ↦ c⁶a₆` (so `Δ ↦ c¹²Δ`, `j` unchanged); given a `FullTranslationDatum`
for `W_c` with data `(u', r', s', t')`, the tuple `(u'/c, r'/c², s'/c, t'/c³)` is one for
`W`, since each of the six conditions is homogeneous of the matching weight. Taking
`c = a₄.den · a₆.den` reduces to `a₄, a₆ ∈ ℤ`, where Newton-polygon arguments are
available.

**THE ONE REMAINING GAP IS THE SAME AS AT `q = 3`: residue degree `1`.** Producing SOME
finite `L/ℚ₂` with good reduction is Silverman *AEC* VII.5.5; producing one with residue
degree `1` is the removal of the unramified layer, and the argument is group-theoretic:
`G/N` is an extension of `Ẑ` by the finite `Φ`, the closure of a Frobenius lift is a
procyclic group surjecting onto `Ẑ` with finite kernel — hence `≅ Ẑ`, since a proper
procyclic quotient of `Ẑ` cannot surject onto `Ẑ` — so it is a complement, its preimage
`H` has `H ∩ I = N` and index `e`, and the fixed field of `H` is TOTALLY RAMIFIED of
degree `e` with good reduction. Formalising that needs local Galois theory this project
does not have.

**THE DECOMPOSITION THAT WOULD PAY FOR ITSELF, and it is uniform in `q`.** Split
`PotentiallyGoodModel` into (i) the same structure WITHOUT `resEquiv`, asking only that
the residue field have characteristic `q`, and (ii) the passage from (i) to residue
degree `1`. Then (i) is Silverman VII.5.5 + a Krasner descent and (ii) is the paragraph
above, both uniform in `q` — and `q = 2`, `q = 3` and `5 ≤ q` all become corollaries of
one pair of leaves instead of three separate per-prime arguments. That cut is NOT made
here only because `exists_potentiallyGoodModel_of_jIntegral_three` has a live owner and
restructuring it under them would cost a merge conflict for no mathematical gain.

**THE CHECK THAT WOULD REFUTE THIS LEAF**: exhibit `E/ℚ` with `0 ≤ v₂(j(E))` acquiring
good reduction over NO finite extension of `ℚ₂` of residue degree `1`. Silverman *AEC*
VII.5.5 gives good reduction over some finite `L/ℚ₂`, and the group-theoretic argument
just quoted removes the unramified layer, so such a witness would have to break that
step. References for the wild arithmetic at `2`: Serre, *Propriétés galoisiennes des
points d'ordre fini des courbes elliptiques*, Invent. Math. 15 (1972), §5.6; Kraus, *Sur
le défaut de semi-stabilité des courbes elliptiques à réduction additive*, Manuscripta
Math. 69 (1990). -/
theorem WeierstrassCurve.nonempty_fullTranslationDatum_two
    (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    {q : ℕ} [Fact q.Prime] (hq2 : q = 2) (hj : 0 ≤ padicValRat q W.j) :
    Nonempty (W.FullTranslationDatum q) :=
  sorry

/-- **The WILD half of the arithmetic leaf at the wild prime: `q = 2`** (PROVEN
2026-07-28 modulo `nonempty_fullTranslationDatum_two`, which carries all the remaining
arithmetic). The proof is only the reduction to short normal form, exactly as in the
`q = 3` and `5 ≤ q` halves: `E.toShortNF` puts `E` in short form (`Invertible 2` and
`Invertible 3` are free over `ℚ`, the residue characteristic being irrelevant to what
happens over `ℚ` itself), `variableChange_j` carries `j`-integrality across, and the two
variable changes compose by `mul_smul` and `map_variableChange`.

**WHAT IS ALREADY BUILT AND MUST NOT BE REBUILT**, all of it uniform in `q`:
`exists_potentiallyGoodModel_of_integral` turns *(number field, DVR, residue equivalence,
variable change, five integrality memberships, invertible `Δ`)* into the
`PotentiallyGoodModel` datum; `hasGoodReduction_of_isUnit_Δ` and
`isMinimal_of_valuation_Δ_eq_one` discharge mathlib's `IsMinimal`/`HasGoodReduction`
bookkeeping; `residueFieldEquivZModOfLocalHom` upgrades any local hom onto `ZMod q` to
the required `resEquiv`; and `TranslationAux.algebraMap_mem_of_not_dvd_den` is the bridge
from `0 ≤ padicValRat q x` to membership of `A`. A prover here owes exactly ONE thing,
and it is stated as its own leaf above. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq2 : q = 2)
    (hj : 0 ≤ padicValRat q E.j) : Nonempty (E.PotentiallyGoodModel q) := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  have hj' : 0 ≤ padicValRat q (E.toShortNF • E).j := by rwa [variableChange_j]
  obtain ⟨D⟩ := WeierstrassCurve.nonempty_fullTranslationDatum_two
    (E.toShortNF • E) hq2 hj'
  obtain ⟨N⟩ := WeierstrassCurve.exists_potentiallyGoodModel_of_fullTranslationDatum
    (E.toShortNF • E) D
  exact ⟨{
    K := N.K
    R := N.R
    resEquiv := N.resEquiv
    V := N.V
    C := N.C * (E.toShortNF.map (algebraMap ℚ N.K))
    V_eq := by
      have hmv : (E.toShortNF.map (algebraMap ℚ N.K)) • (E.baseChange N.K)
          = (E.toShortNF • E).baseChange N.K := map_variableChange _ _ _
      rw [N.V_eq, mul_smul, hmv] }⟩

/-- **The ARITHMETIC half: integral `j`-invariant produces a good model over a
number field with residue degree one at `q`** (opened 2026-07-27 by
decomposing `exists_frobeniusAut_of_potentiallyGoodReduction` below;
**DECOMPOSED 2026-07-27** into its tame and wild halves; **EXTENDED TO `q = 2`
on 2026-07-28**, so the statement is now uniform in `q` and carries no
`hq2 : q ≠ 2`). Of the three halves,
`exists_potentiallyGoodModel_of_jIntegral_five_le` is PROVEN,
`exists_potentiallyGoodModel_of_jIntegral_three` is PROVEN modulo the single
remaining leaf `nonempty_translationDatum_three`, and
`exists_potentiallyGoodModel_of_jIntegral_two` is PROVEN modulo
`nonempty_fullTranslationDatum_two`. No
Galois theory appears here; the whole content is reduction theory of Weierstrass
equations.

THE PROOF BELOW is only the case split: a prime is `2`, or `3`, or `≥ 5`
(`4` is not prime), and the three halves are separately owned. `5 ≤ q` is PROVEN
over `EllipticCurve/TorsionReduction.lean`'s base `ℚ(q^{1/12})`, upgraded to a
DVR here; `q = 3` and `q = 2` are wildly ramified and are where all the
remaining difficulty sits — read those leaves' docstrings, which record why the
tame route does not extend and list the machinery already built for them.

**WHY `hq2 : q ≠ 2` IS GONE, and what it was doing.** It was never a
mathematical restriction — it recorded that the TAME route reaches only odd
primes. Consumers were inheriting it and paying for it: it is why
`map_pow_twentyFour_eq_self_of_padicValRat_j_nonneg` had to be cut into a
`q ≠ 2` half and a separate `q = 2` leaf. Removing it here removes the reason
for that split. It does NOT remove `hq2` from
`exists_frobeniusAut_of_potentiallyGoodReduction`, whose GALOIS half
(`exists_frobeniusAut_of_potentiallyGoodModel`) has its own, independent, use
of `q ≠ 2` — that one is about the separability of the `2`-division polynomial
mod `q` and lives on `PotentiallyGoodModel.exists_isTorsionReduction`.

THE INFORMAL PROOF, kept for the wild halves. Locally, `0 ≤ v_q(j(E))` is
equivalent to potential good reduction (Silverman *AEC* VII.5.5), so `E/ℚ_q`
acquires good reduction over some finite `L/ℚ_q`. Three further steps produce
the datum:

1. *Drop the unramified layer.* For `L'/L` unramified, `I_{L'} = I_L`, so by the
   criterion of Néron–Ogg–Shafarevich good reduction over `L'` already gives
   good reduction over `L`. Equivalently and more concretely: an unramified
   twist of a curve with good reduction has good reduction, because its
   discriminant is again a unit. This is what makes residue degree `1`
   available at all, and it is why `resEquiv` is not an extra assumption but a
   normalisation.
2. *Keep the singular point rational.* The singular point of an additive
   reduction is unique, hence fixed by the residue Galois group, hence residue
   rational — so the `r, s, t` part of the variable change costs no extension
   and only the `u` part can.
3. *Descend to a number field.* `K` is obtained from `L` by Krasner:
   a number field dense enough at `q` has completion `L`, and good reduction is
   a condition on the completion.

THE OBLIGATION THAT IS NOT UNIFORM IN `q`, STATED HONESTLY. Step 1 is the
standard statement for `q ≥ 5`, where the twisting is by `u` with
`v(u) = d/12` and `L` is the TAME Kummer extension `ℚ_q(π^{1/e})`,
`e ∈ {1, 2, 3, 4, 6}` (Silverman *ATAEC* IV.10; Kraus, Manuscripta Math. 69
(1990)). At `q = 3` the semistability defect can be `12` and `L/ℚ_q` is WILDLY
ramified. `q = 3` IS used by the consumers of this file (they take
`q ∈ {3, 5}`), so this cannot be dodged by assuming `5 ≤ q`; the wild case is
the genuinely missing ingredient and the tame case is textbook.

RELATED OPEN LEAF, DO NOT DUPLICATE: `exists_tameGoodModel_of_jIntegral`
(`EllipticCurve/TorsionReduction.lean`) is the same arithmetic in the
`TameGoodModel` vocabulary, restricted to `5 ≤ ℓ`. See
`PotentiallyGoodModel`'s docstring for the comparison.

THE CHECK THAT WOULD REFUTE THIS LEAF: exhibit `E/ℚ` and a prime `q` with
`0 ≤ v_q(j(E))` acquiring good reduction over NO finite extension of `ℚ_q` of
residue degree `1`. By step 1 that would require an example where the
unramified layer cannot be dropped, i.e. a curve with good reduction over an
unramified extension of `ℚ_q` but over no totally ramified one — which the
unit-discriminant argument of step 1 rules out for `q` odd. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (hj : 0 ≤ padicValRat q E.j) :
    Nonempty (E.PotentiallyGoodModel q) := by
  rcases eq_or_lt_of_le hq.two_le with h | h
  · exact WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_two E h.symm hj
  · rcases eq_or_lt_of_le (show 3 ≤ q by omega) with h3 | h3
    · exact WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_three E h3.symm hj
    · have hq4 : q ≠ 4 := by rintro rfl; exact absurd hq (by decide)
      exact WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_five_le E (by omega) hj

/-- **The reduction of the good model, transported to `𝔽_q`** (PROVEN
2026-07-27): the reduction of `D.V` over the residue field of `D.R`, carried to
`ZMod q` along `D.resEquiv`.

This is the curve `Wbar₀` that the Galois leaf below produces, and PINNING it
here rather than leaving it existential is what makes the cut of that leaf safe
— see the ATOMICITY AUDIT on
`WeierstrassCurve.PotentiallyGoodModel.exists_torsionFrame` below (it was
written for `exists_reductionFrame_of_potentiallyGoodModel` and moved to that
leaf when the latter was cut into three on 2026-07-27), which exhibits the
falsity that appears as soon as the curve is handed over as a free variable. -/
noncomputable def WeierstrassCurve.PotentiallyGoodModel.redCurve
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime]
    (D : E.PotentiallyGoodModel q) : WeierstrassCurve (ZMod q) :=
  (D.V.reduction D.R).map (D.resEquiv : IsLocalRing.ResidueField D.R →+* ZMod q)

/-- **The reduction curve is elliptic** (PROVEN 2026-07-27): mathlib's
`hasGoodReduction_iff_isElliptic_reduction` says that good reduction is exactly
the statement that the reduction over the residue field has unit discriminant,
and a ring map carries units to units, so the transport along `D.resEquiv` is
elliptic too. This is what discharges the `Wbar₀.IsElliptic` obligation of the
consumer without any further hypothesis. -/
instance WeierstrassCurve.PotentiallyGoodModel.instIsEllipticRedCurve
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime]
    (D : E.PotentiallyGoodModel q) : D.redCurve.IsElliptic := by
  have h : (D.V.reduction D.R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction D.R).mp D.V_good
  refine ⟨?_⟩
  rw [WeierstrassCurve.PotentiallyGoodModel.redCurve, WeierstrassCurve.map_Δ]
  exact h.isUnit.map _

/-- **The valuation subring of `ℚ̄` above `q` pinned by the fixed embedding
`ℚ̄ ↪ ℚ̄_q`** (definition, opened 2026-07-27 while cutting
`exists_reductionFrame_of_potentiallyGoodModel` below into three leaves).

`localValuationSubring v`
(`Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`) is the integral
closure of `𝒪_v` inside `ℚ̄_q`, packaged as a valuation subring; and
`Field.absoluteGaloisGroup.map` transports `Γ ℚ_q → Γ ℚ` along the SAME
arbitrary-but-fixed embedding
`AlgebraicClosure.map (algebraMap ℚ ℚ_q) : ℚ̄ →+* ℚ̄_q` — that is exactly the
content of `Field.absoluteGaloisGroup.lift_map`. Pulling the local subring back
along that embedding therefore yields the valuation subring of `ℚ̄` whose
decomposition group inside `Γ ℚ` contains the image of the whole of `Γ ℚ_q`,
hence contains `globalFrob v` and the image of `localInertiaGroup v`.

WHY THIS IS A DEFINITION AND NOT A FIELD OF `LocalFrame` BELOW: the primes of
`ℚ̄` above `q` form a single `Γ ℚ`-orbit and `globalFrob v` lies in the
decomposition group of exactly ONE of them, so a frame carrying an ARBITRARY
valuation subring above `R` would make `exists_frobeniusLift` below FALSE — the
refutation is `g • 𝒪` for any `g` outside the decomposition group, at which
`globalFrob v` does not even act. Only the embedding of `K` is free; the subring
of `ℚ̄` is not. -/
noncomputable def GaloisRepresentation.globalValuationSubring
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ValuationSubring (AlgebraicClosure ℚ) :=
  (localValuationSubring v).comap
    (AlgebraicClosure.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))

/-! ### Transport along the fixed embedding `ℚ̄ ↪ ℚ̄_q`

`globalValuationSubring v` is BY DEFINITION the comap of `localValuationSubring v`
along `AlgebraicClosure.map (algebraMap ℚ ℚ_v)`, and `Field.absoluteGaloisGroup.map`
transports `Γ ℚ_v → Γ ℚ` along the SAME embedding (`Field.absoluteGaloisGroup.lift_map`).
The five declarations below are that observation made usable: the image of `Γ ℚ_v`
lands in the decomposition group of `𝒪`, the image of `localInertiaGroup v` lands in
its inertia subgroup, and residues of `𝒪` are read off residues of `𝒪_loc`.

These were listed as "THE FIRST STEP A PROVER SHOULD TAKE" on
`exists_frobeniusLift` below; they are proven here once so that leaf never has to
mention `𝒪_loc` twice. The friction the note warned about is real and is why the
memberships below are supplied as explicit `⟨_, _⟩` ascriptions rather than by
`rw [MulAction.mem_stabilizer_iff]`: `Field.absoluteGaloisGroup ℚ` and
`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ` are reducibly but not syntactically
equal, so `rw` fails on the membership with an instance mismatch while `show` and
`exact` go through. -/

/-- **Membership in `𝒪` is membership of the image in `𝒪_loc`** (PROVEN
2026-07-28) — definitional, since `globalValuationSubring` is a `comap`. -/
theorem GaloisRepresentation.mem_globalValuationSubring_iff
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (x : AlgebraicClosure ℚ) :
    x ∈ GaloisRepresentation.globalValuationSubring v ↔
      AlgebraicClosure.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) x
        ∈ localValuationSubring v :=
  Iff.rfl

/-- **The structural ring map `𝒪 →+* 𝒪_loc`** (PROVEN 2026-07-28): the fixed
embedding `ℚ̄ ↪ ℚ̄_q` restricts to the two valuation subrings, because the source
one is the comap of the target one. -/
noncomputable def GaloisRepresentation.globalValuationSubringToLocal
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    GaloisRepresentation.globalValuationSubring v →+* localValuationSubring v where
  toFun a := ⟨AlgebraicClosure.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) a, a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem GaloisRepresentation.globalValuationSubringToLocal_coe
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (a : GaloisRepresentation.globalValuationSubring v) :
    ((GaloisRepresentation.globalValuationSubringToLocal v a : localValuationSubring v) :
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
      = AlgebraicClosure.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) a :=
  rfl

/-- **The maximal ideal of `𝒪` is the contraction of the maximal ideal of `𝒪_loc`**
(PROVEN 2026-07-28). For a valuation subring, non-invertibility of `x` is
`x = 0 ∨ x⁻¹ ∉ A` (`ValuationSubring.mem_nonunits_iff_or`), and both disjuncts are
preserved and reflected by an injective field embedding. -/
theorem GaloisRepresentation.mem_maximalIdeal_globalValuationSubring_iff
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (a : GaloisRepresentation.globalValuationSubring v) :
    a ∈ IsLocalRing.maximalIdeal (GaloisRepresentation.globalValuationSubring v) ↔
      GaloisRepresentation.globalValuationSubringToLocal v a
        ∈ IsLocalRing.maximalIdeal (localValuationSubring v) := by
  rw [ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.valuation_lt_one_iff,
    ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    GaloisRepresentation.globalValuationSubringToLocal_coe]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rwa [← map_inv₀])
  · rintro (h | h)
    · exact Or.inl ((AlgebraicClosure.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))).injective
          (by rw [h, map_zero]))
    · exact Or.inr (by rwa [← map_inv₀] at h)

instance GaloisRepresentation.isLocalHom_globalValuationSubringToLocal
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsLocalHom (GaloisRepresentation.globalValuationSubringToLocal v) := by
  constructor
  intro a hu
  by_contra hnu
  exact ((IsLocalRing.mem_maximalIdeal _).mp
    ((GaloisRepresentation.mem_maximalIdeal_globalValuationSubring_iff v a).mp
      ((IsLocalRing.mem_maximalIdeal a).mpr hnu))) hu

/-- **Residues in `κ(𝒪)` are detected in `κ(𝒪_loc)`** (PROVEN 2026-07-28): the
induced map on residue fields is injective, because the maximal ideal of `𝒪` is the
contraction of that of `𝒪_loc`. -/
theorem GaloisRepresentation.residue_globalValuationSubring_eq_iff
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (a b : GaloisRepresentation.globalValuationSubring v) :
    IsLocalRing.residue (GaloisRepresentation.globalValuationSubring v) a
        = IsLocalRing.residue (GaloisRepresentation.globalValuationSubring v) b ↔
      IsLocalRing.residue (localValuationSubring v)
          (GaloisRepresentation.globalValuationSubringToLocal v a)
        = IsLocalRing.residue (localValuationSubring v)
          (GaloisRepresentation.globalValuationSubringToLocal v b) := by
  have key1 : IsLocalRing.residue (GaloisRepresentation.globalValuationSubring v) a
        = IsLocalRing.residue (GaloisRepresentation.globalValuationSubring v) b
      ↔ a - b ∈ IsLocalRing.maximalIdeal
        (GaloisRepresentation.globalValuationSubring v) := Ideal.Quotient.eq
  have key2 : IsLocalRing.residue (localValuationSubring v)
          (GaloisRepresentation.globalValuationSubringToLocal v a)
        = IsLocalRing.residue (localValuationSubring v)
          (GaloisRepresentation.globalValuationSubringToLocal v b)
      ↔ GaloisRepresentation.globalValuationSubringToLocal v a
          - GaloisRepresentation.globalValuationSubringToLocal v b
        ∈ IsLocalRing.maximalIdeal (localValuationSubring v) := Ideal.Quotient.eq
  rw [key1, key2, ← map_sub]
  exact GaloisRepresentation.mem_maximalIdeal_globalValuationSubring_iff v _

open scoped Pointwise in
/-- **The image of `Γ ℚ_q` lies in the decomposition group of `𝒪`** (PROVEN
2026-07-28): `mem_decompositionSubgroup_localValuationSubring` says `Γ ℚ_q`
stabilises `𝒪_loc`, and `Field.absoluteGaloisGroup.lift_map` says the transported
automorphism is the same automorphism read through the embedding, so it stabilises
the comap. -/
theorem GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ι : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :
    Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ι ∈
      (GaloisRepresentation.globalValuationSubring v).decompositionSubgroup ℚ := by
  have key : ∀ (κ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
      (x : AlgebraicClosure ℚ), x ∈ GaloisRepresentation.globalValuationSubring v →
      Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) κ x
        ∈ GaloisRepresentation.globalValuationSubring v := by
    intro κ x hx
    have hstab : κ • localValuationSubring v = localValuationSubring v :=
      mem_decompositionSubgroup_localValuationSubring v κ
    rw [GaloisRepresentation.mem_globalValuationSubring_iff,
      Field.absoluteGaloisGroup.lift_map, ← hstab]
    exact ⟨_, hx, rfl⟩
  show (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ι) •
    GaloisRepresentation.globalValuationSubring v
      = GaloisRepresentation.globalValuationSubring v
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact key ι x hx
  · intro x hx
    refine ⟨_, key ι⁻¹ x hx, ?_⟩
    show (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ι)
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ι⁻¹) x) = x
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]

/-- **The transported action on `𝒪` is the local action read through the
embedding** (PROVEN 2026-07-28) — `Field.absoluteGaloisGroup.lift_map` again,
packaged for the two decomposition-group actions. -/
theorem GaloisRepresentation.globalValuationSubringToLocal_smul
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ι : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
    (a : GaloisRepresentation.globalValuationSubring v) :
    GaloisRepresentation.globalValuationSubringToLocal v
        ((⟨_, GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring v ι⟩ :
          (GaloisRepresentation.globalValuationSubring v).decompositionSubgroup ℚ) • a)
      = (⟨ι, mem_decompositionSubgroup_localValuationSubring v ι⟩ :
          (localValuationSubring v).decompositionSubgroup
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) •
        GaloisRepresentation.globalValuationSubringToLocal v a :=
  Subtype.ext (Field.absoluteGaloisGroup.lift_map _ _ _)

/-- **The image of `localInertiaGroup q` lies in the inertia subgroup of `𝒪`**
(PROVEN 2026-07-28): the two residue fields are compared by
`residue_globalValuationSubring_eq_iff`, and the local statement is the
already-proven `mem_inertiaSubgroup_localValuationSubring`. -/
theorem GaloisRepresentation.map_mem_inertiaSubgroup_globalValuationSubring
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ι : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
    (hι : ι ∈ localInertiaGroup v) :
    (⟨_, GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring v ι⟩ :
      (GaloisRepresentation.globalValuationSubring v).decompositionSubgroup ℚ) ∈
      (GaloisRepresentation.globalValuationSubring v).inertiaSubgroup ℚ := by
  have hker := mem_inertiaSubgroup_localValuationSubring v ι hι
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hker ⊢
  apply RingEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ :=
    IsLocalRing.residue_surjective (R := GaloisRepresentation.globalValuationSubring v) z
  show IsLocalRing.residue _ ((⟨_,
    GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring v ι⟩ :
      (GaloisRepresentation.globalValuationSubring v).decompositionSubgroup ℚ) • a)
    = IsLocalRing.residue _ a
  rw [GaloisRepresentation.residue_globalValuationSubring_eq_iff,
    GaloisRepresentation.globalValuationSubringToLocal_smul]
  exact DFunLike.congr_fun hker
    (IsLocalRing.residue _ (GaloisRepresentation.globalValuationSubringToLocal v a))

/-- **A local frame for a potentially-good model: an embedding of `K` into `ℚ̄`
placing the prime of `R` at the pinned valuation subring, with an identification
of its residue field with `𝔽̄_q`** (interface, opened 2026-07-27 while cutting
`exists_reductionFrame_of_potentiallyGoodModel` below into three leaves).

THE CONTENT. `D` gives a good model `V` of `E` over a number field `K` with a
DVR `R ⊂ K` whose residue field is `𝔽_q`; nothing in `D` says WHERE `K` sits
inside `ℚ̄`, and every Galois statement below is about `Γ ℚ` acting on `ℚ̄`. A
frame supplies that placement:

* `emb`, `emb_comm` — a `ℚ`-embedding `K ↪ ℚ̄`. Every embedding of `K` into
  `ℚ̄_q` is of this shape followed by the fixed `ℚ̄ ↪ ℚ̄_q`, because `K/ℚ` is
  algebraic and `ℚ̄` is the algebraic closure of `ℚ` inside `ℚ̄_q`.
* `comap_eq` — that placement puts the prime of `R` at the PINNED subring
  `globalValuationSubring q`, in the exact form `h𝒪` that
  `torsion_unramified_of_good_reduction` and its companions ask for. Choosing
  `emb` within its `Γ ℚ`-orbit is the only freedom a frame has, and this
  equation is what uses it up.
* `resIso`, `resIso_comm` — the residue field of that subring, identified with
  `𝔽̄_q` compatibly with `D.resEquiv`. This is not extra content: `ℚ̄` is
  algebraically closed, so the residue field of any valuation subring of it is
  algebraically closed; `ℚ̄/K` is algebraic, so that residue field is algebraic
  over the residue field of `R`, which `D.resEquiv` identifies with `𝔽_q`.
  Hence it IS an algebraic closure of `𝔽_q`, and `resIso` is a choice among the
  `Gal(𝔽̄_q/𝔽_q)`-torsor of isomorphisms.

THE NON-UNIQUENESS IS HARMLESS, and this is worth checking rather than
assuming, because the analogous non-uniqueness of `ψ₀` is FATAL (see the
atomicity audit on `exists_torsionFrame`). Two choices of `resIso` differ by a
power of the `q`-Frobenius; conjugation by that carries
`WeilPairing.frobeniusTorsionEnd` to itself, and permutes the image of
`autTorsionEnd` because `Aut(Ẽ)` is defined over `𝔽_q` and Frobenius therefore
normalises it. Both conclusions of `exists_torsionFrame` are consequently
invariant under the choice, whereas the free-`ψ₀` conjugator ranges over the
whole centraliser of `F` and moves the image of `Aut(Ẽ)`.

`resIso_comm` quantifies over the membership proof `h` rather than deriving it.
That is not vacuous: `comap_eq` supplies such an `h` for every `r`, which is
precisely what `WeierstrassCurve.RtoO` constructs from the same equation. -/
structure WeierstrassCurve.PotentiallyGoodModel.LocalFrame
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) where
  /-- The chosen `ℚ`-embedding of the good-model field into `ℚ̄`. -/
  emb : D.K →+* AlgebraicClosure ℚ
  /-- `emb` is a map of `ℚ`-algebras. -/
  emb_comm : ∀ x : ℚ, emb (algebraMap ℚ D.K x) = algebraMap ℚ (AlgebraicClosure ℚ) x
  /-- `emb` places the prime of `R` at the pinned valuation subring — the
  hypothesis `h𝒪` of the Néron–Ogg–Shafarevich machinery, verbatim. -/
  comap_eq : ((GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).comap emb).toSubring
      = (algebraMap D.R D.K).range
  /-- The residue field of the pinned valuation subring, identified with `𝔽̄_q`. -/
  resIso : IsLocalRing.ResidueField (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat) ≃+* AlgebraicClosure (ZMod q)
  /-- and that identification restricts to `D.resEquiv` on the residue field
  of `R`, which is what makes the reduction land on `D.redCurve`. -/
  resIso_comm : ∀ (r : D.R) (h : emb (algebraMap D.R D.K r) ∈
      GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat),
      resIso (IsLocalRing.residue _ ⟨emb (algebraMap D.R D.K r), h⟩)
        = algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (D.resEquiv (IsLocalRing.residue D.R r))

/-- **The residue field of a valuation subring of `ℚ̄` is an algebraic closure of
`ZMod p`, compatibly with any `R` it dominates** (PROVEN 2026-07-29; the general
form of `WeierstrassCurve.PotentiallyGoodModel.exists_resIso` below, with no
elliptic curve and no number field in sight).

THE TWO FACTS, both proven inline:

* `κ(A)` is ALGEBRAICALLY CLOSED. Lift a monic `p ∈ κ(A)[X]` to a monic
  `P ∈ A[X]` (`Polynomial.lifts_and_degree_eq_and_monic` over the surjection
  `residue`), take a root `x ∈ ℚ̄` (`IsAlgClosed`), observe `x` is integral over
  `A` through `P`, and use that a valuation subring is integrally closed in its
  fraction field (`IsIntegrallyClosed`, `IsFractionRing A ℚ̄` — both mathlib
  instances) to put the root back in `A`.
* `κ(A)` is ALGEBRAIC over `ZMod p`. An `a : A` is algebraic over `ℤ`; its
  PRIMITIVE PART `g` still kills `a` (the content is a nonzero integer) and
  `g mod p ≠ 0` precisely because `g` is primitive — if `p` divided every
  coefficient then `C p ∣ g` would make `p` a unit of `ℤ`. Reducing `g(a) = 0`
  along `residue` exhibits `residue a` as a root of a nonzero polynomial over
  `ZMod p`. (Ring maps out of `ℤ` are unique, so the `ZMod p`-structure and the
  `ℤ`-structure automatically agree — `RingHom.ext_int`.)

Hence `IsAlgClosure (ZMod p) κ(A)` and `IsAlgClosure.equiv` produces the
isomorphism, as a `ZMod p`-ALGEBRA map — which is what makes the compatibility
clause free rather than an extra constraint: `hcomap` turns
`r ↦ ⟨emb (algebraMap R L r), _⟩` into a LOCAL ring map `R → A` (locality is the
`comap` equation again, applied to `(algebraMap R L r)⁻¹`), and the `ZMod p`
algebra structure on `κ(A)` is DEFINED to be the induced one, so
`AlgEquiv.commutes` closes it. -/
theorem GaloisRepresentation.exists_resIso_of_comap_toSubring_eq_range
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L]
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra R L] [IsFractionRing R L]
    (resEquiv : IsLocalRing.ResidueField R ≃+* ZMod p)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (emb : L →+* AlgebraicClosure ℚ)
    (hcomap : (A.comap emb).toSubring = (algebraMap R L).range) :
    ∃ resIso : IsLocalRing.ResidueField A ≃+* AlgebraicClosure (ZMod p),
      ∀ (r : R) (h : emb (algebraMap R L r) ∈ A),
        resIso (IsLocalRing.residue _ ⟨emb (algebraMap R L r), h⟩)
          = algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
              (resEquiv (IsLocalRing.residue R r)) := by
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap R L) := IsFractionRing.injective R L
  have hmem : ∀ r : R, emb (algebraMap R L r) ∈ A := by
    intro r
    have h1 : algebraMap R L r ∈ (A.comap emb).toSubring := by
      rw [hcomap]; exact ⟨r, rfl⟩
    exact h1
  let φ : R →+* A :=
    { toFun := fun r => ⟨emb (algebraMap R L r), hmem r⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; simp }
  have hφ : ∀ r : R, (φ r : AlgebraicClosure ℚ) = emb (algebraMap R L r) := fun _ => rfl
  haveI hloc : IsLocalHom φ := by
    constructor
    intro r hr
    rw [isUnit_iff_exists_inv] at hr
    obtain ⟨w, hw⟩ := hr
    have hw' : emb (algebraMap R L r) * (w : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) hw
      simpa [hφ] using this
    have hne : algebraMap R L r ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    have hwval : (w : AlgebraicClosure ℚ) = emb ((algebraMap R L r)⁻¹) := by
      have hembne : emb (algebraMap R L r) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hw'
        exact zero_ne_one hw'
      have h2 : emb (algebraMap R L r) * emb ((algebraMap R L r)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hne, map_one]
      exact mul_left_cancel₀ hembne (hw'.trans h2.symm)
    have hmemA : emb ((algebraMap R L r)⁻¹) ∈ A := by rw [← hwval]; exact w.2
    have hrange : (algebraMap R L r)⁻¹ ∈ (algebraMap R L).range := by
      rw [← hcomap]; exact hmemA
    obtain ⟨s, hs⟩ := hrange
    refine IsUnit.of_mul_eq_one s ?_
    apply hinj
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hne]
  -- the residue field of `A` is algebraically closed
  haveI hAC : IsAlgClosed (IsLocalRing.ResidueField A) := by
    apply IsAlgClosed.of_exists_root
    intro P0 hmonic hirr
    have hsurj : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
    obtain ⟨P, hPmap, hPdeg, hPmonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective hsurj P0) hmonic
    have hdegne : (P.map (algebraMap A (AlgebraicClosure ℚ))).degree ≠ 0 := by
      rw [hPmonic.degree_map, hPdeg]
      exact (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_root (P.map (algebraMap A (AlgebraicClosure ℚ))) hdegne
    have hint : IsIntegral A x := ⟨P, hPmonic, by rwa [Polynomial.eval₂_eq_eval_map]⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hPy : P.eval y = 0 := by
      have h1 : algebraMap A (AlgebraicClosure ℚ) (P.eval y) = 0 := by
        rw [← Polynomial.eval₂_at_apply (algebraMap A (AlgebraicClosure ℚ)) y, hy,
          ← Polynomial.eval_map]
        exact hx
      have h2 : Function.Injective (algebraMap A (AlgebraicClosure ℚ)) :=
        IsFractionRing.injective A (AlgebraicClosure ℚ)
      exact h2 (by simpa using h1)
    exact ⟨IsLocalRing.residue A y, by
      rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hPy, map_zero]⟩
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField A) :=
    RingHom.toAlgebra ((IsLocalRing.ResidueField.map φ).comp (resEquiv.symm : ZMod p →+* _))
  -- and algebraic over its prime field
  haveI hAA : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := by
    constructor
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have halgQ : IsAlgebraic ℚ ((a : AlgebraicClosure ℚ)) :=
      (AlgebraicClosure.isAlgebraic (k := ℚ)).isAlgebraic _
    have halgZ : IsAlgebraic ℤ ((a : AlgebraicClosure ℚ)) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).2 halgQ
    obtain ⟨f, hf0, hfa⟩ := halgZ
    set g := f.primPart with hgdef
    have hgprim : g.IsPrimitive := f.isPrimitive_primPart
    have hcont : (f.content : ℤ) ≠ 0 := by
      simpa [Polynomial.content_eq_zero_iff] using hf0
    have hga : (Polynomial.aeval ((a : AlgebraicClosure ℚ))) g = 0 := by
      have hfeq := f.eq_C_content_mul_primPart
      rw [hfeq, map_mul, Polynomial.aeval_C] at hfa
      have hne : (algebraMap ℤ (AlgebraicClosure ℚ)) f.content ≠ 0 := by simpa using hcont
      exact (mul_eq_zero.1 hfa).resolve_left hne
    have hgA : (Polynomial.aeval a) g = 0 := by
      have h2 : Function.Injective (algebraMap A (AlgebraicClosure ℚ)) :=
        IsFractionRing.injective A (AlgebraicClosure ℚ)
      apply h2
      rw [map_zero, ← Polynomial.aeval_algebraMap_apply]
      exact hga
    have hgres : (Polynomial.aeval (IsLocalRing.residue A a)) g = 0 := by
      show (Polynomial.aeval (algebraMap A (IsLocalRing.ResidueField A) a)) g = 0
      rw [Polynomial.aeval_algebraMap_apply, hgA, map_zero]
    refine ⟨g.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
    · intro hzero
      have hdvd : (Polynomial.C (p : ℤ)) ∣ g := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro n
        have hc : ((g.coeff n : ℤ) : ZMod p) = 0 := by
          have := congrArg (fun r => Polynomial.coeff r n) hzero
          simpa using this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
      have hu := hgprim _ hdvd
      rw [Int.isUnit_iff] at hu
      have hp2 := hp.two_le
      omega
    · have hcomp : (algebraMap (ZMod p) (IsLocalRing.ResidueField A)).comp
          (Int.castRingHom (ZMod p)) = algebraMap ℤ (IsLocalRing.ResidueField A) :=
        RingHom.ext_int _ _
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      exact hgres
  haveI : IsAlgClosure (ZMod p) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  refine ⟨(IsAlgClosure.equiv (ZMod p) (IsLocalRing.ResidueField A)
    (AlgebraicClosure (ZMod p))).toRingEquiv, ?_⟩
  intro r h
  have hpt : (⟨emb (algebraMap R L r), h⟩ : A) = φ r := Subtype.ext rfl
  have hres : IsLocalRing.residue A (⟨emb (algebraMap R L r), h⟩ : A)
      = algebraMap (ZMod p) (IsLocalRing.ResidueField A) (resEquiv (IsLocalRing.residue R r)) := by
    rw [hpt]
    show _ = (IsLocalRing.ResidueField.map φ) (resEquiv.symm (resEquiv (IsLocalRing.residue R r)))
    rw [RingEquiv.symm_apply_apply, IsLocalRing.ResidueField.map_residue]
  rw [hres]
  exact (IsAlgClosure.equiv (ZMod p) (IsLocalRing.ResidueField A)
    (AlgebraicClosure (ZMod p))).commutes _

open scoped Pointwise in
/-- **Placing a valuation ring of a number field at a prescribed valuation
subring of `ℚ̄`** (PROVEN 2026-07-29 over the transitivity leaf
`GaloisRepresentation.exists_smul_eq_globalValuationSubring`; the general form
of `WeierstrassCurve.PotentiallyGoodModel.exists_emb_comap_eq` below).

THE ARGUMENT. `L/ℚ` is finite, so `IsAlgClosed.lift` gives SOME `ℚ`-embedding
`emb₀ : L ↪ ℚ̄`. `IsLocalRing.exists_factor_valuationRing` (mathlib's form of
CHEVALLEY extension: every local subring of a field is dominated by a valuation
subring) applied to `R → L → ℚ̄` yields a valuation subring `B` of `ℚ̄` and the
LOCALITY of `R → B`. Locality is exactly what pins `emb₀⁻¹ B = R`: `R` is a
valuation ring of `L`, so any `x ∉ R` has `x⁻¹ = algebraMap R L r` with `r` a
nonzero nonunit, and `emb₀ x = emb₀ ((algebraMap R L r)⁻¹) ∈ B` would make
`emb₀ (algebraMap R L r)` a unit of `B`, hence `r` a unit of `R`.

The same computation at `r = (p : R)` — a nonzero nonunit because `resEquiv`
lands in `ZMod p`, so `residue (p : R) = 0` — gives `(p : ℚ̄)⁻¹ ∉ B`, which is
the hypothesis the transitivity leaf consumes. Conjugating by the `γ` it returns
and composing, `emb := γ ∘ emb₀` satisfies `emb⁻¹ A = emb₀⁻¹ B = R`
(`ValuationSubring.smul_mem_pointwise_smul_iff`).

NOTE the `(p : ℚ̄)⁻¹ ∉ B` phrasing is not decoration: it is exactly
`p ∈ B.nonunits` for `p ≠ 0`, i.e. "B lies over `p`", and it is what makes the
transitivity statement TRUE rather than merely plausible — see the leaf. -/
theorem GaloisRepresentation.exists_emb_comap_eq_of_exists_smul_eq
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R L] [IsFractionRing R L]
    (resEquiv : IsLocalRing.ResidueField R ≃+* ZMod p)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hTrans : ∀ B : ValuationSubring (AlgebraicClosure ℚ),
        (algebraMap ℚ (AlgebraicClosure ℚ) (p : ℚ))⁻¹ ∉ B →
        ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ • B = A) :
    ∃ emb : L →+* AlgebraicClosure ℚ,
      (∀ x : ℚ, emb (algebraMap ℚ L x) = algebraMap ℚ (AlgebraicClosure ℚ) x) ∧
      (A.comap emb).toSubring = (algebraMap R L).range := by
  have hinj : Function.Injective (algebraMap R L) := IsFractionRing.injective R L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let emb₀ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hpR0 : (p : R) ≠ 0 := by
    intro h0
    have h1 : algebraMap R L (p : R) = 0 := by rw [h0, map_zero]
    rw [map_natCast] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne' : ((p : ℕ) : L) ≠ 0) h1
  have hpRm : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    apply resEquiv.injective
    rw [map_natCast, map_zero]
    exact ZMod.natCast_self p
  have hpRnu : ¬ IsUnit (p : R) := fun hu =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hpRm hu)
  obtain ⟨B, hmemB, hlocB⟩ := IsLocalRing.exists_factor_valuationRing
      ((emb₀ : L →+* AlgebraicClosure ℚ).comp (algebraMap R L))
  have hnu : ∀ r : R, r ≠ 0 → ¬ IsUnit r → emb₀ ((algebraMap R L r)⁻¹) ∉ B := by
    intro r hr0 hr hmem
    apply hr
    have hne : algebraMap R L r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
    have hprod : emb₀ (algebraMap R L r) * emb₀ ((algebraMap R L r)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    have hu : IsUnit (((emb₀ : L →+* AlgebraicClosure ℚ).comp
        (algebraMap R L)).codRestrict B.toSubring hmemB r) := by
      refine IsUnit.of_mul_eq_one (⟨emb₀ ((algebraMap R L r)⁻¹), hmem⟩ : B.toSubring) ?_
      apply Subtype.ext
      simpa using hprod
    exact hlocB.1 _ hu
  have hcomapB : (B.comap (emb₀ : L →+* AlgebraicClosure ℚ)).toSubring
      = (algebraMap R L).range := by
    apply le_antisymm
    · intro x hx
      by_contra hxR
      rcases ValuationRing.isInteger_or_isInteger R x with h | h
      · exact hxR h
      obtain ⟨r, hr⟩ := h
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hxR (by rw [show x = 0 by simpa using (inv_eq_zero.1 hr.symm)]; exact ⟨0, by simp⟩)
      have hru : ¬ IsUnit r := by
        rintro ⟨u, rfl⟩
        refine hxR ⟨(↑u⁻¹ : R), ?_⟩
        rw [map_units_inv, hr, inv_inv]
      have hxeq : x = (algebraMap R L r)⁻¹ := by rw [hr, inv_inv]
      rw [hxeq] at hx
      exact hnu r hr0 hru hx
    · rintro x ⟨r, rfl⟩
      exact hmemB r
  have hBnot : (algebraMap ℚ (AlgebraicClosure ℚ) (p : ℚ))⁻¹ ∉ B := by
    have hcast : algebraMap ℚ (AlgebraicClosure ℚ) (p : ℚ) = emb₀ (algebraMap R L (p : R)) := by
      simp
    rw [hcast, ← map_inv₀]
    exact hnu (p : R) hpR0 hpRnu
  obtain ⟨γ, hγ⟩ := hTrans B hBnot
  refine ⟨((γ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
      AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
      (emb₀ : L →+* AlgebraicClosure ℚ), fun x => ?_, ?_⟩
  · simp
  · have hkey : A.comap (((γ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
        AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (emb₀ : L →+* AlgebraicClosure ℚ))
        = B.comap (emb₀ : L →+* AlgebraicClosure ℚ) := by
      ext y
      simp only [ValuationSubring.mem_comap, RingHom.comp_apply]
      rw [← hγ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff (g := γ) (S := B) (x := emb₀ y)
    rw [hkey]
    exact hcomapB

open scoped Pointwise in
/-- **`Γ ℚ` acts transitively on the valuation subrings of `ℚ̄` above `q`**
(**PROVEN 2026-07-30** in
`Fermat/FLT/Mathlib/RingTheory/Valuation/AlgebraicIntegerConjugacy.lean`, along
exactly the route the note below prescribes; cut 2026-07-29 while proving
`WeierstrassCurve.PotentiallyGoodModel.exists_emb_comap_eq` below, of which it
was the ONLY remaining input).

WHAT THE PROOF DOES, in the notation of that module. Every valuation subring
`B ⊆ ℚ̄` contains the ring `𝒪 = integralClosure ℤ ℚ̄` of ALL algebraic integers
(a valuation subring is integrally closed in its fraction field), so it has a
CENTRE `center B = 𝔪_B ∩ 𝒪`; the hypothesis `(q : ℚ̄)⁻¹ ∉ B` says exactly that
this centre lies over `(q) ⊆ ℤ` (`under_center_eq`). `Γ ℚ` is profinite and acts
continuously on the DISCRETE ring `𝒪`, with `Algebra.IsInvariant ℤ 𝒪 (Γ ℚ)`, so
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` gives transitivity on
the primes of `𝒪` over `(q)`. What remains — and it is the only place where the
Prüfer property of `𝒪` is used — is that a subring above `q` is DETERMINED by
its centre: that is `exists_den_notMem`, proven by descending to the number field
`ℚ(x)` generated by one element, where mathlib's
`IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq` writes
`x` as `n/d` or `d/n` with `d` outside the prime. Finally `1/q` really is outside
the pinned subring, because `ℤ_q` is integrally closed in `ℚ_q` and `q` lies in
its maximal ideal (`maximalIdeal_adicCompletionIntegers_eq_span`).

Pure valuation theory: no elliptic curve, no `PotentiallyGoodModel`, no residue
fields. Everything else in `exists_emb_comap_eq` — Chevalley extension, the
locality bookkeeping, the transport of the `comap` along `γ` — is proven above
in `GaloisRepresentation.exists_emb_comap_eq_of_exists_smul_eq`.

WHY THE HYPOTHESIS IS THE RIGHT ONE, and why the statement is FAITHFUL. `B` is a
subring of `ℚ̄`, hence contains `ℤ`, so `B ∩ ℚ` is a valuation subring of `ℚ`
containing `ℤ` — i.e. `ℤ_(ℓ)` for some prime `ℓ`, or `ℚ`. The hypothesis
`(q : ℚ̄)⁻¹ ∉ B` excludes `ℚ` and excludes every `ℓ ≠ q` (as `1/q ∈ ℤ_(ℓ)`
there), so it says exactly `B ∩ ℚ = ℤ_(q)`. And
`globalValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat` satisfies the
same condition — it is the comap of `integralClosure 𝒪ᵥ ℚ̄_q` along the fixed
`ℚ̄ ↪ ℚ̄_q`, and `1/q` is not integral over `ℤ_q` because `ℤ_q` is integrally
closed in `ℚ_q` — the prime being `(q)` by
`asIdeal_toHeightOneSpectrumRingOfIntegersRat`. So both sides lie over the SAME
prime of `ℚ`, and the claim is the classical conjugacy of the extensions of
`v_q` to the algebraic closure.

A PROVER'S ROUTE. At finite level mathlib already has it —
`Ideal.exists_smul_eq_of_isGaloisGroup` /
`IsDedekindDomain.HeightOneSpectrum.isPretransitive_of_isGaloisGroup`
(`Mathlib/NumberTheory/RamificationInertia/Galois.lean`) — and for the profinite
limit `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`
(`Mathlib/RingTheory/Invariant/Profinite.lean`) is stated for exactly this
situation: `G` profinite acting continuously on a discrete `B` with
`Algebra.IsInvariant A B G`, concluding transitivity on the primes of `B` over a
prime of `A`. Taking `A = ℤ_(q)` (or `ℤ`) and `B` the integral closure of `ℤ` in
`ℚ̄`, with `G = Γ ℚ`, that lemma gives the transitivity on PRIMES; converting a
prime of `B` to a valuation subring of `ℚ̄` and back is the remaining bridge
(`ValuationSubring.ofPrime` / `LocalSubring`), together with the identification
of `B ∩ ℚ` above.

THE CHECK THAT WOULD REFUTE THIS LEAF: a valuation subring of `ℚ̄` lying over
`ℤ_(q)` that is not in the `Γ ℚ`-orbit of the pinned one — equivalently a
failure of conjugacy of the extensions of `v_q` to `ℚ̄`, or a proof that
`globalValuationSubring hq.…` does NOT satisfy `(q : ℚ̄)⁻¹ ∉ ·` (which would
make the target of the conjugation lie over a different prime, or be all of
`ℚ̄`). -/
theorem GaloisRepresentation.exists_smul_eq_globalValuationSubring
    {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (B : ValuationSubring (AlgebraicClosure ℚ))
    (hB : (algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ))⁻¹ ∉ B) :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      γ • B = GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat := by
  have hA : (algebraMap ℚ (AlgebraicClosure ℚ) (q : ℚ))⁻¹ ∉
      GaloisRepresentation.globalValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat :=
    AlgebraicIntegersRat.inv_natCast_notMem_comap_localValuationSubring hq
  exact AlgebraicIntegersRat.exists_smul_eq_of_valuationSubring hq B _ hB hA

/-- **The placement of `K` inside `ℚ̄` that puts the prime of `R` at the pinned
subring** (sorry leaf, opened 2026-07-28 by cutting `nonempty_localFrame` below
into its VALUATION-THEORETIC and its RESIDUE-FIELD halves).

This is item 1 of `nonempty_localFrame`'s docstring and it is pure valuation
theory: `R` is a discrete valuation ring with fraction field `K` whose residue
field has characteristic `q` (`D.resEquiv`), so `R ∩ ℚ = ℤ_(q)`. Choose ANY
`ℚ`-embedding `emb₀ : K ↪ ℚ̄` (`K/ℚ` is finite and `ℚ̄` is algebraically closed);
extend the valuation of `R` along `emb₀` to a valuation subring `𝒪'` of `ℚ̄`
(Chevalley), so that `emb₀⁻¹ 𝒪' = R`. Both `𝒪'` and
`globalValuationSubring q` lie over `ℤ_(q)`, and `Γ ℚ` acts TRANSITIVELY on the
valuation subrings of `ℚ̄` above a fixed prime of `ℚ`; pick `γ` carrying `𝒪'` to
`globalValuationSubring q` and set `emb := γ ∘ emb₀`. Then
`emb⁻¹ (globalValuationSubring q) = emb₀⁻¹ 𝒪' = R`.

NO ELLIPTIC CURVE APPEARS: `D` is used only through `D.K`, `D.R` and
`D.resEquiv`, and `E` only as an index.

THE CHECK THAT WOULD REFUTE THIS LEAF is the one recorded on
`nonempty_localFrame`: a prime of `K` above `q` outside the single `Γ ℚ`-orbit.
Equivalently, a failure of Chevalley extension or of conjugacy of the extensions
of `v_q` to `ℚ̄`. -/
theorem WeierstrassCurve.PotentiallyGoodModel.exists_emb_comap_eq
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) :
    ∃ emb : D.K →+* AlgebraicClosure ℚ,
      (∀ x : ℚ, emb (algebraMap ℚ D.K x) = algebraMap ℚ (AlgebraicClosure ℚ) x) ∧
      ((GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).comap emb).toSubring
        = (algebraMap D.R D.K).range :=
  GaloisRepresentation.exists_emb_comap_eq_of_exists_smul_eq D.resEquiv _
    (fun B hB => GaloisRepresentation.exists_smul_eq_globalValuationSubring hq B hB)

/-- **The residue field of the pinned subring is an algebraic closure of `𝔽_q`,
compatibly with `D.resEquiv`** (sorry leaf, opened 2026-07-28 by cutting
`nonempty_localFrame` below into its VALUATION-THEORETIC and its RESIDUE-FIELD
halves).

This is item 2 of `nonempty_localFrame`'s docstring. `ℚ̄` is algebraically
closed, so the residue field `κ(𝒪)` of any valuation subring of it is
algebraically closed; `ℚ̄/ℚ` is algebraic, so `κ(𝒪)` is algebraic over the
residue field of `𝒪 ∩ ℚ = ℤ_(q)`, i.e. over `𝔽_q`. Hence `κ(𝒪)` IS an algebraic
closure of `𝔽_q` and `resIso` exists by uniqueness of algebraic closures.

WHY `hcomap` IS THE ONLY HYPOTHESIS NEEDED FOR THE COMPATIBILITY, and why the
compatibility is not an extra constraint on the choice of `resIso`: `hcomap`
makes `r ↦ ⟨emb (algebraMap D.R D.K r), _⟩` a ring map `D.R → 𝒪` (this is
`WeierstrassCurve.RtoO`'s construction verbatim) which is LOCAL
(`WeierstrassCurve.isLocalHom_RtoO`), hence induces a ring map
`κ(D.R) → κ(𝒪)`. Both sides of the required identity are therefore ring
homomorphisms out of `κ(D.R) ≃+* ZMod q` — and **any two ring homomorphisms out
of `ZMod q` agree** (`RingHom.ext_zmod`). So the compatibility holds for EVERY
`resIso`; it is recorded in the conclusion only because `LocalFrame` bundles it.

NO ELLIPTIC CURVE APPEARS here either.

THE CHECK THAT WOULD REFUTE THIS LEAF: a valuation subring of an algebraically
closed field whose residue field is not algebraically closed, or a `D` whose
`D.R` has residue characteristic different from `q` — the latter is excluded by
`D.resEquiv`, which lands in `ZMod q`. -/
theorem WeierstrassCurve.PotentiallyGoodModel.exists_resIso
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) (emb : D.K →+* AlgebraicClosure ℚ)
    (hcomap : ((GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).comap emb).toSubring
      = (algebraMap D.R D.K).range) :
    ∃ resIso : IsLocalRing.ResidueField (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat) ≃+* AlgebraicClosure (ZMod q),
      ∀ (r : D.R) (h : emb (algebraMap D.R D.K r) ∈
        GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat),
        resIso (IsLocalRing.residue _ ⟨emb (algebraMap D.R D.K r), h⟩)
          = algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
              (D.resEquiv (IsLocalRing.residue D.R r)) :=
  GaloisRepresentation.exists_resIso_of_comap_toSubring_eq_range D.resEquiv _ emb hcomap

/-- **Every potentially-good model admits a local frame** (PROVEN 2026-07-28 by
assembly; opened 2026-07-27 by cutting
`exists_reductionFrame_of_potentiallyGoodModel` below into three).

Pure algebraic number theory; no elliptic curve appears, and `E` enters only as
an index. What has to be proven:

1. the primes of `K` above `q` are exactly the pullbacks of
   `globalValuationSubring q` along the `ℚ`-embeddings `K ↪ ℚ̄`, so `R` is hit
   by some embedding. `Γ ℚ` acts transitively on the valuation subrings of `ℚ̄`
   above `q`, and `K/ℚ` algebraic puts every embedding `K ↪ ℚ̄_q` inside the
   image of `ℚ̄`;
2. the residue field of a valuation subring of an ALGEBRAICALLY CLOSED field is
   algebraically closed, and here it is algebraic over the residue field of `R`;
   hence it is an algebraic closure of `𝔽_q` and `resIso` exists by uniqueness
   of algebraic closures, `resIso_comm` being the extension property.

THE CHECK THAT WOULD REFUTE THIS LEAF: a `PotentiallyGoodModel` whose `R` is
induced by no embedding `K ↪ ℚ̄` — which would need a prime of `K` above `q`
outside the single `Γ ℚ`-orbit, i.e. a failure of going-up plus conjugacy.

CUT 2026-07-28. The two numbered items above share no technique — the first is
conjugacy of extensions of a valuation, the second is uniqueness of algebraic
closures — so they are now the two separately-ownable leaves
`exists_emb_comap_eq` and `exists_resIso` below, and this declaration is their
assembly. Nothing else is left here: `LocalFrame` has exactly four fields and
the two leaves supply two each. -/
theorem WeierstrassCurve.PotentiallyGoodModel.nonempty_localFrame
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) : Nonempty (D.LocalFrame hq) := by
  obtain ⟨emb, hcomm, hcomap⟩ := D.exists_emb_comap_eq hq
  obtain ⟨resIso, hres⟩ := D.exists_resIso hq emb hcomap
  exact ⟨⟨emb, hcomm, hcomap, resIso, hres⟩⟩

/-- **Residue degree one is inherited by the compositum `ℚ_q · F`** (PROVEN
2026-07-28; the DENSITY half of
`exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne` below).

WHAT IT SAYS. `F` is a subfield of `ℚ̄_q` all of whose integral elements are
congruent to a RATIONAL INTEGER mod `𝔪`. Then the same holds for every integral
element of the compositum `ℚ_q · F` — spelled here as
`IntermediateField.adjoin ℚ_q F`, which is exactly the compositum since `ℚ̄_q/ℚ_q`
is algebraic.

WHY IT IS TRUE, and this is the ONLY place the base field's being `ℚ` is used.
`F` is a field, so it contains `ℚ`, which is DENSE in `ℚ_q`
(`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`). An element of the
compositum is a finite `ℚ_q`-linear combination `b = ∑ cᵢ fᵢ` with `fᵢ ∈ F`
(`Algebra.adjoin_eq_span`, the monoid closure of a subfield being the subfield);
each `fᵢ` has an integral multiple `dᵢ fᵢ ∈ 𝒪` with `dᵢ ∈ ℤ_q ∖ 0`
(`IsAlgebraic.exists_integral_multiple`). Approximating `cᵢ` by a rational `qᵢ`
to precision `dᵢ · ϖ` — the set `cᵢ − dᵢ ϖ · ℤ_q` is a NEIGHBOURHOOD of `cᵢ`,
being the preimage of the open unit ball under multiplication by a nonzero
scalar — gives `cᵢ − qᵢ = dᵢ wᵢ` with `wᵢ ∈ 𝔪ᵥ`, whence
`b − ∑ qᵢ fᵢ = ∑ wᵢ · (dᵢ fᵢ) ∈ 𝔪` because `𝔪` lies over `𝔪ᵥ`. So `y := ∑ qᵢ fᵢ`
lies in `F` (the `qᵢ` are rational, `F` is a field) AND in `𝒪` (it differs from
the integral `b` by an element of `𝔪`), and `hres` applied to `y` finishes.

NO METRIC ON `ℚ̄_q` IS USED: the approximation happens entirely inside `ℚ_q`,
where `Valued.isOpen_valuationSubring` supplies the one topological fact needed.
The `ϖ` is any nonzero element of `𝔪ᵥ` — an irreducible of the DVR `ℤ_q` — and
it need not generate.

THE CHECK THAT WOULD REFUTE THIS LEAF: an integral element of `ℚ_q · F` at
positive distance from `F`. Over a base in which `F` is NOT dense this really
happens — see the `ℚ_p(√p)` / `ℚ(√(mp))` counterexample recorded on
`exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne` below, which is
why that leaf's base field may not be generalised. -/
theorem GaloisRepresentation.exists_int_sub_mem_maximalIdeal_of_mem_adjoin
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (F : Subfield (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
    (hres : ∀ b : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b ∈ F →
      ∃ n : ℤ, b - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈
        IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
    (b : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
    (hb : algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b ∈
      IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        (F : Set (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))) :
    ∃ n : ℤ, b - (n : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈
      IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
  classical
  -- STEP 1: `b` lies in the `ℚ_q`-span of `F`.
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x),
    ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at hb
  have hmon : ((Submonoid.closure (F : Set (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :
      Submonoid (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) : Set _)
      = (F : Set (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
    Set.Subset.antisymm
      ((Submonoid.closure_le (S := F.toSubring.toSubmonoid)).mpr (fun _ h => h))
      Submonoid.subset_closure
  rw [hmon] at hb
  obtain ⟨m, cc, gg, hsum⟩ := Submodule.mem_span_set'.mp hb
  -- STEP 2: integral denominators for the generators.
  have hden : ∀ i : Fin m, ∃ d : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
      d ≠ 0 ∧ IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (d • (gg i : AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := fun i =>
    IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))).mpr
        (Algebra.IsAlgebraic.isAlgebraic _))
  choose d hd0 hdint using hden
  -- STEP 3: a nonzero element of the maximal ideal of `ℤ_q`.
  obtain ⟨pi, hpiirr⟩ := IsDiscreteValuationRing.exists_irreducible
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
  have hpimem : pi ∈ IsLocalRing.maximalIdeal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) :=
    (IsLocalRing.mem_maximalIdeal pi).mpr hpiirr.not_isUnit
  have hpi0 : pi ≠ 0 := hpiirr.ne_zero
  have hinj : Function.Injective (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := fun _ _ h => Subtype.ext h
  -- STEP 4: rational approximations of the coefficients, to precision `d i · pi`.
  have hdens : ∀ i : Fin m, ∃ (q : ℚ)
      (w : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v),
      w ∈ IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) ∧
      cc i - (q : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        = algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) (d i)
          * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) w := by
    intro i
    have ht0 : algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) (d i)
        * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) pi ≠ 0 :=
      mul_ne_zero (fun h => hd0 i (hinj (by simpa using h)))
        (fun h => hpi0 (hinj (by simpa using h)))
    set t : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v :=
      algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) (d i)
        * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) pi with ht
    have hTeq : {y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v |
          ∃ o : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
            y = t * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) o}
        = (fun y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v => t⁻¹ * y) ⁻¹'
          ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) : Set _) := by
      ext y
      constructor
      · rintro ⟨o, rfl⟩
        show t⁻¹ * (t * algebraMap _ _ o) ∈
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
        rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
        exact o.2
      · intro hy
        exact ⟨⟨t⁻¹ * y, hy⟩, by
          show y = t * (t⁻¹ * y)
          rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]⟩
    have hTopen : IsOpen {y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v |
        ∃ o : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
          y = t * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) o} := by
      rw [hTeq]
      exact (Valued.isOpen_valuationSubring
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)).preimage
        (continuous_const.mul continuous_id)
    have hSopen : IsOpen {y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v |
        ∃ o : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
          cc i - y = t * algebraMap _
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) o} := by
      have hpre : {y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v |
            ∃ o : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
              cc i - y = t * algebraMap _ _ o}
          = (fun y : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v => cc i - y) ⁻¹'
            {z : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v |
              ∃ o : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
                z = t * algebraMap _ _ o} := rfl
      rw [hpre]
      exact hTopen.preimage (Continuous.sub continuous_const continuous_id)
    obtain ⟨q, o, ho⟩ :=
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap ℚ v).exists_mem_open
        hSopen ⟨cc i, 0, by simp⟩
    rw [eq_ratCast] at ho
    exact ⟨q, pi * o, Ideal.mul_mem_right _ _ hpimem, by
      rw [map_mul, ← mul_assoc, ← ht]; exact ho⟩
  choose q w hwmem hweq using hdens
  -- STEP 5: the correction term `z ∈ 𝔪`, so that `b - z` lies in `F`.
  have hmap : ∀ x : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v,
      x ∈ IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) →
      algebraMap _ (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) x ∈
      IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
    intro x hx
    rw [Ideal.over_def
      (A := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (P := IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      (p := IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v))] at hx
    exact hx
  set G : Fin m → IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
    fun i => ⟨d i • (gg i : AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)), hdint i⟩ with hGdef
  set z : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
    ∑ i, algebraMap _ (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (w i) * G i with hzdef
  have hzmem : z ∈ IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
    Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ (hmap _ (hwmem i)))
  have hzval : algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) z
      = algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b
        - ∑ i, (q i : AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
          * (gg i : AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := by
    rw [hzdef, map_sum, ← hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, ← IsScalarTower.algebraMap_apply
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))]
    have e1 : algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (G i)
        = d i • (gg i : AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := rfl
    rw [e1]
    have hsmO : ∀ (r : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (x : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
        r • x = algebraMap _ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) r * x :=
      fun r x => Algebra.smul_def r x
    have hsmK : ∀ (r : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        (x : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
        r • x = algebraMap _ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) r * x :=
      fun r x => Algebra.smul_def r x
    have e2 : algebraMap _ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (w i)
          * (d i • (gg i : AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
            (algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) (d i)
              * algebraMap _ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) (w i))
          * (gg i : AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := by
      rw [hsmO, map_mul,
        IsScalarTower.algebraMap_apply
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (w i),
        IsScalarTower.algebraMap_apply
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (d i)]
      ring
    rw [e2, ← hweq i, map_sub, sub_mul, map_ratCast, hsmK]
  -- STEP 6: `b - z` is an integral element of `F`, so it is an integer mod `𝔪`.
  obtain ⟨n, hn⟩ := hres (b - z) (by
    rw [map_sub, hzval]
    have e3 : algebraMap _ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b
        - (algebraMap _ (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b
          - ∑ i, (q i : AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
            * (gg i : AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        = ∑ i, (q i : AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
            * (gg i : AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := by ring
    rw [e3]
    exact Subfield.sum_mem _ (fun i _ =>
      F.mul_mem (SubfieldClass.ratCast_mem F _) (gg i).2))
  refine ⟨n, ?_⟩
  have e4 : b - (n : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      = z + (b - z - (n : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))) := by
    ring
  rw [e4]
  exact Ideal.add_mem _ hzmem hn

open scoped Pointwise in
set_option maxHeartbeats 1000000 in
/-- **Residue degree one over the prime field makes the pointwise stabiliser of an
INTERMEDIATE FIELD realise every residue action** (PROVEN 2026-07-28; opened the
same day by cutting `exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne`
below into its DENSITY half — `exists_int_sub_mem_maximalIdeal_of_mem_adjoin`
above — and this, its INVARIANT-THEORY half).

WHAT IT SAYS. `M` is a subextension of `ℚ̄_q/ℚ_q` whose integral elements are all
congruent to rational integers mod `𝔪`, i.e. `M/ℚ_q` has residue degree one.
Then for every `σ ∈ Γ ℚ_q` there is a `g ∈ Γ ℚ_q` fixing `M` POINTWISE and
inducing the same map as `σ` on the residue field of
`𝒪 = IntegralClosure ℤ_q ℚ̄_q`. Equivalently `Γ ℚ_q = Gal(ℚ̄_q/M) · I_q`.

WHY THE HYPOTHESIS IS STATED AS A CONGRUENCE TO `ℤ` AND NOT AS `k_M = 𝔽_q`: the
residue field of `𝒪 ∩ M` is not a type this development carries, whereas
"congruent to a rational integer mod `𝔪`" is a statement about `𝒪` alone and is
exactly what the density leaf above delivers and what the caller
(`exists_inertia_frobLift_fixes_emb`) has in hand.

THE ROUTE (all of `IsGalois ↥M ℚ̄_q`, `CompactSpace (ℚ̄_q ≃ₐ[↥M] ℚ̄_q)`,
`TotallyDisconnectedSpace`, `IsTopologicalGroup`,
`Algebra.IsInvariant ↥M ℚ̄_q (ℚ̄_q ≃ₐ[↥M] ℚ̄_q)` and
`ContinuousSMulDiscrete (ℚ̄_q ≃ₐ[↥M] ℚ̄_q) 𝒪` already synthesise for a general
`M`; the ONE gap is `SMulCommClass (ℚ̄_q ≃ₐ[↥M] ℚ̄_q) ℤ_q ℚ̄_q`, not an instance
but immediate — `g` is `↥M`-linear and `ℤ_q ⊆ ℚ_q ⊆ M` — so it is supplied by a
local `haveI`):

1. Put `H := ℚ̄_q ≃ₐ[↥M] ℚ̄_q`, acting on `𝒪` through
   `mulSemiringActionIntegralClosure`, and let `A ⊆ 𝒪` be the subring of
   `H`-invariants. Then `Algebra.IsInvariant A 𝒪 H` holds BY CONSTRUCTION — this
   is what avoids ever forming the type `IntegralClosure ℤ_q ↥M`, whose algebra
   instances in `LocalInertiaFixedField` are stated only for
   `[FiniteDimensional ℚ_q N]` and so do not apply here.
2. `Ideal.Quotient.stabilizerHom_surjective_of_profinite A 𝔪` then says
   `H ↠ Aut((𝒪/𝔪) / (A/𝔪∩A))`.
3. `σ` stabilises `𝔪` (the unique maximal ideal) so induces an automorphism of
   `𝒪/𝔪`; it is `A/𝔪∩A`-linear BECAUSE OF `hres`: an invariant `a ∈ A` lies in
   `M` (`Algebra.IsInvariant ↥M ℚ̄_q H`, the project instance for `IsGalois`), so
   `a ≡ n` for a rational integer `n`, and `σ` fixes `n`.
4. Pull back through (2) and restrict scalars to `ℚ_q`: `g := τ.restrictScalars`
   fixes `M` pointwise and has `σ`'s residue action, which is the conclusion.

THE CHECK THAT WOULD REFUTE THIS LEAF: an `M` of residue degree one over `ℚ_q`
with `Gal(ℚ̄_q/M)` mapping onto a PROPER subgroup of `Gal(𝔽̄_q/𝔽_q)`. Note the
hypothesis is genuinely about `M`, not about a dense subfield of it: the
unramified quadratic `M = ℚ_q(√u)` (`u` a non-residue unit) has residue degree
`2` and is exactly what `hres` excludes. -/
theorem GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_intermediateField
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (M : IntermediateField (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
    (hres : ∀ b : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b ∈ M →
      ∃ n : ℤ, b - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈
        IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
    (σ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :
    ∃ g : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v),
      (∀ x ∈ M, g x = x) ∧
      ∀ b : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
        σ • b - g • b ∈ IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
  classical
  -- `ℤ_q` sits inside `M`, so `Gal(ℚ̄_q/M)` commutes with it (the one missing instance).
  have hsmO : ∀ (r : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (x : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      r • x = algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) r * x :=
    fun r x => Algebra.smul_def r x
  haveI hcc : SMulCommClass
      ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) := by
    constructor
    intro g r x
    show g (r • x) = r • (g x)
    rw [hsmO, hsmO, map_mul]
    congr 1
    rw [IsScalarTower.algebraMap_apply
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      IsScalarTower.algebraMap_apply
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) M
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))]
    exact g.commutes _
  haveI hcc2 : SMulCommClass
      ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
    constructor
    intro g r x
    exact Subtype.ext (smul_comm g r x.1)
  -- THE FIXED SUBRING, which is what avoids ever forming `IntegralClosure ℤ_q ↥M`.
  set A : Subalgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
    FixedPoints.subalgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) with hA
  haveI hinv : Algebra.IsInvariant A
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
    ⟨fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  haveI hcc3 : SMulCommClass
      ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) A
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
    constructor
    intro g a x
    show g • (a.1 * x) = a.1 * (g • x)
    rw [MulSemiringAction.smul_mul, a.2 g]
  letI : TopologicalSpace (IntegralClosure
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := ⊥
  haveI : DiscreteTopology (IntegralClosure
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := ⟨rfl⟩
  set P : Ideal A := (IsLocalRing.maximalIdeal (IntegralClosure
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
    (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))).under A
    with hPdef
  -- Every ring automorphism of the LOCAL ring `𝒪` preserves `𝔪` (units are preserved).
  have hcomapgen : ∀ e : (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ≃+*
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))),
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))).comap
        (e : (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) →+*
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      = IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
    intro e
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h hu
      exact h (hu.map (e : (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) →+*
        (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))))
    · intro h hu
      exact h (by simpa using hu.map (e.symm : (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) →+*
        (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))))
  set sr := MulSemiringAction.toRingEquiv
    (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
    (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ with hsr
  have hmapeq : IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      = (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))).map
        (sr : (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) →+*
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))) :=
    (hcomapgen sr.symm).symm.trans (Ideal.comap_symm sr)
  -- `σ` is the identity on the residues of `A`, BY `hres`: an invariant lies in `M`.
  have hAmemM : ∀ a : A, algebraMap _ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (a : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈ M := by
    intro a
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := M)
      (G := (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      (algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (a : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      (fun g => congrArg Subtype.val (a.2 g))
    exact hy ▸ y.2
  have hAcomm : ∀ a : A, σ • (a : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      - (a : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
      ∈ IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
    intro a
    obtain ⟨n, hn⟩ := hres (a : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) (hAmemM a)
    have hstab : ∀ m : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
        m ∈ IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) →
        σ • m ∈ IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
      intro m hm
      have hcg := hcomapgen sr
      rw [← hcg] at hm
      exact hm
    have h1 := hstab _ hn
    have h2 : σ • ((a : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
        = σ • (a : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
      rw [smul_sub]
      congr 1
      exact map_intCast (MulSemiringAction.toRingHom _ (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ) n
    rw [h2] at h1
    have h3 : σ • (a : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        - (a : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        = (σ • (a : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
          - (n : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
          - ((a : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
          - (n : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))) := by ring
    rw [h3]
    exact Ideal.sub_mem _ h1 hn
  -- the residue action of `σ`, as an `A ⧸ P`-algebra automorphism of `𝒪 ⧸ 𝔪`
  obtain ⟨τ, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ≃ₐ[M]
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
    P (IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
    (AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv _ _ sr hmapeq) (by
      rintro ⟨a⟩
      exact Ideal.Quotient.eq.mpr (hAcomm a)))
  refine ⟨((τ : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
    ≃ₐ[M] (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))).restrictScalars
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v), ?_, ?_⟩
  · intro x hx
    exact ((τ : (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
      ≃ₐ[M] (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))).commutes (⟨x, hx⟩ : M)
  · intro b
    refine Ideal.Quotient.eq.mp ?_
    exact (DFunLike.congr_fun hτ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))) b)).symm

/-- **Residue degree one over the PRIME field makes `Gal(ℚ̄_q/F·ℚ_q)` surject onto
`Gal(𝔽̄_q/𝔽_q)`** (PROVEN 2026-07-28 over
`exists_int_sub_mem_maximalIdeal_of_mem_adjoin` and
`exists_fixing_sub_smul_mem_maximalIdeal_of_intermediateField` above, both also
proven; opened 2026-07-28 by cutting `exists_inertia_frobLift_fixes_emb` below
into its ELLIPTIC-CURVE-FREE local core and its assembly).

CUT 2026-07-28 into a DENSITY half and an INVARIANT-THEORY half, which share no
technique: the first is "`ℚ` is dense in `ℚ_q`, so `k_{ℚ_q·F} = k_{𝒪∩F}`" and
lives entirely inside `ℚ_q`; the second is Galois descent for the profinite group
`Gal(ℚ̄_q/M)` and never mentions `ℚ`. Both are proven; this declaration is their
assembly, and the ONLY thing it does is instantiate the second at
`M := ℚ_q · F = IntermediateField.adjoin ℚ_q F` and note `F ⊆ M`.

WHAT IT SAYS. `F` is any subfield of `ℚ̄_q`. The hypothesis `hres` is
*residue degree one*: every element of `F` that is integral over `ℤ_q` is
congruent, modulo the maximal ideal of `𝒪 = IntegralClosure ℤ_q ℚ̄_q`, to a
RATIONAL INTEGER — i.e. the residue field of `𝒪 ∩ F` is the prime field `𝔽_q`.
The conclusion is that the subgroup of `Γ ℚ_q` fixing `F` pointwise already
realises every residue action: for each `σ` there is a `g` fixing `F` pointwise
with `σ • b ≡ g • b (mod 𝔪)` for every integral `b`.

WHY IT IS TRUE. Write `M := ℚ_q · F`, a subextension of `ℚ̄_q/ℚ_q`. Because `F`
is a field it contains `ℚ`, which is DENSE in `ℚ_q`, so `F` is dense in `M`;
residues are locally constant on `𝒪`, so `k_M = k_{𝒪 ∩ F} = 𝔽_q`, i.e. `M/ℚ_q`
has residue degree one. Invariant theory of `ℤ_q ⊆ 𝒪` (mathlib's
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`, applicable since
`Algebra.IsInvariant ℤ_q 𝒪 (Γ ℚ_q)` — `isInvariant_integralClosure` — and
`Γ ℚ_q` is profinite) makes `Γ ℚ_q ↠ Aut(𝔽̄_q/𝔽_q)` with kernel the inertia
group, and the same theorem over `𝒪_M` makes `Gal(ℚ̄_q/M) ↠ Aut(𝔽̄_q/k_M)`.
With `k_M = 𝔽_q` the two images coincide, so `σ`'s residue action is hit by some
`g ∈ Gal(ℚ̄_q/M) = ` the pointwise stabiliser of `F`. That `g` is the witness.

**THE BASE FIELD MUST BE `ℚ`; the statement is FALSE over a general number
field, and this is not a formalisation artefact.** The density step is what uses
`ℚ ⊆ F` dense in `ℚ_q`. Over a base `K` with `Kᵥ/ℚ_p` ramified the analogous
statement fails: take `p` odd, `Kᵥ = ℚ_p(√p)` (so `k_v = 𝔽_p`) and
`F = ℚ(√(mp))` with `m` a non-residue mod `p`. Then `𝒪 ∩ F` has residue field
`𝔽_p = k_v`, so the hypothesis holds; but `Kᵥ · F = ℚ_p(√p, √(mp)) ∋ √m`
contains the unramified quadratic extension, so `Gal(ℚ̄_p/Kᵥ·F)` has index `2`
in `Γ Kᵥ` modulo inertia and misses the Frobenius class. The compositum of two
totally ramified extensions need not be totally ramified — that is the whole
obstruction, and it disappears over `ℚ` because `F ⊇ ℚ` is then already dense in
the base.

NO ELLIPTIC CURVE, NO `PotentiallyGoodModel` AND NO FRAME APPEAR: this is a
statement about `ℚ_q`, one subfield of `ℚ̄_q`, and one Galois element.

THE CHECK THAT WOULD REFUTE THIS LEAF: an `F` satisfying `hres` whose compositum
with `ℚ_q` has residue degree `> 1` — equivalently, an integral element of
`ℚ_q · F` whose residue is not a limit of residues from `F`. Over `ℚ` that
contradicts density of `ℚ` in `ℚ_q`; see the displayed counterexample for what
goes wrong once the base is allowed to ramify. -/
theorem GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (F : Subfield (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
    (hres : ∀ b : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) b ∈ F →
      ∃ n : ℤ, b - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈
        IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
    (σ : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :
    ∃ g : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v),
      (∀ x ∈ F, g x = x) ∧
      ∀ b : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
        σ • b - g • b ∈ IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
  -- Assembly: pass from the subfield `F` to the compositum `M = ℚ_q · F`, using
  -- density of `ℚ` in `ℚ_q` to carry `hres` across (the leaf above), and then
  -- read off the pointwise stabiliser of `F` from that of `M ⊇ F`.
  obtain ⟨g, hgfix, hgres⟩ :=
    GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_intermediateField v
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
        (F : Set (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      (fun b hb =>
        GaloisRepresentation.exists_int_sub_mem_maximalIdeal_of_mem_adjoin v F hres b hb) σ
  exact ⟨g, fun x hx => hgfix x (IntermediateField.subset_adjoin _ _ hx), hgres⟩

/-- **RESIDUE DEGREE ONE, AND NOTHING ELSE: an inertia element `ι` at `q` with
`ι⁻¹ · Frob_q` fixing `emb K` pointwise** (PROVEN 2026-07-28 over
`GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne`
above; opened 2026-07-28 by cutting `exists_frobeniusLift` below).

CUT 2026-07-28, and this is where `D.resEquiv` is SPENT. The leaf mixed two
things that share no technique:

1. *residue degree one for this particular frame* — that every element of
   `Fr.emb K` which is integral over `ℤ_q` is congruent to a rational integer
   modulo `𝔪`. This is now PROVEN below, and it is the only use `D`, `E`,
   `Fr.comap_eq` and `D.resEquiv` get: `Fr.comap_eq` turns integrality of
   `emb x` into `x ∈ R`, `D.resEquiv` writes `residue r` as an integer because
   it lands in the PRIME field `ZMod q`, and non-invertibility descends back
   along `emb` because `emb⁻¹ 𝒪 = R` exactly (this is `RtoO`'s local-hom
   argument, inlined against `ValuationSubring.mem_nonunits_iff_or`);
2. *the local-field theorem that residue degree one buys surjectivity onto
   `Gal(𝔽̄_q/𝔽_q)`* — no curve, no model, no frame. That is the new leaf
   `exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne` above, stated
   for an arbitrary subfield `F ⊆ ℚ̄_q`, and it is where the remaining
   arithmetic lives.

Given the witness `g` of (2) at `σ := Frob_q`, the rest is group algebra:
`ι := Frob_q · g⁻¹` lies in `localInertiaGroup q` because
`Frob_q • (g⁻¹ • b) ≡ g • (g⁻¹ • b) = b` for every integral `b`, and
`ι⁻¹ · Frob_q = g`; the transport to `Γ ℚ` is `Field.absoluteGaloisGroup.map`
being a monoid hom, `globalFrob` being BY DEFINITION the transported local
Frobenius (the internal `ℚ →+* ℚ_q` being pinned by `Subsingleton.elim`), and
`Field.absoluteGaloisGroup.lift_map` plus injectivity of `ℚ̄ ↪ ℚ̄_q`.

THIS IS THE WHOLE ARITHMETIC CONTENT OF `exists_frobeniusLift`, and it is the
ONLY place in that cut where `D.resEquiv` is consumed. Everything else in
`exists_frobeniusLift` is transport along the fixed embedding `ℚ̄ ↪ ℚ̄_q`
(`map_mem_decompositionSubgroup_globalValuationSubring`,
`map_mem_inertiaSubgroup_globalValuationSubring`) or the defining property of
`Field.AbsoluteGaloisGroup.adicArithFrob`, and all of that is proven above.

WHY IT IS TRUE. Write `K_𝔮 ⊆ ℚ̄_q` for the closure of the image of `Fr.emb`
under the fixed embedding — this is the completion of `K` at the prime that
`Fr.comap_eq` identifies with the prime of `D.R`. `D.resEquiv` says the residue
field of `D.R` is the PRIME field `𝔽_q`, so `K_𝔮/ℚ_q` has residue degree one and
`Gal(ℚ̄_q/K_𝔮) ↠ Gal(𝔽̄_q/𝔽_q)`. Pick `g ∈ Gal(ℚ̄_q/K_𝔮)` inducing `x ↦ x^q` on
residues and set `ι := Frob_q · g⁻¹`; then `ι` induces the identity on residues,
hence lies in `localInertiaGroup q`, and `ι⁻¹ · Frob_q = g` fixes the image of
`Fr.emb` pointwise by construction. Transport to `Γ ℚ` is
`Field.absoluteGaloisGroup.lift_map` plus injectivity of `ℚ̄ ↪ ℚ̄_q`: a
transported automorphism fixes `Fr.emb x` exactly when the original fixes its
image.

Equivalently and more structurally: `I · Gal(ℚ̄_q/K_𝔮) = Γ ℚ_q`, because
`Γ ℚ_q / I ≅ Gal(𝔽̄_q/𝔽_q)` and the image of `Gal(ℚ̄_q/K_𝔮)` there is the whole
group precisely when the residue degree is `1`. `Frob_q ∈ I · Gal(ℚ̄_q/K_𝔮)` is
the statement above.

NOTHING ABOUT ELLIPTIC CURVES APPEARS: `D` enters through `D.K` and
`D.resEquiv`, and `Fr` through `Fr.emb` and `Fr.comap_eq`.

THE CHECK THAT WOULD REFUTE THIS LEAF: a `PotentiallyGoodModel` and frame at
which the image of `Gal(ℚ̄_q/K_𝔮)` in `Gal(𝔽̄_q/𝔽_q)` is PROPER — i.e. residue
degree `> 1`, which is exactly what `D.resEquiv` excludes by landing in `ZMod q`
rather than in a proper extension of it. -/
theorem WeierstrassCurve.PotentiallyGoodModel.exists_inertia_frobLift_fixes_emb
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) (Fr : D.LocalFrame hq) :
    ∃ ι ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ x : D.K, ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
          GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) (Fr.emb x) = Fr.emb x := by
  -- RESIDUE DEGREE ONE for this frame.  This is the only step that consumes
  -- `D.resEquiv`, `Fr.comap_eq` and the model `D` at all.
  have hres : ∀ b : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)),
      algebraMap _ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) b ∈
        ((AlgebraicClosure.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).comp Fr.emb).fieldRange →
      ∃ n : ℤ, b - (n : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) ∈
        IsLocalRing.maximalIdeal (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    intro b hb
    obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hb
    rw [RingHom.comp_apply] at hx
    -- integrality of `emb x` puts `x` in `R`, by `Fr.comap_eq`
    have hmemO : Fr.emb x ∈ GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat := by
      rw [GaloisRepresentation.mem_globalValuationSubring_iff, hx]
      exact b.2
    have hxR : x ∈ (algebraMap D.R D.K).range := by
      rw [← Fr.comap_eq]; exact hmemO
    obtain ⟨r, hr⟩ := hxR
    -- `D.resEquiv` lands in the PRIME field, so `residue r` is a rational integer
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (D.resEquiv (IsLocalRing.residue D.R r))
    refine ⟨n, ?_⟩
    have hs : r - (n : D.R) ∈ IsLocalRing.maximalIdeal D.R := by
      have h0 : IsLocalRing.residue D.R (r - (n : D.R)) = 0 := by
        apply D.resEquiv.injective
        rw [map_zero, map_sub, map_sub, map_intCast, map_intCast, hn, sub_self]
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hy : algebraMap D.R D.K (r - (n : D.R)) = x - (n : D.K) := by
      rw [map_sub, map_intCast, hr]
    -- non-invertibility descends along `emb`, because `emb⁻¹ 𝒪 = R` EXACTLY
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have hval := congrArg (algebraMap (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) hc
    rw [map_mul, map_one, map_sub, map_intCast] at hval
    have hleft : algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) b
          - (n : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
        = AlgebraicClosure.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
            (Fr.emb (algebraMap D.R D.K (r - (n : D.R)))) := by
      rw [hy, map_sub, map_intCast, map_sub, map_intCast, hx]
    rw [hleft] at hval
    have hne : AlgebraicClosure.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (Fr.emb (algebraMap D.R D.K (r - (n : D.R)))) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hval
      exact zero_ne_one hval
    have hinv : algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) c
        = AlgebraicClosure.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
            (Fr.emb ((algebraMap D.R D.K (r - (n : D.R)))⁻¹)) := by
      rw [map_inv₀, map_inv₀]
      exact (inv_eq_of_mul_eq_one_right hval).symm
    have hmemInv : Fr.emb ((algebraMap D.R D.K (r - (n : D.R)))⁻¹) ∈
        GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat := by
      rw [GaloisRepresentation.mem_globalValuationSubring_iff, ← hinv]
      exact c.2
    have hmemInv2 : (algebraMap D.R D.K (r - (n : D.R)))⁻¹ ∈ (algebraMap D.R D.K).range := by
      rw [← Fr.comap_eq]; exact hmemInv
    obtain ⟨t, ht⟩ := hmemInv2
    have hyne : algebraMap D.R D.K (r - (n : D.R)) ≠ 0 := by
      intro h0
      exact hne (by rw [h0, map_zero, map_zero])
    have hrt : (r - (n : D.R)) * t = 1 := by
      apply IsFractionRing.injective D.R D.K
      rw [map_mul, map_one, ht, mul_inv_cancel₀ hyne]
    exact (IsLocalRing.mem_maximalIdeal _).mp hs (isUnit_iff_exists_inv.mpr ⟨t, hrt⟩)
  -- the local-field leaf, applied at `σ := Frob_q`
  obtain ⟨g, hgfix, hgres⟩ :=
    GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne
      hq.toHeightOneSpectrumRingOfIntegersRat
      ((AlgebraicClosure.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).comp Fr.emb).fieldRange
      hres (Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)
  refine ⟨Field.AbsoluteGaloisGroup.adicArithFrob
    hq.toHeightOneSpectrumRingOfIntegersRat * g⁻¹, ?_, ?_⟩
  · -- `Frob_q · g⁻¹` acts trivially on residues, hence lies in inertia
    refine AddSubgroup.mem_inertia.mpr fun b => ?_
    have h := hgres (g⁻¹ • b)
    rwa [smul_smul, smul_inv_smul] at h
  · intro x
    -- `globalFrob` IS the transported local Frobenius; ring maps out of `ℚ` are unique
    have hglob : GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
        = Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) := by
      have hf : ∀ f₁ f₂ : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat,
          Field.absoluteGaloisGroup.map f₁ (Field.AbsoluteGaloisGroup.adicArithFrob
              hq.toHeightOneSpectrumRingOfIntegersRat)
            = Field.absoluteGaloisGroup.map f₂ (Field.AbsoluteGaloisGroup.adicArithFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) := by
        intro f₁ f₂
        rw [Subsingleton.elim f₁ f₂]
      exact hf _ _
    have hmapeq : (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat * g⁻¹))⁻¹ *
          GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
        = Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) g := by
      rw [hglob, map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [hmapeq]
    apply (AlgebraicClosure.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).injective
    rw [Field.absoluteGaloisGroup.lift_map]
    exact hgfix _ (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)

/-- **Residue degree one produces a Frobenius lift inside the decomposition
group of `K`** (PROVEN 2026-07-28 over `exists_inertia_frobLift_fixes_emb`;
opened 2026-07-27 by cutting `exists_reductionFrame_of_potentiallyGoodModel`
below into three).

WHAT IT SAYS, writing `𝒪 := globalValuationSubring q` and `t` for the image of
`ι` in `Γ ℚ`: there is an inertia element `ι` of `Γ ℚ_q` such that
`σ := t⁻¹ · Frob_q` (i) fixes `emb K` pointwise and (ii) induces `x ↦ x^q` on
the residue field of `𝒪`; and `t` itself lies in the inertia subgroup of `𝒪`.
Everything is phrased so that `exists_torsionFrame` below never has to mention
`ℚ_q` again.

WHY IT IS TRUE, and where each hypothesis is used. `D.resEquiv` makes the
residue field of `R` the PRIME field, so the completion `K_𝔮/ℚ_q` has residue
degree one and `Gal(ℚ̄_q/K_𝔮)` still surjects onto `Gal(𝔽̄_q/𝔽_q)` — THIS IS
WHAT RESIDUE DEGREE ONE BUYS. Pick `g ∈ Gal(ℚ̄_q/K_𝔮)` inducing the `q`-power
map on residues and set `ι := Frob_q · g⁻¹`; then `ι` acts trivially on
residues, hence lies in `localInertiaGroup q`, and `ι⁻¹ · Frob_q = g` by
construction. `Field.absoluteGaloisGroup.map` is a monoid homomorphism and
`globalFrob` is BY DEFINITION the image of the local arithmetic Frobenius, so
the identity survives transport into `Γ ℚ`.

NOTHING ABOUT ELLIPTIC CURVES APPEARS: `D` enters only through `D.K` and
`D.resEquiv`, and `Fr` only through `Fr.emb`.

THE TRANSPORT OF THE TWO SUBGROUPS along `Field.absoluteGaloisGroup.map` — which
the 2026-07-27 version of this docstring named as "the first step a prover should
take" — IS NOW DONE, above: `map_mem_decompositionSubgroup_globalValuationSubring`
and `map_mem_inertiaSubgroup_globalValuationSubring`, with the maximal ideal of a
comap valuation subring handled by
`mem_maximalIdeal_globalValuationSubring_iff`. The friction that note warned
about is real — `Γ ℚ` and `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ` are
reducibly but not syntactically equal, so `rw [MulAction.mem_stabilizer_iff]`
fails with an instance mismatch — and it is dealt with there by `show` plus
explicit `⟨_, _⟩` ascriptions.

WHAT REMAINS (updated 2026-07-28): `exists_inertia_frobLift_fixes_emb` above is
now PROVEN, and the residual open node is the elliptic-curve-free local leaf
`GaloisRepresentation.exists_fixing_sub_smul_mem_maximalIdeal_of_residueDegreeOne`
— residue degree one over the prime field makes the pointwise stabiliser of a
subfield of `ℚ̄_q` surject onto `Gal(𝔽̄_q/𝔽_q)`. Conclusion (ii) is AUTOMATIC and costs no arithmetic
— `ι` acts trivially on residues because it is in inertia, and `Frob_q` acts as
`x ↦ x^q` by `Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob` together
with `natCard_residue_quotient_toHeightOneSpectrum` (which is what pins the
exponent of `IsArithFrobAt` to `q`), so `ι⁻¹ · Frob_q` acts as `x ↦ x^q`
whatever `ι` is. That is why the cut below puts ALL of the residue-degree-one
content in the existence statement and none of it here.

THE CHECK THAT WOULD REFUTE THIS LEAF: a `PotentiallyGoodModel` at which every
`ι ∈ localInertiaGroup q` leaves `t⁻¹ Frob_q` moving `K` — which needs the
image of `Gal(ℚ̄_q/K_𝔮)` in `Gal(𝔽̄_q/𝔽_q)` to be proper, i.e. residue degree
`> 1`, which is exactly what `resEquiv` excludes. -/
theorem WeierstrassCurve.PotentiallyGoodModel.exists_frobeniusLift
    {E : WeierstrassCurve ℚ} {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (D : E.PotentiallyGoodModel q) (Fr : D.LocalFrame hq) :
    ∃ (ι : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (_ : ι ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      (hdecT : Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι ∈
        (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
      (hdecS : (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
          GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat ∈
        (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ),
      (⟨_, hdecT⟩ : (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) ∈
        (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup ℚ ∧
      (∀ x : D.K, ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
          GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) (Fr.emb x) = Fr.emb x) ∧
      (∀ z : GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat,
        (⟨_, hdecS⟩ : (GaloisRepresentation.globalValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) •
          IsLocalRing.residue _ z = (IsLocalRing.residue _ z) ^ q) := by
  obtain ⟨ι, hι, hfix⟩ := D.exists_inertia_frobLift_fixes_emb hq Fr
  have hdecT := GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring
    hq.toHeightOneSpectrumRingOfIntegersRat ι
  have hdecFrob := GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring
    hq.toHeightOneSpectrumRingOfIntegersRat
    (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)
  -- `globalFrob` is the transported local Frobenius; the ring map `ℚ →+* ℚ_q` inside it need
  -- not be SYNTACTICALLY the one this file writes, but ring maps out of `ℚ` are unique.
  have hglob : GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
      = Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) := by
    have hf : ∀ f₁ f₂ : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat,
        Field.absoluteGaloisGroup.map f₁ (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)
          = Field.absoluteGaloisGroup.map f₂ (Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) := by
      intro f₁ f₂
      rw [Subsingleton.elim f₁ f₂]
    exact hf _ _
  have hdecS : (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
      GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ∈
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ := by
    rw [hglob]
    exact mul_mem (inv_mem hdecT) hdecFrob
  refine ⟨ι, hι, hdecT, hdecS,
    GaloisRepresentation.map_mem_inertiaSubgroup_globalValuationSubring _ ι hι, hfix, ?_⟩
  intro z
  -- Rewrite the ambient decomposition-group element as a single transported one.
  have heq : (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
        GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
      = Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        (ι⁻¹ * Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hglob, map_mul, map_inv]
  have hsub : (⟨_, hdecS⟩ : (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
      = ⟨_, GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat
          (ι⁻¹ * Field.AbsoluteGaloisGroup.adicArithFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)⟩ := Subtype.ext heq
  rw [hsub, show (IsLocalRing.residue _ z) ^ q
      = IsLocalRing.residue (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat) (z ^ q) from (map_pow _ _ _).symm]
  show IsLocalRing.residue _ ((⟨_,
      GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat
        (ι⁻¹ * Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)⟩ :
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) • z)
    = IsLocalRing.residue _ (z ^ q)
  rw [GaloisRepresentation.residue_globalValuationSubring_eq_iff,
    GaloisRepresentation.globalValuationSubringToLocal_smul, map_pow]
  -- Split the local element into its inertia part and its Frobenius part.
  set y := GaloisRepresentation.globalValuationSubringToLocal
    hq.toHeightOneSpectrumRingOfIntegersRat z
  have hsplit : (⟨ι⁻¹ * Field.AbsoluteGaloisGroup.adicArithFrob
        hq.toHeightOneSpectrumRingOfIntegersRat,
      mem_decompositionSubgroup_localValuationSubring _ _⟩ :
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
      = (⟨ι⁻¹, mem_decompositionSubgroup_localValuationSubring _ _⟩ : _) *
        ⟨Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat,
          mem_decompositionSubgroup_localValuationSubring _ _⟩ := Subtype.ext rfl
  rw [hsplit, mul_smul]
  -- Inertia acts trivially on the residue field.
  have hker := mem_inertiaSubgroup_localValuationSubring
    hq.toHeightOneSpectrumRingOfIntegersRat ι⁻¹ (inv_mem hι)
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hker
  have hinv : ∀ w : localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat,
      IsLocalRing.residue _ ((⟨ι⁻¹, mem_decompositionSubgroup_localValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat ι⁻¹⟩ :
        (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) • w)
      = IsLocalRing.residue _ w :=
    fun w => DFunLike.congr_fun hker (IsLocalRing.residue _ w)
  rw [hinv]
  -- and the arithmetic Frobenius raises residues to the `q`-th power.
  have hyq := Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob
    (v := hq.toHeightOneSpectrumRingOfIntegersRat)
    ⟨(y : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)), y.2⟩
  rw [GaloisRepresentation.natCard_residue_quotient_toHeightOneSpectrum hq] at hyq
  exact Ideal.Quotient.eq.mpr hyq

/-- **The good model of `D`, placed inside `ℚ̄` by the frame** (PROVEN 2026-07-28,
opened while cutting `exists_torsionFrame` below along the COORDINATEWISE
characterisation of the reduction map — the split that leaf's own atomicity audit
names as the recommended one).

`D.V_eq` says `V = C • E_K`; pushing that equation along the frame's embedding
`Fr.emb : K ↪ ℚ̄` and using `emb_comm` to collapse `ℚ → K → ℚ̄` into `ℚ → ℚ̄`
gives the same sentence over `ℚ̄`. Nothing here is about reduction: this is the
"transport `E`-points to `V`-points along `D.C`" step that the audit records as
the one prerequisite of the coordinatewise formulation. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.model_eq
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {q : ℕ} [Fact q.Prime] {hq : q.Prime}
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq) :
    D.V.map Fr.emb
      = (D.C.map Fr.emb) • (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  have hcomp : Fr.emb.comp (algebraMap ℚ D.K) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    RingHom.ext Fr.emb_comm
  rw [D.V_eq, ← WeierstrassCurve.map_variableChange]
  congr 1
  show (E.map (algebraMap ℚ D.K)).map Fr.emb = _
  rw [WeierstrassCurve.map_map, hcomp]

/-- **The frame's identification of the `ℚ̄`-points of `E` with those of the good
model** (PROVEN 2026-07-28): the point-level transport along `D.C`, carried to
`ℚ̄` through `Fr.emb`.

This is `Affine.Point.equivVariableChange` (project shim
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`) read
backwards through `model_eq`. It is what lets the reduction map be pinned by
COORDINATES: a torsion point of `E` over `ℚ̄` has no integrality of its own, but
its image on the GOOD model `V` does, because `V` is a minimal integral model
over the DVR `D.R`. -/
noncomputable def WeierstrassCurve.PotentiallyGoodModel.LocalFrame.modelEquiv
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {q : ℕ} [Fact q.Prime] {hq : q.Prime}
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq) :
    (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point ≃+
      (D.V.map Fr.emb).toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivVariableChange
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (D.C.map Fr.emb)).symm.trans
    (WeierstrassCurve.Affine.Point.equivOfEq Fr.model_eq.symm)

/-- **The COORDINATEWISE pinning of the reduction map on `N`-torsion**
(definition, opened 2026-07-28 while cutting `exists_torsionFrame` below into
three).

`Fr.IsTorsionReduction ψ₀` says: for every `N`-torsion point `P` of `E` over
`ℚ̄`, if the corresponding point of the GOOD model `V` (via `modelEquiv`) is
affine with coordinates `X, Y`, then `X` and `Y` lie in the pinned valuation
subring `𝒪 = globalValuationSubring q`, and `ψ₀ P` is the point of
`Ẽ = D.redCurve` over `𝔽̄_q` whose coordinates are the residues of `X` and `Y`
carried along `Fr.resIso`.

WHY THIS PREDICATE IS WHAT MAKES THE CUT OF `exists_torsionFrame` SAFE. That
leaf's ATOMICITY AUDIT (reproduced there in full, and still standing) shows every
cut handing `ψ₀` over as FREE data is FALSE: two solutions of the Frobenius
intertwining differ by an element of the centraliser of `F`, which at
`q ≡ 1 mod N` is all of `GL₂(ZMod N)` and moves the image of `Aut(Ẽ)`. The
audit's own stated refutation is "a formulation whose hypotheses pin `ψ₀` up to
the image of `Aut(Ẽ)` — for instance a statement of the reduction map by its
coordinatewise definition". This IS that formulation, and it is in fact stronger
than the audit anticipated: the coordinates are pinned outright, not merely up to
`Aut(Ẽ)`, because the transport `E → V` is along the GIVEN variable change `D.C`
and the residue identification is the GIVEN `Fr.resIso`. So a witness `ψ₀` is
unique, and the two conclusions of the atom cannot come apart.

The integrality of `X` and `Y` is part of the CONCLUSION rather than a
hypothesis, deliberately: it is proven once, inside `exists_isTorsionReduction`,
out of `torsion_abscissa_mem` and `torsion_ordinate_mem`, and both consumers then
receive it instead of each re-deriving it.

NOT VACUOUS: `ψ₀` is a linear EQUIVALENCE and the pinning determines it at every
point, so a witness has to BE the genuine reduction map — in particular its
existence forces reduction to be injective on `E[N]`, which is where the
arithmetic sits. -/
def WeierstrassCurve.PotentiallyGoodModel.LocalFrame.IsTorsionReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} {q : ℕ} [Fact q.Prime]
    {hq : q.Prime} {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)) :
    Prop :=
  ∀ (P : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N)
    (X Y : AlgebraicClosure ℚ) (hns : (D.V.map Fr.emb).toAffine.Nonsingular X Y),
    (Fr.modelEquiv P.val = WeierstrassCurve.Affine.Point.some X Y hns) →
    ∃ (hX : X ∈ GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (hY : Y ∈ GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (hns' : (D.redCurve.map
            (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).toAffine.Nonsingular
          (Fr.resIso (IsLocalRing.residue _ ⟨X, hX⟩))
          (Fr.resIso (IsLocalRing.residue _ ⟨Y, hY⟩))),
      (ψ₀ P).val = WeierstrassCurve.Affine.Point.some _ _ hns'

/-- **THE REDUCTION MAP ON `N`-TORSION EXISTS, AND IS PINNED COORDINATEWISE**
(PROVEN 2026-07-28; opened the same day by cutting `exists_torsionFrame` below
into three along the coordinatewise characterisation of `ψ₀`).

WHAT IT SAYS: there is a `ZMod N`-linear EQUIVALENCE
`ψ₀ : E[N](ℚ̄) ≃ Ẽ[N](𝔽̄_q)`, `Ẽ := D.redCurve`, which is the honest reduction
map — for every `N`-torsion point of `E` over `ℚ̄` the coordinates of the
corresponding point of the good model `V` lie in `𝒪`, and `ψ₀` sends it to the
point with the residue coordinates.

NO GALOIS THEORY APPEARS. Neither `σ` nor `τ` occurs; this leaf is
Néron–Ogg–Šafarevič's integrality and injectivity plus a counting surjectivity,
and nothing else. That separation is the point of the cut: the two equivariances
of the atom are proven ABOUT this map by the two leaves below, which receive it
WITH its coordinatewise pinning and therefore cannot be satisfied by a conjugated
junk witness.

HOW IT IS PROVEN — and the survey this leaf inherited was pointing at the wrong
machinery. Steps 2 and 3 of the old plan (well-definedness and additivity of the
reduction map) do NOT have to be redone: they already exist, sorry-free and fully
general, as `WeierstrassCurve.IsReductionAlong` and its
`redHom : W(F) →+ Wred(κ)` in
`KnownIn1980s/EllipticCurves/PointReduction.lean` (Silverman *AEC* VII.2.1 —
integrality and reduction of `negY`/`addX`/`addY`, the integral chord–tangent
slope, and the kernel analysis `addX_notMem_of_res_opposite` /
`not_isIntegralPoint_add`). **`WeilPairing.exists_frobenius_reduction_model` is
therefore NOT the pattern to copy**; adapting that ~2800-line monolith would have
been rebuilding an existing API. The proof is:

1. *The reduction datum.* Good reduction makes `D.V` integral over `D.R`, so each
   coefficient is `algebraMap D.R D.K r` (`integralModel_aᵢ_eq`); `Fr.comap_eq`
   puts its `Fr.emb`-image in `𝒪 = globalValuationSubring q`, and
   `Fr.resIso_comm` computes its residue as the corresponding coefficient of
   `D.redCurve ⊗ 𝔽̄_q`. Those ten facts ARE
   `IsReductionAlong 𝒪 ρ (D.V.map Fr.emb) (D.redCurve ⊗ 𝔽̄_q)` for
   `ρ := Fr.resIso ∘ IsLocalRing.residue 𝒪`, which is an `IsLocalHom` because
   `residue` is one and every ring map out of a field is one.
2. *Well-definedness and additivity*: `hred.redHom hΔ`, with `hΔ` supplied by
   `instIsEllipticRedCurve` above. Composing with `Fr.modelEquiv` gives an
   ADDITIVE map on all of `E(ℚ̄)`, not merely on torsion.
3. *Injectivity on `E[N]` — and this is where the `N = 2` obligation
   DISAPPEARED.* `IsReductionAlong.redFun_eq_zero_iff` says the kernel of
   reduction is EXACTLY the affine points with non-integral abscissa, and
   `torsion_abscissa_mem` (`KnownIn1980s/EllipticCurves/GoodReduction.lean`,
   PROVEN, applied with `R := D.R`, `k := D.K`, `E := D.V`,
   `ksep := AlgebraicClosure ℚ` through `Fr.emb.toAlgebra` and `h𝒪` supplied
   VERBATIM by `Fr.comap_eq`) says every `N`-torsion abscissa IS integral. So a
   nonzero `N`-torsion point cannot reduce to `O`. Note that
   `torsion_abscissa_mem` needs only `NeZero (N : κ(D.R))`, i.e. `q ≠ N`; the
   `IsSepClosure` hypothesis of its section is `omit`ted from it, so no
   separable-closure instance has to be produced for `ℚ̄/D.K` either.
4. *Surjectivity by counting*: `n_torsion_card` gives `N²` on both sides
   (`IsSepClosed` on both closures; `N ≠ 0` in `ℚ̄` by characteristic zero and in
   `𝔽̄_q` because `q ≠ N`), so an injective additive map between them is bijective
   (`Nat.bijective_iff_injective_and_card`), and `AddMonoidHom.toZModLinearMap`
   upgrades it to the `ZMod N`-linear equivalence.

**THE `N = 2` OBLIGATION IS DISCHARGED, NOT INHERITED** (2026-07-28; the note it
replaces is reproduced almost verbatim in `exists_torsionFrame`'s docstring below
and has been corrected there too). That note said oddness of `N` was consumed
through `torsion_abscissa_residue_ne` and `torsion_ordinate_eq_of_residue_eq`, so
a prover must either supply their `n = 2` case or restate this leaf with `Odd N`.
**Neither was necessary: this proof uses neither lemma.** Injectivity of reduction
on prime-to-`q` torsion does not go through "distinct torsion points have distinct
residues" at all — only through "torsion points are integral, and the kernel of
reduction is exactly the non-integral locus" (Silverman VII.3.1's actual
argument). The statement is unchanged and holds for every prime `N ≠ q`, `N = 2`
included, and `torsion_unramified_of_good_reduction`'s `Odd n` never enters.

**`hq2 : q ≠ 2` IS GONE FROM THE SIGNATURE** (2026-07-29). It was first
underscore-prefixed here when this leaf was proven, to make its uselessness
mechanically visible, and kept only because dropping it would churn a proven
declaration. That trade reversed as soon as a CONSUMER at `q = 2` appeared:
`exists_inertiaAut_of_padicValRat_j_nonneg` (`B₀²ᵃ`, far below) has to call this
leaf at `q = 2`, where no `q ≠ 2` can be produced at all, so an unused hypothesis
was the single thing forcing a separate `2`-adic leaf under it. Nothing in the
proof below changed; only the binder was deleted. The one call site that held
`hq2` (`exists_torsionFrame` below) keeps its own binder, renamed `_hq2`.

THE CHECK THAT WOULD REFUTE THIS LEAF: an `N`-torsion point of `E` over `ℚ̄`
whose image on `D.V` has a coordinate outside `𝒪`, or two distinct `N`-torsion
points with the same residue coordinates. The first contradicts
`torsion_abscissa_mem` at the minimal integral model `D.V`; the second
contradicts `torsion_abscissa_residue_ne`, whose hypotheses (`N` prime, `N`
invertible in the residue field, good reduction) are all in hand. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.exists_isTorsionReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] {hq : q.Prime} (hqN : q ≠ N)
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq) :
    ∃ ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N),
      Fr.IsTorsionReduction ψ₀ := by
  classical
  letI : Algebra D.K (AlgebraicClosure ℚ) := Fr.emb.toAlgebra
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  set 𝒪 : ValuationSubring (AlgebraicClosure ℚ) :=
    GaloisRepresentation.globalValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat
  set ρ : 𝒪 →+* AlgebraicClosure (ZMod q) :=
    (Fr.resIso : IsLocalRing.ResidueField 𝒪 →+* AlgebraicClosure (ZMod q)).comp
      (IsLocalRing.residue 𝒪) with hρdef
  haveI : IsLocalHom ρ := by
    rw [hρdef]; exact RingHom.isLocalHom_comp _ _
  -- Step 1: the images of `D.R` are integral, and their residues are computed by
  -- `Fr.resIso_comm`.
  have hmem : ∀ r : D.R, Fr.emb (algebraMap D.R D.K r) ∈ 𝒪 := by
    intro r
    have hr : algebraMap D.R D.K r ∈ (algebraMap D.R D.K).range := ⟨r, rfl⟩
    rw [← Fr.comap_eq] at hr
    exact hr
  have hcoeff : ∀ (a : D.K) (r : D.R), algebraMap D.R D.K r = a →
      ∃ h : Fr.emb a ∈ 𝒪, ρ ⟨Fr.emb a, h⟩
        = algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (D.resEquiv (IsLocalRing.residue D.R r)) := by
    intro a r har
    subst har
    exact ⟨hmem r, Fr.resIso_comm r (hmem r)⟩
  obtain ⟨hm1, he1⟩ := hcoeff D.V.a₁ _ (WeierstrassCurve.integralModel_a₁_eq D.R D.V)
  obtain ⟨hm2, he2⟩ := hcoeff D.V.a₂ _ (WeierstrassCurve.integralModel_a₂_eq D.R D.V)
  obtain ⟨hm3, he3⟩ := hcoeff D.V.a₃ _ (WeierstrassCurve.integralModel_a₃_eq D.R D.V)
  obtain ⟨hm4, he4⟩ := hcoeff D.V.a₄ _ (WeierstrassCurve.integralModel_a₄_eq D.R D.V)
  obtain ⟨hm6, he6⟩ := hcoeff D.V.a₆ _ (WeierstrassCurve.integralModel_a₆_eq D.R D.V)
  -- so `D.redCurve ⊗ 𝔽̄_q` IS the reduction of the good model along `ρ`.
  have hred : WeierstrassCurve.IsReductionAlong 𝒪 ρ (D.V.map Fr.emb)
      (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) :=
    ⟨hm1, hm2, hm3, hm4, hm6, he1.symm, he2.symm, he3.symm, he4.symm, he6.symm⟩
  have hΔ : (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).Δ ≠ 0 :=
    (inferInstance :
      (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).IsElliptic).isUnit.ne_zero
  -- `N` is invertible in the residue field of `D.R` — this is the ONLY arithmetic
  -- hypothesis the integrality step needs, and it is `q ≠ N`.
  haveI hNez : NeZero ((N : ℕ) : IsLocalRing.ResidueField D.R) := by
    refine ⟨fun h0 => ?_⟩
    have h1 : D.resEquiv ((N : ℕ) : IsLocalRing.ResidueField D.R) = 0 := by
      rw [h0, map_zero]
    rw [map_natCast, ZMod.natCast_eq_zero_iff] at h1
    exact hqN ((Nat.prime_dvd_prime_iff_eq Fact.out hN).mp h1)
  -- Step 2 (integrality): `N`-torsion points of the good model have integral coordinates.
  have habs : ∀ {x y : AlgebraicClosure ℚ}
      (h : (D.V.map Fr.emb).toAffine.Nonsingular x y),
      (N : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        (D.V.map Fr.emb).toAffine.Point) = 0 → x ∈ 𝒪 :=
    fun h htor => WeierstrassCurve.torsion_abscissa_mem D.R D.K D.V N
      (AlgebraicClosure ℚ) 𝒪 Fr.comap_eq h htor
  have hord : ∀ {x y : AlgebraicClosure ℚ}
      (h : (D.V.map Fr.emb).toAffine.Nonsingular x y),
      (N : ℤ) • (WeierstrassCurve.Affine.Point.some x y h :
        (D.V.map Fr.emb).toAffine.Point) = 0 → y ∈ 𝒪 :=
    fun h htor => WeierstrassCurve.torsion_ordinate_mem D.R D.K D.V N
      (AlgebraicClosure ℚ) 𝒪 Fr.comap_eq h htor
  -- Step 3 (well-definedness and additivity): the reduction homomorphism on ALL points
  -- of `E` over `ℚ̄`, transported along `D.C` by `Fr.modelEquiv`.
  set f : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point →+
      (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).toAffine.Point :=
    (hred.redHom hΔ).comp Fr.modelEquiv.toAddMonoidHom
  have hfapply : ∀ P, f P = hred.redFun hΔ (Fr.modelEquiv P) := fun _ => rfl
  -- Step 4 (injectivity): the kernel of reduction is the non-integral locus, and
  -- torsion abscissae are integral.  No oddness of `N` is consumed.
  have hker : ∀ P : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point,
      (N : ℤ) • P = 0 → f P = 0 → P = 0 := by
    intro P hP hfP
    have hQ : (N : ℤ) • (Fr.modelEquiv P) = 0 := by
      rw [← map_zsmul, hP, map_zero]
    suffices hh : Fr.modelEquiv P = 0 by
      have h2 := congrArg Fr.modelEquiv.symm hh
      rwa [AddEquiv.symm_apply_apply, map_zero] at h2
    rcases hMP : Fr.modelEquiv P with _ | ⟨x, y, hns⟩
    · rfl
    · exfalso
      rw [hMP] at hQ
      have hx : x ∈ 𝒪 := habs hns hQ
      have h0 : hred.redFun hΔ (WeierstrassCurve.Affine.Point.some x y hns) = 0 := by
        rw [← hMP, ← hfapply]; exact hfP
      exact ((hred.redFun_eq_zero_iff hΔ hns).mp h0) hx
  have htor : ∀ P : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N,
      (N : ℤ) • P.val = 0 := fun P => (Submodule.mem_torsionBy_iff _ _).mp P.2
  -- restrict the reduction homomorphism to `N`-torsion
  let g : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) →+
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) :=
    { toFun := fun P => ⟨f P.val, (Submodule.mem_torsionBy_iff _ _).mpr
        ((map_zsmul f (N : ℤ) P.val).symm.trans
          ((congrArg (⇑f) (htor P)).trans (map_zero f)))⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun P Q => Subtype.ext (map_add f P.val Q.val) }
  have hgval : ∀ P, (g P).val = f P.val := fun _ => rfl
  have hginj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro P hP0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    refine hker P.val (htor P) ?_
    have hz := congrArg Subtype.val hP0
    rwa [hgval, ZeroMemClass.coe_zero] at hz
  -- Step 5 (surjectivity): both torsion groups have `N²` elements.
  have hNQ : ((N : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    simpa using hN.ne_zero
  have hNF : ((N : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro h0
    have h1 : ((N : ℕ) : ZMod q) = 0 := by
      have := h0
      rw [← map_natCast (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) N] at this
      exact (map_eq_zero_iff _ (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective).mp this
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hqN ((Nat.prime_dvd_prime_iff_eq Fact.out hN).mp h1)
  have hcard1 : Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) = N ^ 2 :=
    WeierstrassCurve.n_torsion_card _ hNQ
  have hcard2 : Nat.card
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) = N ^ 2 :=
    WeierstrassCurve.n_torsion_card _ hNF
  haveI hfin : Finite
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) := by
    have hpos : 0 < Nat.card
        ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) := by
      rw [hcard2]; exact pow_pos hN.pos 2
    exact (Nat.card_pos_iff.mp hpos).2
  have hbij : Function.Bijective g :=
    (Nat.bijective_iff_injective_and_card g).mpr ⟨hginj, by rw [hcard1, hcard2]⟩
  refine ⟨LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap N g) hbij, ?_⟩
  -- and the witness satisfies the coordinatewise pinning BY CONSTRUCTION.
  intro P X Y hns hPXY
  have hPtor : (N : ℤ) • P.val = 0 := htor P
  have hQtor : (N : ℤ) • (WeierstrassCurve.Affine.Point.some X Y hns :
      (D.V.map Fr.emb).toAffine.Point) = 0 := by
    rw [← hPXY]
    exact (map_zsmul Fr.modelEquiv (N : ℤ) P.val).symm.trans
      ((congrArg (⇑Fr.modelEquiv) hPtor).trans (map_zero Fr.modelEquiv))
  have hX : X ∈ 𝒪 := habs hns hQtor
  have hY : Y ∈ 𝒪 := hord hns hQtor
  refine ⟨hX, hY, ((D.redCurve.map
    (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      hΔ).mp (hred.equation_res hX hY hns.1), ?_⟩
  show (g P).val = _
  refine (hgval P).trans ((hfapply P.val).trans ?_)
  rw [hPXY]
  exact hred.redFun_some_of_mem hΔ hns hX hY

/-- **A FROBENIUS LIFT ACTS THROUGH THE REDUCTION MAP AS THE `q`-POWER FROBENIUS**
(**PROVEN 2026-07-28**; opened the same day by cutting `exists_torsionFrame`
below into three — this is the SMALL half of that cut).

WHAT IT SAYS: if `ψ₀` is THE reduction map in the coordinatewise sense above, and
`σ` fixes `emb K` pointwise, lies in the decomposition group of `𝒪` and induces
`x ↦ x^q` on `κ(𝒪)`, then `ψ₀ ∘ ρ(σ) = F ∘ ψ₀`.

WHY IT IS TRUE, AND WHY IT IS SMALL. Everything is a computation on coordinates
once the pinning `hψ₀` is available:

* `σ` fixes `emb K` pointwise, hence fixes the four coefficients of
  `D.C.map Fr.emb`, hence COMMUTES with `modelEquiv`. HOW THE PROOF BELOW DOES
  IT, and this differs from the route this docstring originally proposed: rather
  than installing `Fr.emb.toAlgebra` to make `σ` a `D.K`-algebra map and citing
  `Affine.Point.equivVariableChangeBaseChange_galois`, it reads the commutation
  off `LocalFrame.modelEquiv.symm` IN COORDINATES. `modelEquiv.symm` is
  `equivVariableChange` composed with an `equivOfEq`, so on `some X Y` it is
  literally `(u²X + r, u³Y + u²sX + t)` with `u, r, s, t` the components of
  `D.C.map Fr.emb` — each of them `Fr.emb` of an element of `D.K`, hence fixed
  by `σ` by `hσK`. Applying `σ` to that formula and cancelling `u²`/`u³` (a unit)
  identifies the model coordinates of `ρ(σ) P` as `(σX, σY)`. This avoids the
  non-canonical `Algebra D.K ℚ̄` instance and the `IsScalarTower` plumbing the
  shim route would need; the shim lemma is never cited;
* so if the model point of `P` is `(X, Y)`, that of `ρ(σ) P` is `(σX, σY)`;
* `IsLocalRing.ResidueField.residue_smul` turns `residue 𝒪 (σ • z)` into
  `⟨σ, hdecS⟩ • residue 𝒪 z`, and `hσres` turns that into `(residue 𝒪 z) ^ q`;
* `Fr.resIso` is a ring equivalence, so it carries `q`-th powers to `q`-th
  powers;
* `WeilPairing.frobeniusTorsionEnd` is by definition the restriction of
  `Affine.Point.map (WeilPairing.frobAlgHom q)`, and `frobAlgHom q` is
  `x ↦ x ^ q`.

NO ARITHMETIC IS CONSUMED HERE beyond what `hψ₀` already carries, and that is
what makes the leaf faithful: a cut handing `ψ₀` over constrained ONLY by
`ψ₀ ρ(σ) ψ₀⁻¹ = F` would be false — see the atomicity audit below.

THE CHECK THAT WOULD REFUTE THIS LEAF: a torsion point whose model coordinates
are integral but whose `σ`-image has a non-integral coordinate. Impossible: `σ`
lies in the decomposition group of `𝒪`, so it preserves `𝒪` setwise.

NOTE ON `hqN`: the proof does not use it. `q ≠ N` is what
`exists_isTorsionReduction` needs to PRODUCE `ψ₀`; once `ψ₀` arrives with its
coordinatewise pinning, the equivariance is a pure computation. The hypothesis is
kept so the two halves of the cut have parallel signatures and the consumer
`exists_torsionFrame` can pass its own `hqN` positionally. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.frobenius_of_isTorsionReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] {hq : q.Prime} (hqN : q ≠ N)
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N))
    (hψ₀ : Fr.IsTorsionReduction ψ₀)
    (σ : Field.absoluteGaloisGroup ℚ)
    (hdecS : σ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hσK : ∀ x : D.K, σ (Fr.emb x) = Fr.emb x)
    (hσres : ∀ z : GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat,
      (⟨σ, hdecS⟩ : (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) •
        IsLocalRing.residue _ z = (IsLocalRing.residue _ z) ^ q) :
    ∀ x, ψ₀ (E.galoisRep N hN.pos σ x) =
      WeilPairing.frobeniusTorsionEnd q D.redCurve N (ψ₀ x) := by
  classical
  -- The Galois action on `N`-torsion, in coordinates.
  have hgalS : ∀ (y : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N)
      (a b : AlgebraicClosure ℚ)
      (h : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular a b),
      y.val = WeierstrassCurve.Affine.Point.some a b h →
      ∃ h', (E.galoisRep N hN.pos σ y).val
        = WeierstrassCurve.Affine.Point.some (σ a) (σ b) h' := by
    intro y a b h hy
    exact ⟨_, by
      show WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
        (AlgEquiv.toAlgHom σ) y.val = _
      rw [hy]
      rfl⟩
  -- The `q`-power Frobenius on the reduced curve's `N`-torsion, in coordinates.
  have hfrobS : ∀ (w : (D.redCurve.map
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)
      (a b : AlgebraicClosure (ZMod q))
      (h : (D.redCurve.map
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).toAffine.Nonsingular a b),
      w.val = WeierstrassCurve.Affine.Point.some a b h →
      ∃ h', (WeilPairing.frobeniusTorsionEnd q D.redCurve N w).val
        = WeierstrassCurve.Affine.Point.some (a ^ q) (b ^ q) h' := by
    intro w a b h hw
    exact ⟨_, by
      show WeierstrassCurve.Affine.Point.map (W' := D.redCurve) (S := ZMod q)
        (WeilPairing.frobAlgHom q) w.val = _
      rw [hw]
      rfl⟩
  -- `equivOfEq` inverts to `equivOfEq`.
  have hEq : ∀ {V₁ V₂ : WeierstrassCurve (AlgebraicClosure ℚ)} (h : V₁ = V₂),
      (WeierstrassCurve.Affine.Point.equivOfEq h).symm
        = WeierstrassCurve.Affine.Point.equivOfEq h.symm := by
    intro V₁ V₂ h
    subst h
    rfl
  -- `modelEquiv.symm`, in coordinates.
  have hcoord : ∀ (X Y : AlgebraicClosure ℚ)
      (hns : (D.V.map Fr.emb).toAffine.Nonsingular X Y),
      ∃ h', Fr.modelEquiv.symm (WeierstrassCurve.Affine.Point.some X Y hns)
        = WeierstrassCurve.Affine.Point.some
            (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X + (D.C.map Fr.emb).r)
            (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y
              + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X
              + (D.C.map Fr.emb).t) h' := by
    intro X Y hns
    exact ⟨_, by
      show WeierstrassCurve.Affine.Point.equivVariableChange
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (D.C.map Fr.emb)
          ((WeierstrassCurve.Affine.Point.equivOfEq Fr.model_eq.symm).symm
            (WeierstrassCurve.Affine.Point.some X Y hns)) = _
      rw [hEq, WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.equivVariableChange_some]⟩
  -- `σ` fixes the coefficients of the frame's variable change.
  have hσu : σ ((D.C.map Fr.emb).u : AlgebraicClosure ℚ)
      = ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) := hσK _
  have hσr : σ (D.C.map Fr.emb).r = (D.C.map Fr.emb).r := hσK _
  have hσs : σ (D.C.map Fr.emb).s = (D.C.map Fr.emb).s := hσK _
  have hσt : σ (D.C.map Fr.emb).t = (D.C.map Fr.emb).t := hσK _
  have hune : ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ≠ 0 := (D.C.map Fr.emb).u.ne_zero
  -- Residues of `σ`-images are `q`-th powers.
  have hres : ∀ (z : AlgebraicClosure ℚ)
      (hz : z ∈ GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (hz' : σ z ∈ GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat),
      Fr.resIso (IsLocalRing.residue _ (⟨σ z, hz'⟩ :
          GaloisRepresentation.globalValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat))
        = (Fr.resIso (IsLocalRing.residue _ (⟨z, hz⟩ :
            GaloisRepresentation.globalValuationSubring
              hq.toHeightOneSpectrumRingOfIntegersRat))) ^ q := by
    intro z hz hz'
    have h1 : (⟨σ z, hz'⟩ : GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat)
        = (⟨σ, hdecS⟩ : (GaloisRepresentation.globalValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) •
          (⟨z, hz⟩ : GaloisRepresentation.globalValuationSubring
            hq.toHeightOneSpectrumRingOfIntegersRat) := Subtype.ext rfl
    rw [h1, IsLocalRing.ResidueField.residue_smul, hσres, map_pow]
  intro x
  rcases hQ : Fr.modelEquiv x.val with _ | ⟨X, Y, hns⟩
  · -- the point is the origin
    have hxv : x.val = 0 :=
      Fr.modelEquiv.injective (by rw [hQ]; exact (map_zero Fr.modelEquiv).symm)
    have hx0 : x = 0 := Subtype.ext hxv
    have hgz : E.galoisRep N hN.pos σ x = 0 := by rw [hx0]; exact map_zero _
    have hψz : ψ₀ x = 0 := by rw [hx0]; exact map_zero _
    calc ψ₀ (E.galoisRep N hN.pos σ x) = ψ₀ 0 := congrArg (fun z => ψ₀ z) hgz
      _ = 0 := map_zero ψ₀
      _ = WeilPairing.frobeniusTorsionEnd q D.redCurve N 0 :=
          (map_zero (WeilPairing.frobeniusTorsionEnd q D.redCurve N)).symm
      _ = WeilPairing.frobeniusTorsionEnd q D.redCurve N (ψ₀ x) :=
          congrArg (fun z => WeilPairing.frobeniusTorsionEnd q D.redCurve N z) hψz.symm
  · obtain ⟨hX, hY, hns', hval⟩ := hψ₀ x X Y hns hQ
    rcases hQ' : Fr.modelEquiv (E.galoisRep N hN.pos σ x).val with _ | ⟨X', Y', hns2⟩
    · exfalso
      have h1 : (E.galoisRep N hN.pos σ x).val = 0 :=
        Fr.modelEquiv.injective (by rw [hQ']; exact (map_zero Fr.modelEquiv).symm)
      have h1' : WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
          (AlgEquiv.toAlgHom σ) x.val = 0 := h1
      have h2 : x.val = 0 := by
        refine WeierstrassCurve.Affine.Point.map_injective (W' := E) (S := ℚ)
          (AlgEquiv.toAlgHom σ) ?_
        rw [h1']
        exact (WeierstrassCurve.Affine.Point.map_zero _).symm
      have hz : (WeierstrassCurve.Affine.Point.some X Y hns :
          (D.V.map Fr.emb).toAffine.Point) = 0 := by
        rw [← hQ, h2]
        exact map_zero Fr.modelEquiv
      first
        | exact WeierstrassCurve.Affine.Point.noConfusion hz
        | simp at hz
    · -- identify `X'`, `Y'` with the `σ`-images of `X`, `Y`
      obtain ⟨hc1, hcoord1⟩ := hcoord X Y hns
      obtain ⟨hc2, hcoord2⟩ := hcoord X' Y' hns2
      have hx : x.val
          = WeierstrassCurve.Affine.Point.some
              (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X + (D.C.map Fr.emb).r)
              (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y
                + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X
                + (D.C.map Fr.emb).t) hc1 := by
        rw [← hcoord1, ← hQ, Fr.modelEquiv.symm_apply_apply]
      have hxσ2 : (E.galoisRep N hN.pos σ x).val
          = WeierstrassCurve.Affine.Point.some
              (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X' + (D.C.map Fr.emb).r)
              (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y'
                + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X'
                + (D.C.map Fr.emb).t) hc2 := by
        rw [← hcoord2, ← hQ', Fr.modelEquiv.symm_apply_apply]
      obtain ⟨hh, hxσ1⟩ := hgalS x _ _ hc1 hx
      have hcomb := hxσ1.symm.trans hxσ2
      have hXX : X' = σ X := by
        have e1 : σ (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X + (D.C.map Fr.emb).r)
            = ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X' + (D.C.map Fr.emb).r := by
          injection hcomb with e1 e2
          try exact e1
        simp only [map_add, map_mul, map_pow, hσu, hσr] at e1
        exact (mul_left_cancel₀ (pow_ne_zero 2 hune) (add_right_cancel e1)).symm
      have hYY : Y' = σ Y := by
        have e2 : σ (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y
              + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X
              + (D.C.map Fr.emb).t)
            = ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y'
              + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X'
              + (D.C.map Fr.emb).t := by
          injection hcomb with e1 e2
          try exact e2
        simp only [map_add, map_mul, map_pow, hσu, hσs, hσt, hXX] at e2
        exact (mul_left_cancel₀ (pow_ne_zero 3 hune)
          (add_right_cancel (add_right_cancel e2))).symm
      subst hXX
      subst hYY
      obtain ⟨hX2, hY2, hns3, hval2⟩ :=
        hψ₀ (E.galoisRep N hN.pos σ x) (σ X) (σ Y) hns2 hQ'
      obtain ⟨hh2, hfr⟩ := hfrobS (ψ₀ x) _ _ hns' hval
      refine Subtype.ext ?_
      rw [hval2, hfr]
      exact WeierstrassCurve.Affine.Point.some_eq_some _ (hres X hX hX2) (hres Y hY hY2)

/-- **A CHANGE OF VARIABLES BETWEEN TWO INTEGRAL WEIERSTRASS MODELS WITH UNIT
DISCRIMINANT HAS INTEGRAL ENTRIES** (PROVEN 2026-07-28, while proving
`exists_aut_of_isTorsionReduction` below; this is the one genuinely
valuation-theoretic step of the Serre–Tate route recorded on that leaf).

Silverman *AEC* VII.1.3(b) for a valuation subring `𝒪` of an arbitrary field
`F`, stated with `𝒪.valuation` so that "coefficient in `𝒪`" reads
`valuation ≤ 1` and "unit discriminant" reads `valuation = 1`.

WHY `2` MUST BE A UNIT, AND WHY `3` NEED NOT BE. The `a₁`-relation
`u · (C • W).a₁ = W.a₁ + 2s` is the only source of information about `s`, so
`2 ∈ 𝒪ˣ` is genuinely used (and is exactly the hypothesis `q ≠ 2` at the
call site). It is tempting to read `r` off the `a₂`-relation
`u² · (C • W).a₂ = W.a₂ - s·W.a₁ + 3r - s²` the same way, but that would need
`3 ∈ 𝒪ˣ` and the consumers of this file explicitly need `q = 3`. The
`a₆`-relation supplies `r` with no such cost: `r³` is the unique term of
strictly largest valuation there once `v r > 1`, since the `a₃`-relation
already forces `v t ≤ max 1 (v r)`, so every other term has valuation at most
`(v r)²` while `v (r³) = (v r)³`. -/
theorem WeierstrassCurve.variableChange_valuation_of_valuation_Δ_eq_one
    {F : Type*} [Field F] (𝒪 : ValuationSubring F)
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (h2 : 𝒪.valuation (2 : F) = 1)
    (ha₁ : 𝒪.valuation W.a₁ ≤ 1) (ha₂ : 𝒪.valuation W.a₂ ≤ 1)
    (ha₃ : 𝒪.valuation W.a₃ ≤ 1) (ha₄ : 𝒪.valuation W.a₄ ≤ 1)
    (ha₆ : 𝒪.valuation W.a₆ ≤ 1)
    (hc₁ : 𝒪.valuation (C • W).a₁ ≤ 1)
    (hc₃ : 𝒪.valuation (C • W).a₃ ≤ 1)
    (hc₆ : 𝒪.valuation (C • W).a₆ ≤ 1)
    (hΔ : 𝒪.valuation W.Δ = 1) (hΔ' : 𝒪.valuation (C • W).Δ = 1) :
    𝒪.valuation (C.u : F) = 1 ∧ 𝒪.valuation C.r ≤ 1 ∧ 𝒪.valuation C.s ≤ 1 ∧
      𝒪.valuation C.t ≤ 1 := by
  have cancel : ∀ {a b c : 𝒪.ValueGroup}, a ≠ 0 → a * b ≤ a * c → b ≤ c := by
    intro a b c ha h
    calc b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left₀ ha]
      _ ≤ a⁻¹ * (a * c) := mul_le_mul_left' h _
      _ = c := by rw [inv_mul_cancel_left₀ ha]
  set v := 𝒪.valuation with hv
  have hune : (C.u : F) ≠ 0 := C.u.ne_zero
  have hu0 : v (C.u : F) ≠ 0 := by
    simpa [hv] using (Valuation.ne_zero_iff v).mpr hune
  -- Step 1 : `v u = 1`, because `u¹²` is the ratio of two unit discriminants.
  have hu12 : v (C.u : F) ^ 12 = 1 := by
    have h := congrArg v (W.variableChange_Δ C)
    rw [Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀, hΔ, hΔ', mul_one] at h
    have h' : ((v (C.u : F))⁻¹) ^ 12 = 1 := h.symm
    rw [inv_pow] at h'
    exact inv_eq_one.mp h'
  have huval : v (C.u : F) = 1 := by
    rcases lt_trichotomy (v (C.u : F)) 1 with h | h | h
    · exfalso
      have hle : v (C.u : F) ^ 12 ≤ v (C.u : F) := by
        calc v (C.u : F) ^ 12 = v (C.u : F) ^ 11 * v (C.u : F) := pow_succ _ 11
          _ ≤ 1 * v (C.u : F) := mul_le_mul_right' (pow_le_one' h.le 11) _
          _ = v (C.u : F) := one_mul _
      rw [hu12] at hle
      exact absurd (hle.trans_lt h) (lt_irrefl 1)
    · exact h
    · exfalso
      have hle : v (C.u : F) ≤ v (C.u : F) ^ 12 := by
        calc v (C.u : F) = 1 * v (C.u : F) := (one_mul _).symm
          _ ≤ v (C.u : F) ^ 11 * v (C.u : F) :=
              mul_le_mul_right' (one_le_pow_of_one_le' h.le 11) _
          _ = v (C.u : F) ^ 12 := (pow_succ _ 11).symm
      rw [hu12] at hle
      exact absurd (h.trans_le hle) (lt_irrefl 1)
  -- Step 2 : `v s ≤ 1`, from the `a₁`-relation and `2 ∈ 𝒪ˣ`.
  have hs : v C.s ≤ 1 := by
    have h := W.variableChange_a₁ C
    rw [Units.val_inv_eq_inv_val] at h
    have key : (2 : F) * C.s = (C.u : F) * (C • W).a₁ - W.a₁ := by
      rw [h]; field_simp; ring
    have hb : v ((2 : F) * C.s) ≤ 1 := by
      rw [key]
      refine Valuation.map_sub_le v ?_ ha₁
      rw [map_mul, huval, one_mul]; exact hc₁
    rw [map_mul, h2, one_mul] at hb
    exact hb
  -- Step 3 : `v t ≤ max 1 (v r)`, from the `a₃`-relation.
  have key3 : (2 : F) * C.t = (C.u : F) ^ 3 * (C • W).a₃ - W.a₃ - C.r * W.a₁ := by
    have h := W.variableChange_a₃ C
    rw [Units.val_inv_eq_inv_val] at h
    rw [h]; field_simp; ring
  have ht_le : v C.t ≤ max 1 (v C.r) := by
    have hb : v ((2 : F) * C.t) ≤ max 1 (v C.r) := by
      rw [key3]
      refine Valuation.map_sub_le v (Valuation.map_sub_le v ?_ ?_) ?_
      · rw [map_mul, map_pow, huval, one_pow, one_mul]
        exact hc₃.trans (le_max_left _ _)
      · exact ha₃.trans (le_max_left _ _)
      · rw [map_mul]
        calc v C.r * v W.a₁ ≤ v C.r * 1 := mul_le_mul_left' ha₁ _
          _ = v C.r := mul_one _
          _ ≤ max 1 (v C.r) := le_max_right _ _
    rw [map_mul, h2, one_mul] at hb
    exact hb
  -- Step 4 : `v r ≤ 1`, because `r³` would dominate the `a₆`-relation.
  have hr : v C.r ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hr0 : v C.r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hcon)
    have htr : v C.t ≤ v C.r := ht_le.trans (max_le hcon.le le_rfl)
    have h1r2 : (1 : 𝒪.ValueGroup) ≤ v C.r ^ 2 := one_le_pow_of_one_le' hcon.le 2
    have hrr2 : v C.r ≤ v C.r ^ 2 := by
      calc v C.r = 1 * v C.r := (one_mul _).symm
        _ ≤ v C.r * v C.r := mul_le_mul_right' hcon.le _
        _ = v C.r ^ 2 := (pow_two _).symm
    have key6 : C.r ^ 3 = (C.u : F) ^ 6 * (C • W).a₆ - W.a₆ - C.r * W.a₄ - C.r ^ 2 * W.a₂
        + C.t * W.a₃ + C.t ^ 2 + C.r * C.t * W.a₁ := by
      have h := W.variableChange_a₆ C
      rw [Units.val_inv_eq_inv_val] at h
      rw [h]; field_simp; ring
    have hb : v (C.r ^ 3) ≤ v C.r ^ 2 := by
      rw [key6]
      refine Valuation.map_add_le v (Valuation.map_add_le v (Valuation.map_add_le v
        (Valuation.map_sub_le v (Valuation.map_sub_le v (Valuation.map_sub_le v ?_ ?_) ?_) ?_)
        ?_) ?_) ?_
      · rw [map_mul, map_pow, huval, one_pow, one_mul]; exact hc₆.trans h1r2
      · exact ha₆.trans h1r2
      · rw [map_mul]
        exact ((mul_le_mul_left' ha₄ _).trans_eq (mul_one _)).trans hrr2
      · rw [map_mul, map_pow]
        exact (mul_le_mul_left' ha₂ _).trans_eq (mul_one _)
      · rw [map_mul]
        exact ((mul_le_mul_left' ha₃ _).trans_eq (mul_one _)).trans (htr.trans hrr2)
      · rw [map_pow]
        exact pow_le_pow_left' htr 2
      · rw [map_mul, map_mul]
        calc v C.r * v C.t * v W.a₁ ≤ v C.r * v C.t * 1 := mul_le_mul_left' ha₁ _
          _ = v C.r * v C.t := mul_one _
          _ ≤ v C.r * v C.r := mul_le_mul_left' htr _
          _ = v C.r ^ 2 := (pow_two _).symm
    rw [map_pow] at hb
    have hlast : v C.r ^ 2 * v C.r ≤ v C.r ^ 2 * 1 := by
      rw [mul_one]
      calc v C.r ^ 2 * v C.r = v C.r ^ 3 := (pow_succ _ 2).symm
        _ ≤ v C.r ^ 2 := hb
    exact absurd (hcon.trans_le (cancel (pow_ne_zero 2 hr0) hlast)) (lt_irrefl 1)
  exact ⟨huval, hr, hs, ht_le.trans (max_le le_rfl hr)⟩

/-- **The good model of `D`, placed inside `ℚ̄` by an ARBITRARY `ℚ`-embedding**
(PROVEN 2026-07-28, while proving `exists_aut_of_isTorsionReduction` below).

This is `LocalFrame.model_eq` with the frame's own embedding replaced by any
`ℚ`-embedding `φ : K ↪ ℚ̄`; the proof is verbatim the same, and the generality is
exactly what is needed for the `τ`-CONJUGATE embedding `τ ∘ emb`, which is not a
frame's embedding — it need not satisfy `comap_eq`, and does not have to. -/
theorem WeierstrassCurve.PotentiallyGoodModel.map_eq_variableChange_smul
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {q : ℕ} [Fact q.Prime]
    (D : E.PotentiallyGoodModel q) (φ : D.K →+* AlgebraicClosure ℚ)
    (hφ : ∀ x : ℚ, φ (algebraMap ℚ D.K x) = algebraMap ℚ (AlgebraicClosure ℚ) x) :
    D.V.map φ = (D.C.map φ) • (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
  have hcomp : φ.comp (algebraMap ℚ D.K) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    RingHom.ext hφ
  rw [D.V_eq, ← WeierstrassCurve.map_variableChange]
  congr 1
  show (E.map (algebraMap ℚ D.K)).map φ = _
  rw [WeierstrassCurve.map_map, hcomp]

/-- **The frame's model identification, read backwards on affine points**
(PROVEN 2026-07-28, while proving `exists_aut_of_isTorsionReduction` below).

`Fr.modelEquiv` transports `E`-points to `V`-points along `D.C`; its INVERSE is
the forward change of variables `(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` for
`C₁ := D.C.map Fr.emb`, namely `Affine.Point.equivVariableChange` composed with
the transport along `model_eq`. Stating the INVERSE rather than the forward map
is deliberate: it is the direction whose coordinates come straight out of
`equivVariableChange_some` with no inversion, and both uses below go through it
— the forward values get pinned by applying `modelEquiv.symm` to an affine point
that is already known. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.modelEquiv_symm_some
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {q : ℕ} [Fact q.Prime] {hq : q.Prime}
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    {X Y : AlgebraicClosure ℚ}
    (hns : (D.V.map Fr.emb).toAffine.Nonsingular X Y) :
    ∃ h : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular
        (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X + (D.C.map Fr.emb).r)
        (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y
          + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X
          + (D.C.map Fr.emb).t),
      Fr.modelEquiv.symm (WeierstrassCurve.Affine.Point.some X Y hns)
        = WeierstrassCurve.Affine.Point.some _ _ h := by
  have hsymm : ∀ {V V' : WeierstrassCurve (AlgebraicClosure ℚ)} (h : V = V')
      (P : V'.toAffine.Point),
      (WeierstrassCurve.Affine.Point.equivOfEq h).symm P
        = WeierstrassCurve.Affine.Point.equivOfEq h.symm P := by
    intro V V' h P; subst h; rfl
  have key : Fr.modelEquiv.symm (WeierstrassCurve.Affine.Point.some X Y hns)
      = WeierstrassCurve.Affine.Point.equivVariableChange
          (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (D.C.map Fr.emb)
          (WeierstrassCurve.Affine.Point.equivOfEq Fr.model_eq
            (WeierstrassCurve.Affine.Point.some X Y hns)) := by
    rw [WeierstrassCurve.PotentiallyGoodModel.LocalFrame.modelEquiv,
      AddEquiv.symm_trans_apply, AddEquiv.symm_symm, hsymm]
  rw [key, WeierstrassCurve.Affine.Point.equivOfEq_some,
    WeierstrassCurve.Affine.Point.equivVariableChange_some]
  exact ⟨_, rfl⟩

/-- **`autTorsionEnd` in coordinates** (PROVEN 2026-07-28, while proving
`exists_aut_of_isTorsionReduction` below): the endomorphism of the `N`-torsion
induced by an automorphism `C` of `W` sends an affine point to the point with
the `C`-transformed coordinates. Taking the affine presentation of the SOURCE as
a hypothesis, rather than case-splitting inside, is what makes the statement
usable: it forces the `Point.some` to be elaborated at the curve
`W ⊗ (algebraMap F F)` that `equivOfEq hC.symm` acts on, which is the same curve
as `W` only up to defeq — and a `rw` cannot see through that. -/
theorem WeierstrassCurve.autTorsionEnd_val_some {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (C : WeierstrassCurve.VariableChange F)
    (hC : C • (W.map (algebraMap F F)) = W.map (algebraMap F F)) (N : ℕ)
    (y : W.nTorsion N) {x₀ y₀ : F}
    (hns : (W.map (algebraMap F F)).toAffine.Nonsingular x₀ y₀)
    (hy : y.val = WeierstrassCurve.Affine.Point.some x₀ y₀ hns) :
    ∃ h', (WeierstrassCurve.autTorsionEnd W C hC N y).val
      = WeierstrassCurve.Affine.Point.some ((C.u : F) ^ 2 * x₀ + C.r)
          ((C.u : F) ^ 3 * y₀ + (C.u : F) ^ 2 * C.s * x₀ + C.t) h' := by
  have hunf : (WeierstrassCurve.autTorsionEnd W C hC N y).val
      = WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) C
          (WeierstrassCurve.Affine.Point.equivOfEq hC.symm y.val) := rfl
  rw [hunf, hy, WeierstrassCurve.Affine.Point.equivOfEq_some,
    WeierstrassCurve.Affine.Point.equivVariableChange_some]
  exact ⟨_, rfl⟩

open scoped Pointwise in
/-- **THE INERTIA VARIABLE CHANGE, AND ITS REDUCTION — the Serre–Tate step**
(PROVEN 2026-07-28 over `variableChange_valuation_of_valuation_Δ_eq_one`).

`τ` need not fix `K`, so it does not commute with `modelEquiv`; the FAILURE to
commute is the automorphism. Concretely: `τ` carries the placed variable change
`C₁ := D.C.map Fr.emb` to its conjugate `C₁ᵗᵃᵘ`, and `Dτ := C₁ᵗᵃᵘ · C₁⁻¹` is a
change of variables between the two integral models `V ⊗ emb` and
`V ⊗ (τ ∘ emb)` of the SAME curve, both with unit discriminant. Hence its
entries are integral (`variableChange_valuation_of_valuation_Δ_eq_one`), so it
reduces to a change of variables `C` over `κ(𝒪) ≅ 𝔽̄_q`; and because `τ` lies in
INERTIA it fixes `κ(𝒪)` pointwise, so the two models reduce to the same `Ẽ` and
`C` is an automorphism of it. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.exists_inertiaVariableChange
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {q : ℕ} [Fact q.Prime] {hq : q.Prime}
    (hq2 : q ≠ 2) {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    (τ : Field.absoluteGaloisGroup ℚ)
    (hdecT : τ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hτin : (⟨τ, hdecT⟩ : (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) ∈
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup ℚ) :
    ∃ (Dτ : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ))
      (hu : ((Dτ.u : AlgebraicClosure ℚ)) ∈ GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)
      (hr : Dτ.r ∈ GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)
      (hs : Dτ.s ∈ GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)
      (ht : Dτ.t ∈ GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat)
      (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (_hC : C • ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
      Dτ * (D.C.map Fr.emb)
          = (D.C.map Fr.emb).map (AlgEquiv.toRingEquiv
              (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toRingHom ∧
        (C.u : AlgebraicClosure (ZMod q))
            = Fr.resIso (IsLocalRing.residue _ ⟨(Dτ.u : AlgebraicClosure ℚ), hu⟩) ∧
        C.r = Fr.resIso (IsLocalRing.residue _ ⟨Dτ.r, hr⟩) ∧
        C.s = Fr.resIso (IsLocalRing.residue _ ⟨Dτ.s, hs⟩) ∧
        C.t = Fr.resIso (IsLocalRing.residue _ ⟨Dτ.t, ht⟩) := by
  classical
  set Ob := GaloisRepresentation.globalValuationSubring
    hq.toHeightOneSpectrumRingOfIntegersRat with hObdef
  set τR : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ :=
    (AlgEquiv.toRingEquiv (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toRingHom with hτRdef
  set ρτ : Ob →+* Ob := MulSemiringAction.toRingHom (Ob.decompositionSubgroup ℚ) Ob
    ⟨τ, hdecT⟩ with hρτdef
  have hρτcoe : ∀ z : Ob, ((ρτ z : Ob) : AlgebraicClosure ℚ) = τ (z : AlgebraicClosure ℚ) :=
    fun _ => rfl
  have hτmem : ∀ (z : AlgebraicClosure ℚ), z ∈ Ob → τ z ∈ Ob := fun z hz => (ρτ ⟨z, hz⟩).2
  have hτres : ∀ z : Ob, IsLocalRing.residue Ob (ρτ z) = IsLocalRing.residue Ob z := by
    intro z
    have h1 := MonoidHom.mem_ker.mp hτin
    rw [show ρτ z = (⟨τ, hdecT⟩ : Ob.decompositionSubgroup ℚ) • z from rfl,
      IsLocalRing.ResidueField.residue_smul]
    calc (⟨τ, hdecT⟩ : Ob.decompositionSubgroup ℚ) • IsLocalRing.residue Ob z
        = (MulSemiringAction.toRingAut (Ob.decompositionSubgroup ℚ)
            (IsLocalRing.ResidueField Ob) ⟨τ, hdecT⟩) (IsLocalRing.residue Ob z) := rfl
      _ = IsLocalRing.residue Ob z := by rw [h1]; rfl
  -- the residue homomorphism `𝒪 → 𝔽̄_q`
  set φ : Ob →+* AlgebraicClosure (ZMod q) :=
    (Fr.resIso : IsLocalRing.ResidueField Ob ≃+* AlgebraicClosure (ZMod q)).toRingHom.comp
      (IsLocalRing.residue Ob) with hφdef
  have hφapp : ∀ z : Ob, φ z = Fr.resIso (IsLocalRing.residue Ob z) := fun _ => rfl
  have hφρτ : φ.comp ρτ = φ := RingHom.ext fun z => by
    rw [RingHom.comp_apply, hφapp, hφapp, hτres]
  -- `R → 𝒪`
  have hRO : ∀ z : D.R, Fr.emb (algebraMap D.R D.K z) ∈ Ob := by
    intro z
    have hmem : algebraMap D.R D.K z ∈ (algebraMap D.R D.K).range := ⟨z, rfl⟩
    rw [← Fr.comap_eq] at hmem
    exact hmem
  have hROunit : ∀ z : D.R, IsUnit z →
      IsUnit (⟨Fr.emb (algebraMap D.R D.K z), hRO z⟩ : Ob) := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    refine isUnit_iff_exists_inv.mpr ⟨⟨Fr.emb (algebraMap D.R D.K w), hRO w⟩, Subtype.ext ?_⟩
    show Fr.emb (algebraMap D.R D.K z) * Fr.emb (algebraMap D.R D.K w) = 1
    rw [← map_mul, ← map_mul, hw, map_one, map_one]
  -- the integral model of `V` over `R`, and integrality of its coefficients in `𝒪`
  have ha₁ : Fr.emb D.V.a₁ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_a₁_eq D.R D.V]; exact hRO _
  have ha₂ : Fr.emb D.V.a₂ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_a₂_eq D.R D.V]; exact hRO _
  have ha₃ : Fr.emb D.V.a₃ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_a₃_eq D.R D.V]; exact hRO _
  have ha₄ : Fr.emb D.V.a₄ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_a₄_eq D.R D.V]; exact hRO _
  have ha₆ : Fr.emb D.V.a₆ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_a₆_eq D.R D.V]; exact hRO _
  -- the discriminant of the integral model is a unit of `R`
  have hΔRunit : IsUnit (WeierstrassCurve.integralModel D.R D.V).Δ := by
    have hell : (D.V.reduction D.R).IsElliptic :=
      (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction D.R).mp D.V_good
    have h2 : IsUnit (IsLocalRing.residue D.R (WeierstrassCurve.integralModel D.R D.V).Δ) := by
      have h3 := hell.isUnit
      rwa [WeierstrassCurve.reduction, WeierstrassCurve.map_Δ] at h3
    refine IsLocalRing.notMem_maximalIdeal.mp fun hcon => ?_
    rw [← IsLocalRing.residue_eq_zero_iff] at hcon
    rw [hcon] at h2
    exact not_isUnit_zero h2
  have hΔmem : Fr.emb D.V.Δ ∈ Ob := by
    rw [← WeierstrassCurve.integralModel_Δ_eq D.R D.V]; exact hRO _
  have hΔunit : IsUnit (⟨Fr.emb D.V.Δ, hΔmem⟩ : Ob) := by
    have h := hROunit _ hΔRunit
    convert h using 2
    exact congrArg Fr.emb (WeierstrassCurve.integralModel_Δ_eq D.R D.V).symm
  -- `2` is a unit of `𝒪`, because `q ≠ 2`
  have h2Runit : IsUnit (2 : D.R) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hcon => ?_
    rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat] at hcon
    have hz : (2 : ZMod q) = 0 := by
      have := congrArg D.resEquiv hcon
      rwa [map_ofNat, map_zero] at this
    have hz' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast hz
    exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp hz'))
  have h2mem : (2 : AlgebraicClosure ℚ) ∈ Ob := by
    have h := hRO (2 : D.R)
    rwa [map_ofNat, map_ofNat] at h
  have h2unit : IsUnit (⟨(2 : AlgebraicClosure ℚ), h2mem⟩ : Ob) := by
    have h := hROunit (2 : D.R) h2Runit
    convert h using 2
    rw [map_ofNat, map_ofNat]
  have hval_le : ∀ (z : AlgebraicClosure ℚ), z ∈ Ob → Ob.valuation z ≤ 1 :=
    fun z hz => (ValuationSubring.valuation_le_one_iff Ob z).mpr hz
  have h2val : Ob.valuation (2 : AlgebraicClosure ℚ) = 1 :=
    (ValuationSubring.valuation_eq_one_iff Ob ⟨(2 : AlgebraicClosure ℚ), h2mem⟩).mp h2unit
  have hΔval : Ob.valuation (Fr.emb D.V.Δ) = 1 :=
    (ValuationSubring.valuation_eq_one_iff Ob ⟨Fr.emb D.V.Δ, hΔmem⟩).mp hΔunit
  -- the `τ`-conjugate embedding, and the second integral model
  set embT : D.K →+* AlgebraicClosure ℚ := τR.comp Fr.emb with hembTdef
  have hembT : ∀ z : D.K, embT z = τ (Fr.emb z) := fun _ => rfl
  have hm2 : D.V.map embT = (D.C.map embT) • (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    D.map_eq_variableChange_smul embT (fun x => by
      show τ (Fr.emb (algebraMap ℚ D.K x)) = _
      rw [Fr.emb_comm]
      exact (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).commutes x)
  set Dτ : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ) :=
    (D.C.map embT) * (D.C.map Fr.emb)⁻¹ with hDτdef
  have hpin : Dτ * (D.C.map Fr.emb) = D.C.map embT := by
    rw [hDτdef, inv_mul_cancel_right]
  have hpin' : Dτ * (D.C.map Fr.emb) = (D.C.map Fr.emb).map τR := by
    rw [hpin, hembTdef, ← WeierstrassCurve.VariableChange.map_map]
  have hsmul : Dτ • (D.V.map Fr.emb) = D.V.map embT := by
    rw [Fr.model_eq, hm2, ← mul_smul, hpin]
  -- the change of variables between the two integral models has integral entries
  obtain ⟨huval, hrval, hsval, htval⟩ :=
    WeierstrassCurve.variableChange_valuation_of_valuation_Δ_eq_one Ob (D.V.map Fr.emb) Dτ h2val
      (hval_le _ ha₁) (hval_le _ ha₂) (hval_le _ ha₃) (hval_le _ ha₄) (hval_le _ ha₆)
      (by rw [hsmul]; exact hval_le _ (hτmem _ ha₁))
      (by rw [hsmul]; exact hval_le _ (hτmem _ ha₃))
      (by rw [hsmul]; exact hval_le _ (hτmem _ ha₆))
      (by rw [WeierstrassCurve.map_Δ]; exact hΔval)
      (by
        rw [hsmul, WeierstrassCurve.map_Δ]
        show Ob.valuation (τ (Fr.emb D.V.Δ)) = 1
        exact (ValuationSubring.valuation_eq_one_iff Ob (ρτ ⟨Fr.emb D.V.Δ, hΔmem⟩)).mp
          (hΔunit.map (MulSemiringAction.toRingAut (Ob.decompositionSubgroup ℚ) Ob ⟨τ, hdecT⟩)))
  have humem : (Dτ.u : AlgebraicClosure ℚ) ∈ Ob :=
    (ValuationSubring.valuation_le_one_iff Ob _).mp huval.le
  have hrmem : Dτ.r ∈ Ob := (ValuationSubring.valuation_le_one_iff Ob _).mp hrval
  have hsmem : Dτ.s ∈ Ob := (ValuationSubring.valuation_le_one_iff Ob _).mp hsval
  have htmem : Dτ.t ∈ Ob := (ValuationSubring.valuation_le_one_iff Ob _).mp htval
  have huUnit : IsUnit (⟨(Dτ.u : AlgebraicClosure ℚ), humem⟩ : Ob) :=
    (ValuationSubring.valuation_eq_one_iff Ob _).mpr huval
  -- descend the whole picture to `𝒪`, then reduce it
  set Ŵ : WeierstrassCurve Ob :=
    ⟨⟨Fr.emb D.V.a₁, ha₁⟩, ⟨Fr.emb D.V.a₂, ha₂⟩, ⟨Fr.emb D.V.a₃, ha₃⟩,
      ⟨Fr.emb D.V.a₄, ha₄⟩, ⟨Fr.emb D.V.a₆, ha₆⟩⟩ with hŴdef
  set Ĉ : WeierstrassCurve.VariableChange Ob :=
    ⟨huUnit.unit, ⟨Dτ.r, hrmem⟩, ⟨Dτ.s, hsmem⟩, ⟨Dτ.t, htmem⟩⟩ with hĈdef
  have hŴmap : Ŵ.map Ob.subtype = D.V.map Fr.emb := by ext <;> rfl
  have hŴτmap : (Ŵ.map ρτ).map Ob.subtype = D.V.map embT := by ext <;> rfl
  have hĈmap : Ĉ.map Ob.subtype = Dτ := by
    have hu' : ((Ĉ.map Ob.subtype).u : AlgebraicClosure ℚ) = (Dτ.u : AlgebraicClosure ℚ) := by
      show ((huUnit.unit : Ob) : AlgebraicClosure ℚ) = (Dτ.u : AlgebraicClosure ℚ)
      rw [IsUnit.unit_spec]
    exact WeierstrassCurve.VariableChange.ext (Units.ext hu') rfl rfl rfl
  have hkey : Ĉ • Ŵ = Ŵ.map ρτ := by
    refine WeierstrassCurve.map_injective (f := Ob.subtype) Ob.subtype_injective ?_
    show (Ĉ • Ŵ).map Ob.subtype = (Ŵ.map ρτ).map Ob.subtype
    rw [← WeierstrassCurve.map_variableChange, hĈmap, hŴmap, hsmul, hŴτmap]
  have hred : (Ĉ.map φ) • (Ŵ.map φ) = Ŵ.map φ := by
    rw [WeierstrassCurve.map_variableChange, hkey, WeierstrassCurve.map_map, hφρτ]
  -- the reduction of `Ŵ` is `Ẽ ⊗ 𝔽̄_q`
  have hcoef : ∀ (z : D.R) (h : Fr.emb (algebraMap D.R D.K z) ∈ Ob),
      φ ⟨Fr.emb (algebraMap D.R D.K z), h⟩
        = algebraMap (ZMod q) (AlgebraicClosure (ZMod q))
            (D.resEquiv (IsLocalRing.residue D.R z)) :=
    fun z h => Fr.resIso_comm z h
  have hŴφ : Ŵ.map φ = D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · have hsub : (⟨Fr.emb D.V.a₁, ha₁⟩ : Ob)
          = ⟨Fr.emb (algebraMap D.R D.K (WeierstrassCurve.integralModel D.R D.V).a₁), hRO _⟩ :=
        Subtype.ext (congrArg Fr.emb (WeierstrassCurve.integralModel_a₁_eq D.R D.V).symm)
      exact (congrArg φ hsub).trans (hcoef _ _)
    · have hsub : (⟨Fr.emb D.V.a₂, ha₂⟩ : Ob)
          = ⟨Fr.emb (algebraMap D.R D.K (WeierstrassCurve.integralModel D.R D.V).a₂), hRO _⟩ :=
        Subtype.ext (congrArg Fr.emb (WeierstrassCurve.integralModel_a₂_eq D.R D.V).symm)
      exact (congrArg φ hsub).trans (hcoef _ _)
    · have hsub : (⟨Fr.emb D.V.a₃, ha₃⟩ : Ob)
          = ⟨Fr.emb (algebraMap D.R D.K (WeierstrassCurve.integralModel D.R D.V).a₃), hRO _⟩ :=
        Subtype.ext (congrArg Fr.emb (WeierstrassCurve.integralModel_a₃_eq D.R D.V).symm)
      exact (congrArg φ hsub).trans (hcoef _ _)
    · have hsub : (⟨Fr.emb D.V.a₄, ha₄⟩ : Ob)
          = ⟨Fr.emb (algebraMap D.R D.K (WeierstrassCurve.integralModel D.R D.V).a₄), hRO _⟩ :=
        Subtype.ext (congrArg Fr.emb (WeierstrassCurve.integralModel_a₄_eq D.R D.V).symm)
      exact (congrArg φ hsub).trans (hcoef _ _)
    · have hsub : (⟨Fr.emb D.V.a₆, ha₆⟩ : Ob)
          = ⟨Fr.emb (algebraMap D.R D.K (WeierstrassCurve.integralModel D.R D.V).a₆), hRO _⟩ :=
        Subtype.ext (congrArg Fr.emb (WeierstrassCurve.integralModel_a₆_eq D.R D.V).symm)
      exact (congrArg φ hsub).trans (hcoef _ _)
  have hmapid : ∀ W : WeierstrassCurve (AlgebraicClosure (ZMod q)),
      W.map (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))) = W := by
    intro W; rw [Algebra.algebraMap_self]; exact W.map_id
  refine ⟨Dτ, humem, hrmem, hsmem, htmem, Ĉ.map φ, ?_, hpin', ?_, rfl, rfl, rfl⟩
  · rw [hmapid, ← hŴφ]; exact hred
  · show φ (huUnit.unit : Ob) = _
    rw [IsUnit.unit_spec]
    rfl

open scoped Pointwise in
/-- **INERTIA ACTS THROUGH THE REDUCTION MAP AS AN AUTOMORPHISM OF THE REDUCED
CURVE — SERRE–TATE** (**PROVEN 2026-07-28** by the elementary
`Dτ := Cᵗᵃᵘ · C⁻¹` route recorded on this leaf when it was opened; opened
2026-07-28 by cutting `exists_torsionFrame` below into three, as the place where
the remaining mathematics of that leaf sat).

WHAT IT SAYS: if `ψ₀` is THE reduction map in the coordinatewise sense above and
`τ` lies in the inertia subgroup at `𝒪`, then `ψ₀ ρ(τ) ψ₀⁻¹` is
`autTorsionEnd` of an automorphism `C` of `Ẽ` over `𝔽̄_q`, presented as the
variable change it is.

WHY `τ` IS DIFFERENT FROM `σ`, and it is the whole difficulty: `τ` need NOT fix
`K`. Inertia over `ℚ` moves `K` whenever `K/ℚ` is ramified at `q` — and it must,
since `E` has potentially good but in general NOT good reduction, so `ρ` is
genuinely ramified at `q`. Hence `τ` does not commute with `modelEquiv`, and the
FAILURE to commute is precisely the automorphism.

THE PROOF, which is the elementary route and needs no Néron models. `τ` carries
the placed variable change `C₁ := D.C.map Fr.emb` to its conjugate `C₁ᵗᵃᵘ`, and
`Dτ := C₁ᵗᵃᵘ · C₁⁻¹` is a change of variables between the two integral models
`V ⊗ emb` and `V ⊗ (τ ∘ emb)` of the same curve, both with unit discriminant;
`exists_inertiaVariableChange` above shows its entries are integral and produces
the reduction `C`. The point-level half is then bookkeeping in coordinates:
`modelEquiv_symm_some` says the model coordinates `(X, Y)` of `P` satisfy
`P = (u²X + r, u³Y + u²sX + t)` for `C₁ = (u, r, s, t)`, `ρ(τ)` applies `τ` to
both, and the pinning `Dτ · C₁ = C₁ᵗᵃᵘ` turns that into
`(X, Y) ↦ (Dτ.u² τX + Dτ.r, …)`; reducing mod `𝔪_𝒪` and using that `τ` fixes
`κ(𝒪)` pointwise gives exactly `autTorsionEnd C`.

WHERE EACH HYPOTHESIS IS USED. `hτin` (inertia, not merely decomposition) is
used twice and both uses are essential: it makes the two models reduce to the
SAME `Ẽ`, and it is what erases `τ` from the residue coordinates. `hq2`
(`q ≠ 2`) is used exactly once, inside
`variableChange_valuation_of_valuation_Δ_eq_one`, to solve the `a₁`-relation for
`Dτ.s`; note `q = 3` is NOT excluded and must not be, since the consumers of
this file need it. `hqN` is not used here at all — it belongs to
`exists_isTorsionReduction`, which is where the torsion arithmetic lives — and
is kept only because the statement is quantified uniformly with its siblings.

AVAILABLE AND NOT REBUILT: `Affine.Point.equivVariableChange`,
`equivVariableChangeBaseChange` and `equivVariableChangeBaseChange_galois`, in
the project shim
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`; and
`WeierstrassCurve.autTorsionEnd` above, which is already built on them. Note
`equivVariableChangeBaseChange_galois` itself could NOT be cited: it assumes the
variable change is defined over the base field and `σ` is a `K`-automorphism,
which is exactly the hypothesis that fails for inertia here. Serre–Tate itself
remains ABSENT from all three trees (`Fermat/`, `.lake/packages/mathlib/`,
`~/cs/FLT/`); it was not needed.

THE CHECK THAT WOULD REFUTE THIS LEAF: an inertia element at `𝒪` whose action on
`E[N](ℚ̄)`, transported by `ψ₀`, is induced by no variable change of `Ẽ` over
`𝔽̄_q`. By the route above that would need `Dτ` to have a non-unit entry, i.e.
one of the two models to be non-minimal, which `D.V_good` excludes.

THE GLOBAL/CHEBOTAREV AXIS IS A DEAD END for this statement; the reason is
structural rather than technical and is recorded in full on
`exists_torsionFrame` below.

**`hq2 : q ≠ 2` IS LOAD-BEARING FOR THE ROUTE ABOVE, AND ONLY FOR IT** (audited
2026-07-29 while closing the `2`-adic leaf under `B₀²ᵃ` far below; the audit was
begun in order to DELETE this hypothesis and concluded the opposite, so it is
recorded here rather than repeated).

* The STATEMENT is true at `q = 2`. Serre–Tate embeds the semistability defect
  into `Aut(Ẽ)` in every residue characteristic — that embedding is exactly what
  Kraus's `q = 2` classification presupposes when it names `Q₈` and `SL₂(𝔽₃)`. So
  a `q = 2` version of this leaf is a promise that can be kept, and the separate
  leaf `exists_aut_of_isTorsionReduction_two` below states it.
* The ROUTE above nevertheless inverts `2`, at exactly one step and unavoidably
  in that form: "both models have unit discriminant, hence `Dτ` has unit entries"
  is `variableChange_valuation_of_valuation_Δ_eq_one`, whose hypothesis
  `h2 : 𝒪.valuation (2 : F) = 1` says `2 ∈ 𝒪ˣ`. It is genuinely used — the
  `aᵢ`-transformation formulas give `2s = u a₁' - a₁` and `2t = u³a₃' - a₃ - r a₁`,
  so integrality of `s` and `t` is read off only after dividing by `2`. At `q = 2`
  that division loses `v(2) > 0` and the argument does not merely get harder, it
  stops.
* So the honest split is: this leaf keeps `hq2` and keeps its elementary proof;
  `q = 2` is a SEPARATE leaf with a genuinely different integrality argument
  (minimal models are unique up to integral change of variables in every residue
  characteristic — Silverman *AEC* VII.1.3(b) — but at `2` that needs the smooth
  model, or a `v`-case analysis, rather than the division above).

WHAT IS *NOT* THE `q = 2` DIFFICULTY, since three docstrings in this cluster said
it was: the CLASSIFICATION of the group generated by the resulting automorphisms.
That is a statement about the SIZE of `Aut`, it is consumed downstream by
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq` (proven over ANY
field), and this leaf never asks for it — it produces ONE automorphism per
inertia element and says nothing about how many there are. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.exists_aut_of_isTorsionReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] {hq : q.Prime} (hq2 : q ≠ 2) (hqN : q ≠ N)
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N))
    (hψ₀ : Fr.IsTorsionReduction ψ₀)
    (τ : Field.absoluteGaloisGroup ℚ)
    (hdecT : τ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hτin : (⟨τ, hdecT⟩ : (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) ∈
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup ℚ) :
    ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
      ∀ x, ψ₀ (E.galoisRep N hN.pos τ x) =
        WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ x) := by
  classical
  obtain ⟨Dτ, hu, hr, hs, ht, C, hC, hpin, hCu, hCr, hCs, hCt⟩ :=
    Fr.exists_inertiaVariableChange hq2 τ hdecT hτin
  refine ⟨C, hC, fun P => ?_⟩
  set Ob := GaloisRepresentation.globalValuationSubring
    hq.toHeightOneSpectrumRingOfIntegersRat with hObdef
  have hu0 : ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ≠ 0 := (D.C.map Fr.emb).u.ne_zero
  -- `τ` preserves `𝒪` and acts trivially on its residue field (it lies in inertia)
  have hτmem : ∀ (z : AlgebraicClosure ℚ), z ∈ Ob → τ z ∈ Ob := fun z hz =>
    ((⟨τ, hdecT⟩ : Ob.decompositionSubgroup ℚ) • (⟨z, hz⟩ : Ob)).2
  have hτres : ∀ z : Ob,
      IsLocalRing.residue Ob ((⟨τ, hdecT⟩ : Ob.decompositionSubgroup ℚ) • z)
        = IsLocalRing.residue Ob z := by
    intro z
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := MonoidHom.mem_ker.mp hτin
    calc (⟨τ, hdecT⟩ : Ob.decompositionSubgroup ℚ) • IsLocalRing.residue Ob z
        = (MulSemiringAction.toRingAut (Ob.decompositionSubgroup ℚ)
            (IsLocalRing.ResidueField Ob) ⟨τ, hdecT⟩) (IsLocalRing.residue Ob z) := rfl
      _ = IsLocalRing.residue Ob z := by rw [h1]; rfl
  have hφτ : ∀ (z : AlgebraicClosure ℚ) (hz : z ∈ Ob),
      Fr.resIso (IsLocalRing.residue Ob ⟨τ z, hτmem z hz⟩)
        = Fr.resIso (IsLocalRing.residue Ob ⟨z, hz⟩) :=
    fun z hz => congrArg Fr.resIso (hτres ⟨z, hz⟩)
  -- the pinning `Dτ * C₁ = C₁ᵗᵃᵘ`, entry by entry
  have hpu : (Dτ.u : AlgebraicClosure ℚ) * ((D.C.map Fr.emb).u : AlgebraicClosure ℚ)
      = τ ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) := by
    have h := congrArg (fun c : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ) =>
      (c.u : AlgebraicClosure ℚ)) hpin
    simpa [WeierstrassCurve.VariableChange.mul_def] using h
  have hpr : Dτ.r * ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 + (D.C.map Fr.emb).r
      = τ (D.C.map Fr.emb).r := by
    have h := congrArg (fun c : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ) => c.r) hpin
    simpa [WeierstrassCurve.VariableChange.mul_def] using h
  have hps : ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) * Dτ.s + (D.C.map Fr.emb).s
      = τ (D.C.map Fr.emb).s := by
    have h := congrArg (fun c : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ) => c.s) hpin
    simpa [WeierstrassCurve.VariableChange.mul_def] using h
  have hpt : Dτ.t * ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3
      + Dτ.r * (D.C.map Fr.emb).s * ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2
      + (D.C.map Fr.emb).t = τ (D.C.map Fr.emb).t := by
    have h := congrArg (fun c : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ) => c.t) hpin
    simpa [WeierstrassCurve.VariableChange.mul_def] using h
  by_cases hP0 : P = 0
  · subst hP0
    have h0 : ψ₀ (E.galoisRep N hN.pos τ 0) = 0 := by
      rw [map_zero]
      exact map_zero ψ₀
    have h1 : ψ₀ 0 = 0 := map_zero ψ₀
    rw [h0]
    exact (map_zero (WeierstrassCurve.autTorsionEnd
      (D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) C hC N)).symm.trans
      (congrArg _ h1.symm)
  -- `P` is affine; let `(X, Y)` be its model coordinates
  have hPv : P.val ≠ 0 :=
    fun h => hP0 (Subtype.ext h)
  obtain ⟨X, Y, hns, hPeq⟩ : ∃ X Y hns,
      Fr.modelEquiv P.val
        = WeierstrassCurve.Affine.Point.some X Y hns := by
    rcases hh : Fr.modelEquiv P.val
      with _ | ⟨X, Y, hns⟩
    · refine absurd ?_ hPv
      have h2 := congrArg Fr.modelEquiv.symm hh
      rw [Fr.modelEquiv.symm_apply_apply] at h2
      rw [h2, show (WeierstrassCurve.Affine.Point.zero :
        (D.V.map Fr.emb).toAffine.Point) = 0 from rfl, map_zero]
      rfl
    · exact ⟨X, Y, hns, rfl⟩
  obtain ⟨hX, hY, hns', hψP⟩ := hψ₀ P X Y hns hPeq
  obtain ⟨hxy, hPval⟩ := Fr.modelEquiv_symm_some hns
  have hPvalEq : P.val = WeierstrassCurve.Affine.Point.some _ _ hxy := by
    rw [← hPval, ← hPeq, Fr.modelEquiv.symm_apply_apply]
  -- the image of `P` under `ρ(τ)`: apply `τ` to both coordinates
  obtain ⟨hτxy, hQvalEq⟩ : ∃ h,
      (E.galoisRep N hN.pos τ P).val
        = WeierstrassCurve.Affine.Point.some
            (τ (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * X + (D.C.map Fr.emb).r))
            (τ (((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 3 * Y
              + ((D.C.map Fr.emb).u : AlgebraicClosure ℚ) ^ 2 * (D.C.map Fr.emb).s * X
              + (D.C.map Fr.emb).t)) h := by
    have h1 : (E.galoisRep N hN.pos τ P).val
        = WeierstrassCurve.Affine.Point.map (W' := E) (S := ℚ)
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
            P.val := rfl
    rw [h1, hPvalEq]
    exact ⟨_, rfl⟩
  have hQv : (E.galoisRep N hN.pos τ P).val ≠ 0 := by
    rw [hQvalEq]; exact fun hcon => by cases hcon
  obtain ⟨X₂, Y₂, hns₂, hQeq⟩ : ∃ X₂ Y₂ hns₂,
      Fr.modelEquiv (E.galoisRep N hN.pos τ P).val
        = WeierstrassCurve.Affine.Point.some X₂ Y₂ hns₂ := by
    rcases hh : Fr.modelEquiv (E.galoisRep N hN.pos τ P).val with _ | ⟨X₂, Y₂, hns₂⟩
    · refine absurd ?_ hQv
      have h2 := congrArg Fr.modelEquiv.symm hh
      rw [Fr.modelEquiv.symm_apply_apply] at h2
      rw [h2, show (WeierstrassCurve.Affine.Point.zero :
        (D.V.map Fr.emb).toAffine.Point) = 0 from rfl, map_zero]
      rfl
    · exact ⟨X₂, Y₂, hns₂, rfl⟩
  obtain ⟨hX₂, hY₂, hns₂', hψQ⟩ := hψ₀ (E.galoisRep N hN.pos τ P) X₂ Y₂ hns₂ hQeq
  obtain ⟨hxy₂, hQval2⟩ := Fr.modelEquiv_symm_some hns₂
  have hQcoord : (E.galoisRep N hN.pos τ P).val
      = WeierstrassCurve.Affine.Point.some _ _ hxy₂ := by
    rw [← hQval2, ← hQeq, Fr.modelEquiv.symm_apply_apply]
  have hinj := hQvalEq.symm.trans hQcoord
  injection hinj with hx2 hy2
  -- transport the two coordinate equations across the pinning
  have hXX : X₂ = (Dτ.u : AlgebraicClosure ℚ) ^ 2 * τ X + Dτ.r := by
    rw [map_add, map_mul, map_pow, ← hpu, ← hpr] at hx2
    refine mul_left_cancel₀ (pow_ne_zero 2 hu0) ?_
    linear_combination -hx2
  have hYY : Y₂ = (Dτ.u : AlgebraicClosure ℚ) ^ 3 * τ Y
      + (Dτ.u : AlgebraicClosure ℚ) ^ 2 * Dτ.s * τ X + Dτ.t := by
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow,
      ← hpu, ← hps, ← hpt, hXX] at hy2
    refine mul_left_cancel₀ (pow_ne_zero 3 hu0) ?_
    linear_combination -hy2
  -- reduce the two coordinate equations modulo the maximal ideal of `𝒪`
  have hresX : Fr.resIso (IsLocalRing.residue Ob ⟨X₂, hX₂⟩)
      = (C.u : AlgebraicClosure (ZMod q)) ^ 2
          * Fr.resIso (IsLocalRing.residue Ob ⟨X, hX⟩) + C.r := by
    have hsub : (⟨X₂, hX₂⟩ : Ob)
        = (⟨(Dτ.u : AlgebraicClosure ℚ), hu⟩ : Ob) ^ 2 * ⟨τ X, hτmem X hX⟩ + ⟨Dτ.r, hr⟩ :=
      Subtype.ext (by push_cast; exact hXX)
    rw [hsub]
    simp only [map_add, map_mul, map_pow]
    rw [hCu, hCr, hφτ]
  have hresY : Fr.resIso (IsLocalRing.residue Ob ⟨Y₂, hY₂⟩)
      = (C.u : AlgebraicClosure (ZMod q)) ^ 3
          * Fr.resIso (IsLocalRing.residue Ob ⟨Y, hY⟩)
        + (C.u : AlgebraicClosure (ZMod q)) ^ 2 * C.s
          * Fr.resIso (IsLocalRing.residue Ob ⟨X, hX⟩) + C.t := by
    have hsub : (⟨Y₂, hY₂⟩ : Ob)
        = (⟨(Dτ.u : AlgebraicClosure ℚ), hu⟩ : Ob) ^ 3 * ⟨τ Y, hτmem Y hY⟩
          + (⟨(Dτ.u : AlgebraicClosure ℚ), hu⟩ : Ob) ^ 2 * ⟨Dτ.s, hs⟩ * ⟨τ X, hτmem X hX⟩
          + ⟨Dτ.t, ht⟩ :=
      Subtype.ext (by push_cast; exact hYY)
    rw [hsub]
    simp only [map_add, map_mul, map_pow]
    rw [hCu, hCs, hCt, hφτ, hφτ]
  -- assemble
  refine Subtype.ext ?_
  rw [hψQ]
  obtain ⟨hhR, hRHS⟩ : ∃ h,
      (WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ P)).val
        = WeierstrassCurve.Affine.Point.some
            ((C.u : AlgebraicClosure (ZMod q)) ^ 2
              * Fr.resIso (IsLocalRing.residue Ob ⟨X, hX⟩) + C.r)
            ((C.u : AlgebraicClosure (ZMod q)) ^ 3
                * Fr.resIso (IsLocalRing.residue Ob ⟨Y, hY⟩)
              + (C.u : AlgebraicClosure (ZMod q)) ^ 2 * C.s
                * Fr.resIso (IsLocalRing.residue Ob ⟨X, hX⟩) + C.t) h := by
    exact WeierstrassCurve.autTorsionEnd_val_some _ C hC N (ψ₀ P) hns' hψP
  rw [hRHS]
  exact WeierstrassCurve.Affine.Point.some_eq_some _ hresX hresY

/-- **SERRE–TATE AT THE WILD PRIME `2`** (sorry leaf, opened 2026-07-29): the
statement of `exists_aut_of_isTorsionReduction` immediately above, with
`hq2 : q ≠ 2` replaced by `hq2 : q = 2`.  Together the two are uniform in `q`, and
that is the whole point of the pair: **this is the ONLY place where the residue
characteristic `2` costs the `B₀` cluster anything.**

WHERE THIS LEAF CAME FROM, and it is a relocation of an existing leaf rather than
a new obligation.  `WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg_two`
(`B₀²ᵃ⁻²`, opened 2026-07-28, ~500 lines below) restated the whole of `B₀²ᵃ` at
`q = 2` — a Galois-character transport with a good-model construction, a frame, a
torsion reduction and an eighty-line descent to `(λ τ)ⁿ = 1` inside it, ALL of
which are already uniform in `q`.  Its docstring named three obstructions; two of
them were false or overtaken (audited 2026-07-29, in the section note at that
leaf's old position), and the third is this one.  So that leaf has been replaced
by this one and `B₀²ᵃ` now case-splits in three lines onto the pair.  The
frontier count is unchanged and the leaf is ~1/6 the size.

WHAT THE `2`-ADIC DIFFICULTY ACTUALLY IS.  The odd proof establishes that
`Dτ := C₁ᵗᵃᵘ · C₁⁻¹` — the failure of `τ` to commute with the model
identification — has entries in `𝒪`, from the fact that both models have unit
discriminant.  In the form the tree has it
(`WeierstrassCurve.variableChange_valuation_of_valuation_Δ_eq_one`) that step
carries `h2 : 𝒪.valuation (2 : F) = 1`, i.e. `2 ∈ 𝒪ˣ`, and it is genuinely used:
the transformation formulas give `2s = u a₁' - a₁` and
`2t = u³ a₃' - a₃ - r a₁`, so integrality of `s` and `t` is read off only after
dividing by `2`.  At `q = 2` that division is not available.

THE STATEMENT IS STILL TRUE, and this is the promise the `sorry` makes.  Two
Weierstrass models over a valuation ring, both integral with unit discriminant
and isomorphic over the fraction field, are related by an INTEGRAL change of
variables in every residue characteristic — Silverman *AEC* VII.1.3(b) has no
hypothesis on the residue characteristic, and Serre–Tate's embedding of the
semistability defect into `Aut(Ẽ)` is exactly what Kraus's `q = 2` classification
(`Q₈`, `SL₂(𝔽₃)`) presupposes when it lists the possible defects at `2`.  What
fails at `2` is one PROOF of that fact, not the fact.

TWO ROUTES, and the second is the one to try first.

1. *Smooth model.*  A Weierstrass model with unit discriminant is smooth and
   proper over `𝒪`, hence is the Néron model of its generic fibre; an isomorphism
   of generic fibres carrying `O` to `O` extends by the Néron mapping property.
   Characteristic-free, but it needs Néron models, which this file has so far
   avoided on purpose.
2. *Valuation case analysis, no division.*  Argue by contradiction from
   `v(r) < 0`, `v(s) < 0` or `v(t) < 0` directly against the integrality of the
   `aᵢ'`, using the transformation formulas
   `u²a₂' = a₂ - s a₁ + 3r - s²`,
   `u⁴a₄' = a₄ - s a₃ + 2r a₂ - (t + rs) a₁ + 3r² - 2st`,
   `u⁶a₆' = a₆ + r a₄ + r² a₂ + r³ - t a₃ - t² - r t a₁`,
   in which the dominant terms `s²`, `r³` and `t²` carry no factor of `2`.  This
   is the same shape as the `v C.r ^ 3 ≤ v C.r ^ 2` contradiction that
   `variableChange_valuation_of_valuation_Δ_eq_one` already runs for `r`; what is
   new at `2` is only the `s` and `t` cases, which the odd proof gets for free
   from `a₁` and `a₃`.

COORDINATE WITH `exists_aut_of_isTorsionReduction` ABOVE: the two leaves share
every hypothesis but `hq2`, and a `v`-case analysis proved for route 2 would
subsume the odd proof as well.  Whoever closes this should check whether the two
can be merged back into one uniform statement — that is the ideal end state, and
it is deliberately NOT assumed here, because the odd leaf is proven and a
speculative merge would put a working proof at risk.

WHAT THIS LEAF DOES **NOT** CONTAIN: any classification of the defect.  Kraus's
list is consumed downstream by
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`
(`Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`), proven over ANY field.
This leaf produces ONE automorphism per inertia element and says nothing about
how many there are; three docstrings in this cluster used to name the
classification as the `q = 2` difficulty, and all three were wrong.

THE CHECK THAT WOULD REFUTE THIS LEAF: an inertia element at `𝒪` over `q = 2`
whose action on `E[N](ℚ̄)`, transported by `ψ₀`, is induced by no variable change
of `Ẽ` over `𝔽̄_2`.  That would need two integral models of one curve, both with
unit discriminant, related by a NON-integral change of variables — which would
contradict uniqueness of minimal models over `𝒪`. -/
theorem WeierstrassCurve.PotentiallyGoodModel.LocalFrame.exists_aut_of_isTorsionReduction_two
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] {hq : q.Prime} (hq2 : q = 2) (hqN : q ≠ N)
    {D : E.PotentiallyGoodModel q} (Fr : D.LocalFrame hq)
    (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
      ((D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N))
    (hψ₀ : Fr.IsTorsionReduction ψ₀)
    (τ : Field.absoluteGaloisGroup ℚ)
    (hdecT : τ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hτin : (⟨τ, hdecT⟩ : (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) ∈
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup ℚ) :
    ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
      ∀ x, ψ₀ (E.galoisRep N hN.pos τ x) =
        WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ x) :=
  sorry

/-- **THE ATOM: the reduction map on `N`-torsion, and its two equivariances**
(opened 2026-07-27 by cutting `exists_reductionFrame_of_potentiallyGoodModel`
below into three; **PROVEN 2026-07-28** over the three leaves immediately above,
by the COORDINATEWISE cut that this docstring's own atomicity audit named as the
recommended one).

THE PROOF HERE is three lines and no mathematics: `exists_isTorsionReduction`
produces `ψ₀` together with its coordinatewise pinning
`Fr.IsTorsionReduction ψ₀`, and the two equivariances are then
`frobenius_of_isTorsionReduction` and `exists_aut_of_isTorsionReduction` applied
to THAT `ψ₀`. Nothing receives `ψ₀` as free data — it is produced once and both
leaves are handed it with its pinning — which is exactly what the audit below
demands. **A prover should read those three docstrings, not this one**: the
`N = 2` obligation and the Néron–Ogg–Šafarevič machinery survey now live on
`exists_isTorsionReduction`, and the Serre–Tate route on
`exists_aut_of_isTorsionReduction`. What remains here is the audit itself and
the Chebotarev dead-end note, both of which are about the CUT rather than about
any one leaf.

WHAT IT SAYS. Given the placement `Fr` of `K` inside `ℚ̄`, a Frobenius lift `σ`
— in the decomposition group of the pinned subring `𝒪`, fixing `emb K`
pointwise, inducing `x ↦ x^q` on `κ(𝒪)` — and an inertia element `τ` at `𝒪`,
there is a `ZMod N`-linear identification `ψ₀ : E[N](ℚ̄) ≃ Ẽ[N](𝔽̄_q)` with
`Ẽ := D.redCurve` through which `σ` acts as the `q`-power Frobenius of `Ẽ` and
`τ` acts as an automorphism of `Ẽ_{𝔽̄_q}`.

`ℚ_q` DOES NOT APPEAR. The statement is entirely about the good model, the
valuation subring `𝒪` of `ℚ̄`, and `Γ ℚ`. That separation is the point of the
cut: `exists_frobeniusLift` above carries all of the local-field theory and
this leaf carries all of the elliptic-curve theory.

ATOMICITY AUDIT — WHY `ψ₀` IS PRODUCED HERE RATHER THAN HANDED OVER, AND WHY
EVERY CUT THAT HANDS IT OVER IS **FALSE**. (Written 2026-07-27 for the parent
leaf; it applies verbatim here, and it is what forces the two conclusions to
share ONE `ψ₀`.) The axis searched was *cuts that hand `Wbar₀`, `ψ₀` or the
Frobenius lift over as data* — as free hypotheses, or equivalently as fields of
a shared structure, since bundling free data changes nothing. Say the cut is
"leaf 1 produces `Wbar₀, ψ₀, σK` with `ψ₀ ρ(σK) ψ₀⁻¹ = F`; leaf 2 turns that
into the automorphism". Leaf 2 then quantifies over ALL data satisfying that
intertwining, and:

* *Free `Wbar₀` is fatal.* Only the mod-`N` Frobenius of `Wbar₀` is
  constrained, so `Wbar₀` may be replaced by any elliptic curve over `𝔽_q` with
  the same trace mod `N`. Choose the true reduction to have `j = 0` (so
  `Aut = μ₆` and the automorphism `C` has order `3`) and the substitute to have
  `j ∉ {0, 1728}` (so `Aut = {±1}` and `autTorsionEnd` lands in `{±id}`). The
  conclusion then demands an order-`3` element of `{±id}`.
* *Free `ψ₀` is fatal even with `Wbar₀` pinned.* Two solutions of the
  intertwining differ by `β` in the CENTRALIZER of `F`, and
  `ψ₀ ρ(τ) ψ₀⁻¹ ∈ image (autTorsionEnd ·)` is not invariant under conjugating
  by that centraliser: at `q ≡ 1 mod N` the Frobenius is a scalar, its
  centraliser is all of `GL₂(ZMod N)`, and the image of `Aut(Ẽ)` is a cyclic
  subgroup of order `3`, `4` or `6` whose `GL₂`-conjugates are different
  subgroups.
* *Free `σK` is fatal even with `Wbar₀` and `ψ₀` pinned.* The hypothesis
  `ψ₀ ρ(σK) ψ₀⁻¹ = F` does not force `σK` to be a Frobenius LIFT — whenever the
  image of `ρ` is large there are many elements with that image — and then
  `Frob_q · σK⁻¹` need not lie in inertia at all.

HOW THE PRESENT CUT DODGES ALL THREE, which is the check any FURTHER proposal
must also pass. `Wbar₀` is pinned to `D.redCurve`. `ψ₀` is not handed over: this
leaf CONSTRUCTS it and states both equivariances about the same one. And `σ` is
not constrained by a representation-level identity but by VALUATION-THEORETIC
ones (`hdecS`, `hσK`, `hσres`), which do force it to be a genuine Frobenius lift
inside the decomposition group of `K` — strictly stronger than
`ψ₀ ρ(σK) ψ₀⁻¹ = F`, and that is what kills the third counterexample.

THE CHECK THAT WOULD REFUTE THE AUDIT, unchanged: a formulation whose
hypotheses pin `ψ₀` up to the image of `Aut(Ẽ)` — for instance a statement of
the reduction map by its coordinatewise definition — under which the split
becomes two independently true statements. Note that the frame makes such a
formulation WRITABLE for the first time: with `Fr.emb`, `Fr.comap_eq` and
`Fr.resIso` in hand one can say "`ψ₀` sends a torsion point whose coordinates
lie in `𝒪` to the point with the residue coordinates", and that IS a pinning up
to `Aut(Ẽ)`. Splitting this leaf along that line was the recommended next step;
it was not done at the 2026-07-27 cut because writing the coordinatewise
characterisation first requires transporting `E`-points to `V`-points along
`D.C`.

**THAT SPLIT WAS CARRIED OUT ON 2026-07-28 AND IS WHAT PROVES THIS LEAF.** The
transport is `LocalFrame.modelEquiv` (PROVEN, over `LocalFrame.model_eq`), the
characterisation is `LocalFrame.IsTorsionReduction`, and the three leaves are
`exists_isTorsionReduction`, `frobenius_of_isTorsionReduction` and
`exists_aut_of_isTorsionReduction` above. The split passes the audit for the
reason the audit itself predicted, and in fact more strongly than it predicted:
`IsTorsionReduction` pins `ψ₀` OUTRIGHT rather than up to `Aut(Ẽ)`, because the
transport is along the GIVEN `D.C` and the residue identification is the GIVEN
`Fr.resIso`. So the two consumers receive one and the same, uniquely determined,
`ψ₀`, and none of the three counterexamples above can be instantiated: `Wbar₀` is
`D.redCurve`, `ψ₀` is pinned pointwise, and `σ` is still constrained
valuation-theoretically rather than by any representation-level identity.

**THE `N = 2` OBLIGATION IS DISCHARGED (2026-07-28), AND THE NOTE THAT STOOD HERE
WAS WRONG ABOUT WHY IT EXISTED.** It said the obligation had moved onto
`exists_isTorsionReduction` above, as the only one of the three leaves consuming
oddness — through `torsion_abscissa_residue_ne` and
`torsion_ordinate_eq_of_residue_eq` — and that a prover must either supply their
`n = 2` case in `KnownIn1980s/EllipticCurves/GoodReduction.lean` or restate that
leaf with `Odd N` and push the restriction up the chain. When that leaf was
proven it used **neither lemma**: injectivity of reduction on prime-to-`q`
torsion goes through `IsReductionAlong.redFun_eq_zero_iff` (the kernel of
reduction is exactly the non-integral locus) together with
`torsion_abscissa_mem` (torsion abscissae are integral), and neither of those
consumes `Odd n`. So nothing has to be added to `GoodReduction.lean`, no
restriction has to be pushed up the chain, and `q ≠ 2` turned out to be unused as
well — so unused that on 2026-07-29 it was deleted from that leaf's signature
outright, once a consumer at `q = 2` appeared.  The `hq2` on
`exists_aut_of_isTorsionReduction` above is a different matter and was NOT
deleted: it is load-bearing for that leaf's elementary route, which divides by
`2`; see the audit there.  Both statements
are TRUE and PROVEN at every prime
`N ≠ q`, `N = 2` included. Recorded at length because the obsolete paragraph was
exactly the kind of "obligation is live" note that manufactures phantom
dispatches.

MACHINERY, GREPPED 2026-07-27 OVER ALL THREE TREES (`Fermat/`,
`.lake/packages/mathlib/`, `~/cs/FLT/`) — **the survey has been REDISTRIBUTED to
the leaves that consume it, and the copies there are the live ones**:

* the **Néron–Ogg–Šafarevič** half was on `exists_isTorsionReduction` above, which
  is now PROVEN — and the survey it carried named the WRONG assembly pattern, which
  is worth recording. It said to copy `WeilPairing.exists_frobenius_reduction_model`,
  a ~2800-line monolith. **The general, sorry-free API already existed**:
  `WeierstrassCurve.IsReductionAlong` and `redHom` in
  `KnownIn1980s/EllipticCurves/PointReduction.lean` do well-definedness, additivity
  and the kernel analysis once and for all, so only the reduction DATUM had to be
  assembled here. Of the `GoodReduction.lean` companions only
  `torsion_abscissa_mem` / `torsion_ordinate_mem` were used (taking
  `ksep := AlgebraicClosure ℚ` through `Fr.emb.toAlgebra` and `h𝒪 := Fr.comap_eq`
  verbatim, exactly as predicted); `torsion_unramified_of_good_reduction`,
  `torsion_abscissa_residue_ne` and `torsion_ordinate_eq_of_residue_eq` were not
  needed at all, and neither was the `RtoO` plumbing;
* the **Serre–Tate** half (Serre–Tate itself ABSENT from all three trees; the
  elementary `Dτ := Cᵗᵃᵘ · C⁻¹` route; the shim
  `Affine.Point.equivVariableChange` / `equivVariableChangeBaseChange_galois`
  and `WeierstrassCurve.autTorsionEnd`) is on
  `exists_aut_of_isTorsionReduction` above.

THE GLOBAL/CHEBOTAREV AXIS IS A DEAD END HERE, and the reason is structural
rather than technical — recorded so that nobody spends a cycle re-searching it
(the axis searched, 2026-07-27, was: imitate
`WeilPairing.det_galoisRep_eq_cyclotomic`, which pins the DETERMINANT at every
Frobenius globally and so avoids any integral model). `det ρ` is the cyclotomic
CHARACTER, hence unramified at `q ≠ N`, so its value at `σ_q` does not depend on
the choice of lift and a global identity of characters determines it. The trace
is not a character: at potentially-good-but-not-good reduction `ρ` is genuinely
RAMIFIED at `q`, and the trace really does change with the lift (`a ↦ ζ_e a` for
semistability defect `e`). A global argument cannot see inside a Frobenius
coset, so it cannot produce a lift-dependent value. The LOCAL axis is the only
one.

NOT VACUOUS: `ψ₀` is a linear EQUIVALENCE and the two conclusions are
conjugation identities, so together they pin `ρ(σ)` and `ρ(τ)` into
`Aut · F` and `Aut`; in particular they force `det ρ(σ) = q` via
`WeilPairing.det_frobeniusTorsionEnd`, which is independently PROVEN, so a junk
witness would have to reprove that. -/
theorem WeierstrassCurve.PotentiallyGoodModel.exists_torsionFrame
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (D : E.PotentiallyGoodModel q) (Fr : D.LocalFrame hq)
    (σ τ : Field.absoluteGaloisGroup ℚ)
    (hdecS : σ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hdecT : τ ∈ (GaloisRepresentation.globalValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ)
    (hτin : (⟨τ, hdecT⟩ : (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) ∈
      (GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup ℚ)
    (hσK : ∀ x : D.K, σ (Fr.emb x) = Fr.emb x)
    (hσres : ∀ z : GaloisRepresentation.globalValuationSubring
        hq.toHeightOneSpectrumRingOfIntegersRat,
      (⟨σ, hdecS⟩ : (GaloisRepresentation.globalValuationSubring
          hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup ℚ) •
        IsLocalRing.residue _ z = (IsLocalRing.residue _ z) ^ q) :
    ∃ (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
        ((D.redCurve.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N))
      (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
      (∀ x, ψ₀ (E.galoisRep N hN.pos σ x) =
        WeilPairing.frobeniusTorsionEnd q D.redCurve N (ψ₀ x)) ∧
      (∀ x, ψ₀ (E.galoisRep N hN.pos τ x) =
        WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ x)) := by
  obtain ⟨ψ₀, hψ₀⟩ := Fr.exists_isTorsionReduction hN hqN
  obtain ⟨C, hC, haut⟩ :=
    Fr.exists_aut_of_isTorsionReduction hN hq2 hqN ψ₀ hψ₀ τ hdecT hτin
  exact ⟨ψ₀, C, hC,
    Fr.frobenius_of_isTorsionReduction hN hqN ψ₀ hψ₀ σ hdecS hσK hσres, haut⟩

/-- **The reduction frame at `q`: Néron–Ogg–Shafarevich and Serre–Tate,
packaged against the PINNED reduction curve** (PROVEN 2026-07-27 over the three
leaves immediately above, by a cut along the LOCAL FRAME; opened as a single
sorry leaf earlier the same day by decomposing
`exists_frobeniusAut_of_potentiallyGoodModel` immediately below, which is PROVEN
over it).

WHAT IT SAYS. Write `Ẽ := D.redCurve` for the reduction of the good model.
There are

* a `ZMod N`-linear identification `ψ₀ : E[N](ℚ̄) ≃ Ẽ[N](𝔽̄_q)` — the reduction
  map on `N`-torsion;
* an element `ι` of `localInertiaGroup q`, with image `t` in `Γ ℚ`, such that
  `t⁻¹ · Frob_q` acts through `ψ₀` as the `q`-power Frobenius of `Ẽ`. This is
  Néron–Ogg–Shafarevich together with the fact that a Frobenius lift exists
  inside the decomposition group of `K` — which is exactly what RESIDUE DEGREE
  ONE buys, since the residue field of `R` is already `𝔽_q` and the
  decomposition group therefore still surjects onto `Gal(𝔽̄_q/𝔽_q)`;
* an automorphism `C` of `Ẽ_{𝔽̄_q}`, presented as the variable change it is,
  through which `ψ₀` intertwines the action of `t` itself. This is Serre–Tate.

The consumer is then one multiplication: `Frob_q = t · (t⁻¹ · Frob_q)`, and
`galoisRep` is a monoid homomorphism.

THE PROOF HERE is the three-leaf assembly opened 2026-07-27. All of the
mathematics lives in the leaves above and none of it lives here — the body is
three `obtain`s and an anonymous constructor:

* `nonempty_localFrame` places `K` inside `ℚ̄` so that the prime of `R` becomes
  the PINNED valuation subring `GaloisRepresentation.globalValuationSubring q`,
  and identifies its residue field with `𝔽̄_q`;
* `exists_frobeniusLift` produces the inertia element `ι` together with the
  valuation-theoretic facts about `t` and `σ := t⁻¹ Frob_q`. This is the whole
  of the local-field theory, and RESIDUE DEGREE ONE is consumed exactly here;
* `exists_torsionFrame` constructs `ψ₀` and proves both equivariances. This is
  the whole of the elliptic-curve theory, and it is where the ATOMICITY AUDIT,
  the `N = 2` obligation, the machinery survey and the Chebotarev dead-end note
  now live. **A prover should read THAT docstring, not this one.**

WHY THIS CUT IS SAFE, against the audit that shows every cut handing `Wbar₀`,
`ψ₀` or `σK` over as free data is FALSE (the audit stands; it is reproduced in
full on `exists_torsionFrame`). No leaf here RECEIVES `ψ₀`: it is produced by
`exists_torsionFrame`, which states both identities about the same one, so the
two conclusions never come apart. `Wbar₀` is pinned to `D.redCurve` throughout.
And the Frobenius element handed to `exists_torsionFrame` is constrained
VALUATION-theoretically (decomposition-group membership, fixing `emb K`,
inducing `x ↦ x^q` on residues) rather than representation-theoretically, which
is strictly stronger than `ψ₀ ρ(σK) ψ₀⁻¹ = F` and is what defeats the third
counterexample. The valuation subring is pinned by a DEFINITION rather than
carried as a frame field, because `globalFrob q` lies in the decomposition group
of exactly one subring above `q` and a free one would make
`exists_frobeniusLift` false.

NOT VACUOUS: `ψ₀` is a linear EQUIVALENCE and the two conclusions are
conjugation identities, so together they pin `ρ(Frob_q)` into the coset
`Aut · F`; in particular they force `det ρ(Frob_q) = q` via
`WeilPairing.det_frobeniusTorsionEnd`, which is independently PROVEN, so a junk
witness would have to reprove that. -/
theorem WeierstrassCurve.exists_reductionFrame_of_potentiallyGoodModel
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (D : E.PotentiallyGoodModel q) :
    ∃ (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
        ((D.redCurve.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N))
      (ι : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
      (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (D.redCurve.map
              (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
      ι ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ∧
      (∀ x, ψ₀ (E.galoisRep N hN.pos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
            GaloisRepresentation.globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat) x) =
        WeilPairing.frobeniusTorsionEnd q D.redCurve N (ψ₀ x)) ∧
      (∀ x, ψ₀ (E.galoisRep N hN.pos
          (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) ι) x) =
        WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ x)) := by
  obtain ⟨Fr⟩ := D.nonempty_localFrame hq
  obtain ⟨ι, hι, hdecT, hdecS, hτin, hσK, hσres⟩ := D.exists_frobeniusLift hq Fr
  obtain ⟨ψ₀, C, hC, hfrob, haut⟩ :=
    D.exists_torsionFrame hN hq hq2 hqN Fr _ _ hdecS hdecT hτin hσK hσres
  exact ⟨ψ₀, ι, C, hC, hι, hfrob, haut⟩

/-! ##### `autTorsionEnd` is a group ANTI-homomorphism (PROVEN 2026-07-28)

`WeierstrassCurve.autTorsionEnd` above turns an automorphism `C` of `W⁄F` into a
`ZMod N`-linear endomorphism of `W[N]`, and nothing so far said how it interacts
with the group law on `VariableChange F`.  `B₀²ᵃ` below needs exactly one
consequence — `Cⁿ = 1 ⟹ (autTorsionEnd C)ⁿ = 1` — and the three lemmas here
supply it.

The composition law is an ANTI-homomorphism because
`Point.equivVariableChange W C` goes `(C • W).Point → W.Point`, i.e. against the
action: on coordinates it is `(x, y) ↦ (u²x + r, u³y + u²sx + t)`, so applying
`D` and then `C` gives `x ↦ C.u²(D.u²x + D.r) + C.r`, which is the map of
`D * C` (mathlib's `mul_def` has `(D * C).u = D.u * C.u` and
`(D * C).r = D.r * C.u² + C.r`).  Both proofs are one `some_eq_some` and a
`ring`; the `Point.zero` cases are `map_zero`, not `rfl`, because `equivOfEq` is
defined by `subst` and does not reduce on a non-`rfl` equality proof. -/

/-- **The identity change of variables acts as the identity on `N`-torsion**
(PROVEN 2026-07-28).  `(1 : VariableChange F)` is `⟨1, 0, 0, 0⟩`, so the
coordinate map is `(x, y) ↦ (x, y)`. -/
theorem WeierstrassCurve.autTorsionEnd_one {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ)
    (h1 : (1 : WeierstrassCurve.VariableChange F) • (W.map (algebraMap F F))
      = W.map (algebraMap F F)) :
    W.autTorsionEnd 1 h1 N = 1 := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  obtain ⟨(_ | ⟨x, y, hns⟩), hP⟩ := P
  · show (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) 1)
        ((WeierstrassCurve.Affine.Point.equivOfEq h1.symm) 0) = 0
    rw [map_zero, map_zero]
  · show (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) 1)
        ((WeierstrassCurve.Affine.Point.equivOfEq h1.symm)
          (WeierstrassCurve.Affine.Point.some x y hns))
      = WeierstrassCurve.Affine.Point.some x y hns
    rw [WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.equivVariableChange_some]
    refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_ <;>
      simp [WeierstrassCurve.VariableChange.one_def]

/-- **`autTorsionEnd` reverses products** (PROVEN 2026-07-28): composing the
endomorphisms of `C` and of `D` is the endomorphism of `D * C`.  See the section
note above for why the order reverses. -/
theorem WeierstrassCurve.autTorsionEnd_mul {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ)
    (C D : WeierstrassCurve.VariableChange F)
    (hC : C • (W.map (algebraMap F F)) = W.map (algebraMap F F))
    (hD : D • (W.map (algebraMap F F)) = W.map (algebraMap F F))
    (hDC : (D * C) • (W.map (algebraMap F F)) = W.map (algebraMap F F)) :
    W.autTorsionEnd C hC N * W.autTorsionEnd D hD N = W.autTorsionEnd (D * C) hDC N := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  obtain ⟨(_ | ⟨x, y, hns⟩), hP⟩ := P
  · show (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) C)
        ((WeierstrassCurve.Affine.Point.equivOfEq hC.symm)
          ((WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) D)
            ((WeierstrassCurve.Affine.Point.equivOfEq hD.symm) 0)))
      = (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) (D * C))
        ((WeierstrassCurve.Affine.Point.equivOfEq hDC.symm) 0)
    simp only [map_zero]
  · show (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) C)
        ((WeierstrassCurve.Affine.Point.equivOfEq hC.symm)
          ((WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) D)
            ((WeierstrassCurve.Affine.Point.equivOfEq hD.symm)
              (WeierstrassCurve.Affine.Point.some x y hns))))
      = (WeierstrassCurve.Affine.Point.equivVariableChange (W.map (algebraMap F F)) (D * C))
        ((WeierstrassCurve.Affine.Point.equivOfEq hDC.symm)
          (WeierstrassCurve.Affine.Point.some x y hns))
    rw [WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.equivVariableChange_some,
      WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.equivVariableChange_some,
      WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.equivVariableChange_some]
    refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_ <;>
      simp only [WeierstrassCurve.VariableChange.mul_def, Units.val_mul] <;> ring

/-- **A relation `Cⁿ = 1` is inherited by the induced endomorphism of the
`N`-torsion** (PROVEN 2026-07-28).  This is the only consequence of the two
lemmas above that `B₀²ᵃ` needs, and it is what makes the `∀ n, Cⁿ = 1 → …`
phrasing of that leaf transportable. -/
theorem WeierstrassCurve.autTorsionEnd_pow_eq_one {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ)
    (C : WeierstrassCurve.VariableChange F)
    (hC : C • (W.map (algebraMap F F)) = W.map (algebraMap F F)) {n : ℕ} (hn : C ^ n = 1) :
    (W.autTorsionEnd C hC N) ^ n = 1 := by
  have key : ∀ (k : ℕ) (D : WeierstrassCurve.VariableChange F)
      (hD : D • (W.map (algebraMap F F)) = W.map (algebraMap F F)),
      C ^ k = D → (W.autTorsionEnd C hC N) ^ k = W.autTorsionEnd D hD N := by
    intro k
    induction k with
    | zero =>
        intro D hD hk
        rw [pow_zero] at hk
        subst hk
        rw [pow_zero, WeierstrassCurve.autTorsionEnd_one]
    | succ m ih =>
        intro D hD hk
        have hDeq : C * C ^ m = D := by rw [← pow_succ']; exact hk
        subst hDeq
        rw [pow_succ, ih (C ^ m) (WeierstrassCurve.VariableChange.smul_pow_eq_self hC m) rfl,
          WeierstrassCurve.autTorsionEnd_mul W N (C ^ m) C
            (WeierstrassCurve.VariableChange.smul_pow_eq_self hC m) hC hD]
  rw [key n 1 (one_smul _ _) hn, WeierstrassCurve.autTorsionEnd_one]

/-! ##### WHERE THE `B₀` CLUSTER WENT, AND WHY IT WENT DOWN (2026-07-28)

The `B₀` cluster — `B₀²ᵃ`, `B₀¹`, `B₀²`, `B₀`, `B`, leaf `C`,
`exists_isogenyRamificationData` and `exists_isogenySignature` — used to sit
~3300 lines ABOVE this point, immediately after the `D` leaf.  It was moved
DOWN to here VERBATIM, past `exists_reductionFrame_of_potentiallyGoodModel`
just above, because `B₀²ᵃ` needs that frame and Lean has no forward
references.

THE DIRECTION IS THE POINT.  Every note in this cluster used to prescribe the
opposite move — hoisting the ~2300-line `PotentiallyGoodModel` block UP.  That
was tried twice on `flt-lean-341` and rejected twice by the merger
(`50a73c66` deleted the extracted module, `fb82254a` reverted the cut with
it), because the moved region is exactly where several branches are
concurrently growing `TranslationDatum`, `PreTranslationDatum` and the
`exists_potentiallyGoodModel_of_*` family, so the move kept losing and
duplicating declarations.  Moving the CONSUMER down instead costs eight
declarations and ~790 lines, and the cascade terminates.

THE CHECK THAT WOULD REFUTE THE MOVE, run before making it and reproducible in
one pass: nothing in the region skipped over — the `mazurIsogeny_*` arithmetic
and the whole `PotentiallyGoodModel` cluster — mentions any of the eight names
outside a comment.  It does not; every other consumer is either inside the
moved block or thousands of lines below it (`X0.lean`'s uses are in another
module, where declaration order does not apply).

**Do not undo this by re-hoisting the model cluster upwards, and do not
recreate `Fermat/FLT/FreyCurve/PotentiallyGoodModel.lean`** — that file was
deleted by `50a73c66` and any docstring citing it is stale. -/

/-! ##### The two-leaf cut of `B₀` (CARRIED OUT 2026-07-27)

`B₀` — Néron–Ogg–Shafarevich at `q ≠ N` — is PROVEN below from two leaves
plus six lines of arithmetic glue.  The two carry genuinely different
mathematics, and neither implies `B₀` on its own:

* `B₀¹` = `isogenyCharacter_pow_twentyFour_eq_one_of_padicValRat_j_nonneg`
  — the NÉRON–OGG–SHAFAREVICH half.  `λ|_{I_q}` factors through the
  semistability defect `Φ`, whose order divides `24`; hence `λ²⁴ = 1` on
  `I_q`.  Nothing here distinguishes the residue characteristics.
* `B₀²` = `not_eight_dvd_orderOf_isogenyCharacter_of_padicValRat_j_nonneg`
  — the CLASSIFICATION half.  No element of `λ(I_q)` has order divisible
  by `8`.  This is where Kraus's list of the possible `Φ` is consumed, and
  it is the only place the wild primes `q = 2, 3` cost anything.

The glue is the arithmetic fact that a divisor of `24` not divisible by
`8` divides `12`.  Neither `24` nor `8` is negotiable: at `q = 2` the
defect really can have order `8` (`Q₈`) or `24` (`SL₂(𝔽₃)`), so `B₀¹`
alone does NOT give `λ¹² = 1`; and `B₀²` alone bounds nothing.
-/

/-! ##### The Galois-module core of `B₀¹`: the 2026-07-28 cut, and why it is GONE

`B₀¹` was briefly DECOMPOSED (branch `flt-lean-341`, `b23bab50`) into a
Galois-MODULE statement
`WeierstrassCurve.map_pow_twentyFour_eq_self_of_padicValRat_j_nonneg` — "for
`σ ∈ I_q`, `σ²⁴` acts trivially on `E[N]`" — over two leaves under it,
`map_pow_twentyFour_eq_self_of_potentiallyGoodModel` (the `q ≠ 2` half, with
the reduction theory handed over as data) and
`map_pow_twentyFour_eq_self_of_padicValRat_j_nonneg_two` (the wild prime `2`).
That cut names `WeierstrassCurve.PotentiallyGoodModel`, which is declared
~1100 lines BELOW this point, and the branch made it TYPE by hoisting the whole
`PotentiallyGoodModel` cluster out into a new module.

> for `σ ∈ I_q`, `σ²⁴` acts trivially on the `N`-torsion of `E`,

which mentions neither `lam`, nor `hlam`, nor `hg`, nor `hN19`, nor even
`N.Prime` beyond `q ≠ N`.  That sentence is
`WeierstrassCurve.map_pow_twentyFour_eq_self_of_padicValRat_j_nonneg`
below, and `B₀¹` is derived from it in a dozen lines by the standard
`(lam σ).val • g = g ⟹ lam σ = 1` argument that
`isogenyCharacter_pow_twelve_eq_of_localInertia` already runs further
down this file.

WHY THE CHARACTER IS WORTH STRIPPING OFF.  The statement above is a fact
about the mod-`N` Galois REPRESENTATION, not about a character of it, so
it is the same input that `B₀²` needs (`B₀²` reads off the exponent of
`Φ^{ab}`, `B₀¹` the exponent of `Φ`, and both are facts about the image
of `I_q` in `Aut(E[N])`).  Cutting here therefore does not duplicate
work between the two halves of the `B₀` cut; it factors it.

THE GALOIS-MODULE STATEMENT IS THEN SPLIT ON THE RESIDUE
CHARACTERISTIC, because that is where the AVAILABLE machinery splits:

* `WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral`
  turns this leaf's own hypothesis `0 ≤ v_q(j)` into a good model over a
  number field with residue degree one at `q`.  The residual leaf
  `map_pow_twentyFour_eq_self_of_potentiallyGoodModel` is then pure
  Néron–Ogg–Shafarevich plus the classification of the semistability
  defect, with the reduction theory handed over as data.
* **NO SPLIT ON `q = 2` IS NEEDED ANY MORE** (2026-07-28).  An earlier
  version of this paragraph said the producer is "not stated at `q = 2`"
  and prescribed a separate `2`-adic leaf on that ground.  That is no
  longer true: `exists_potentiallyGoodModel_of_jIntegral` is now uniform
  in `q`, its `hq2 : q ≠ 2` hypothesis having been removed when
  `exists_potentiallyGoodModel_of_jIntegral_two` was opened.  The `2`-adic
  arithmetic did not disappear — it is `nonempty_fullTranslationDatum_two`
  — but it is now BEHIND the producer, so this cut sees one case, not two.

THE HOIST THAT THIS CUT NEEDS, AND WHICH HAS NOT BEEN DONE.
`PotentiallyGoodModel` and its producers sit ~1100 lines BELOW this point
IN THIS FILE, so Lean's lack of forward references puts them out of reach
here, and the three-leaf split described above therefore does NOT exist in
the tree: `B₀¹` below is still the single leaf it always was.

The branch that wrote this paragraph moved the cluster VERBATIM into a new
`Fermat/FLT/FreyCurve/PotentiallyGoodModel.lean` (the Minkowski precedent).
That could not be applied at the release-12 integration: two other branches
had meanwhile GROWN the moved region (`TranslationDatum`,
`PreTranslationDatum` and the whole `exists_potentiallyGoodModel_of_*`
family, none of which is in the hoisted file) and MOVED part of it
elsewhere (`flt-lean-381` took `WeierstrassCurve.TameBaseAux` into
`EllipticCurve/TorsionReduction.lean`), so the extraction lost twenty
declarations and duplicated seven — and then, at build 4, reverted the cut with
it, because the mathematics and the refactor were not separable: the refactor
was not packaging, it was what put the structure in scope.  **So none of those
three names exists anywhere in the tree**, and a grep for them finds only
prose.

THE CUT IS NOT WORTH RE-LANDING, and this paragraph deliberately REPLACES the
one that said it was (which prescribed doing the same hoist IN-FILE).  The
declaration-order obstruction is real, but `B₀¹` no longer has to fight it:
`B₀²ᵃ` = `WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg` below
carries the same Serre–Tate transport in a form that is UNIFORM IN `q` — no
`q ≠ 2` exception in the STATEMENT, and, since 2026-07-29, none in the PROOF
either, so there is no `2`-adic leaf anywhere in this cluster; the `2`-adic
reduction theory that genuinely remains sits behind the model producer, as
`nonempty_fullTranslationDatum_two`, which is where it belongs, since it is
reduction theory and not character bookkeeping — and its `htrans` at
`n = 12`, against
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`, gives
`λ(σ)¹² = 1`.  So `λ(σ)²⁴ = 1` is two lines.  `B₀¹` is accordingly PROVEN
below, immediately after `B₀²ᵃ`; moving it past `B₀²ᵃ` was the entire cost.

WHAT REMAINS TRUE of the old note: the reduction theory really is the content
of `B₀`, and it really is blocked by declaration order.  That burden now sits
in exactly ONE place — `exists_inertiaAut_of_padicValRat_j_nonneg`, whose own
docstring records it — instead of in three leaves spread across a refactor
that has already been rejected once.

AND THAT BURDEN IS FAR SMALLER THAN EVERY NOTE HERE HAS ASSUMED.  Both the
old note and `B₀²ᵃ`'s own docstring say the repair is to hoist the
`PotentiallyGoodModel` cluster UPWARDS — ~2300 lines, into or above a region
that several worktrees are concurrently growing, which is exactly the
collision that sank the last attempt.  The opposite move was never measured.
It should have been: **moving the `B₀` cluster DOWN past
`exists_reductionFrame_of_potentiallyGoodModel` costs SEVEN declarations and
about 480 lines, and the cascade terminates** —

    exists_inertiaAut_of_padicValRat_j_nonneg                     (~78 lines)
    isogenyCharacter_pow_twentyFour_eq_one_of_padicValRat_j_nonneg (~104)
    not_eight_dvd_orderOf_isogenyCharacter_of_padicValRat_j_nonneg  (~64)
    isogenyCharacter_pow_twelve_eq_one_of_padicValRat_j_nonneg      (~41)
    isogenyCharacter_pow_twelve_eq_one_of_mem_localInertiaGroup     (~54)
    exists_isogenyRamificationData                                  (~61)
    exists_isogenySignature                                         (~78)

— because every remaining consumer of `exists_isogenySignature` is already
BELOW the frame (in this file: the two `obtain ⟨s, hsmem, hsig, hs6⟩ :=
E.exists_isogenySignature` call sites; and `ModularCurve/X0.lean`, where
declaration order does not apply).  Nothing in the gaps between those seven
consumes any of them, which is why the closure stops.

THE CHECK THAT WOULD REFUTE THIS, and it is one pass over the file rather
than a survey: take the transitive set of declarations in this module that
consume `exists_inertiaAut_of_padicValRat_j_nonneg`, keep those declared
ABOVE the frame, and confirm it is the seven above.  If a new consumer lands
above the frame the number grows, so re-run it rather than quoting it.

This is recorded here and not acted on because
`exists_inertiaAut_of_padicValRat_j_nonneg` had a live owner when it was
measured, and a 480-line relocation of a declaration somebody is mid-proof in
is the one edit guaranteed to conflict. It belongs to whoever closes that
leaf, and it is theirs to do in the same commit. -/

/-! ##### `B₀²ᵃ⁻²`, the `2`-adic leaf: OPENED 2026-07-28, RETIRED 2026-07-29

`WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg_two` — "the statement
of `B₀²ᵃ`, restricted to `q = 2`" — stood here for one day.  It is GONE, and NOT
because it was closed: it was **the wrong cut**, and the obligation it named has
been moved to where the residue characteristic `2` actually costs something,
`WeierstrassCurve.PotentiallyGoodModel.LocalFrame.exists_aut_of_isTorsionReduction_two`
(next to its odd sibling, ~500 lines above).  `B₀²ᵃ` below now case-splits onto
the pair in three lines and is UNIFORM IN `q`.  A grep for the old name finds
only this paragraph.

WHY IT WAS THE WRONG CUT.  It restated the whole of `B₀²ᵃ` at `q = 2` — a good
model, a local frame, a torsion reduction, and an eighty-line descent from
`Cⁿ = 1` to `(λ τ)ⁿ = 1` — when all of that is uniform in `q` and only one
interior step is not.  Its docstring named three obstructions; here is what each
turned out to be, because two were FALSE when written rather than overtaken, and
the pattern is worth keeping:

1. *"`exists_potentiallyGoodModel_of_jIntegral` is literally not stated at
   `q = 2`."*  TRUE when written, OVERTAKEN the same day: the producer is uniform
   in `q` since 2026-07-28 (`exists_potentiallyGoodModel_of_jIntegral_two`), and
   its own docstring says removing `hq2` there was meant precisely to remove the
   reason for splits like this one.  The residual `2`-adic arithmetic is
   `nonempty_fullTranslationDatum_two`, BEHIND the producer, which is its right
   home: it is model theory, not character bookkeeping.
2. *"`exists_isTorsionReduction` carries `hq2` because the reduction map on
   `N`-torsion is injective only when `2` is invertible in the residue field —
   the `2`-division polynomial acquires repeated roots mod `2`."*  **FALSE.**
   Injectivity of reduction on prime-to-`q` torsion never goes through distinct
   torsion points having distinct residues, so the `2`-division polynomial is not
   involved at all: it goes through `IsReductionAlong.redFun_eq_zero_iff` (the
   kernel of reduction is EXACTLY the non-integral locus) together with
   `torsion_abscissa_mem`, whose only arithmetic hypothesis is
   `NeZero (N : κ(D.R))`, i.e. `q ≠ N`.  That is Silverman *AEC* VII.3.1's actual
   argument.  The leaf was proven on 2026-07-28 with its `hq2` unused, and the
   binder is now gone from its signature.
3. *"`exists_aut_of_isTorsionReduction` carries `hq2` for the same reason."*
   FALSE as stated — the reason given is the `2`-division polynomial one, which
   is wrong there too — but that leaf **does** have a reason of its own, and it is
   the only real one in the cluster: its elementary route obtains integrality of
   the inertia variable change from `2s = u a₁' - a₁` and
   `2t = u³ a₃' - a₃ - r a₁`, i.e. BY DIVIDING BY `2`
   (`variableChange_valuation_of_valuation_Δ_eq_one`'s hypothesis
   `h2 : 𝒪.valuation (2 : F) = 1`).  That is what `..._two` above now owns.

THE CONFUSION THAT PRODUCED THE LEAF, since it is the kind that recurs: `q = 2`
really is exceptional for elliptic curves, and three docstrings here said the
exception is the SIZE of the semistability defect — `Q₈` and `SL₂(𝔽₃)` occur at
`2` and nowhere else (Kraus, *Manuscripta Math.* 69 (1990), §1–2).  **That is not
where it bites.**  Every statement in this cluster merely PRODUCES an
automorphism, one per inertia element, and is blind to how many there are; the
single statement that counts them is
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`, proven over ANY
field in `Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`, so the
classification costs this cluster nothing.  Where `2` bites is much duller and
much lower down: a division by `2` in a coordinate computation.  Rule of thumb:
**when a docstring blames `q = 2` on Kraus, check whether the statement counts
automorphisms; if it does not, look for a `2` in a denominator instead.**
-/

/-- **`B₀²ᵃ` — SERRE–TATE TRANSPORT: on inertia at a prime of potentially good
reduction, the isogeny character is a character of an AUTOMORPHISM of the
reduction** (PROVEN 2026-07-28 at every odd `q`, over the reduction frame that
the downward relocation of this cluster put in scope; **UNIFORM IN `q` since
2026-07-29**, when the `2`-adic leaf under it was deleted as spurious — see the
section note immediately above; opened 2026-07-28 while decomposing `B₀²` below;
Serre–Tate, *Ann. of Math.* 88 (1968), Cor. 2 and 3; Silverman *AEC* VII.7 and
*ATAEC* IV.10): at a prime `q ≠ N` with `v_q(j) ≥ 0`, for every `σ` in the
inertia group at `q` there are an elliptic curve `W` over `𝔽̄_q` and an
automorphism `C` of it — an admissible change of variables with `C • W = W` —
such that every relation `Cⁿ = 1` is inherited by `λ(σ)`.

WHAT THIS SAYS, and why it is written with `∀ n` rather than with `orderOf`.
The conclusion is exactly `orderOf (λ σ) ∣ orderOf C`, i.e. `λ(σ)` lies in a
quotient of the cyclic group `⟨C⟩`.  Writing it as an implication removes the
`orderOf C = 0` escape hatch: a witness with an infinite-order `C` would make
an `orderOf`-divisibility conclusion vacuously true, whereas here `n = 0` is
the only free case and it carries nothing.  (No such witness exists anyway —
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq` shows every
stabilising `C` satisfies `C¹² = 1` — but the statement should not depend on
that for its content.)

THE MATHEMATICS.  `v_q(j) ≥ 0` is potentially good reduction (Silverman *AEC*
VII.5.5), so `E` acquires good reduction over a finite extension `K/ℚ_q`.
Since `N ≠ q`, Néron–Ogg–Shafarevich makes `I_K` act trivially on `E[N]`, so
the action of `I_q` on `E[N]` factors through the semistability defect
`Φ = Gal(K^{nr}/ℚ_q^{nr})`, and Serre–Tate embeds `Φ` into the automorphism
group of the good reduction `W` over `𝔽̄_q`.  Reading that action on the
Galois-stable line `⟨g⟩` — which is what `hlam` makes `lam` be — gives `λ(σ)`
as a value of a character of `⟨C⟩`, where `C` is the automorphism attached to
`σ`.  So a relation `Cⁿ = 1` transports to `λ(σ)ⁿ = 1`.

WHAT THIS LEAF DOES **NOT** CONTAIN, and that is the point of the cut: no
classification of `Φ`.  Kraus's list — the only place `q = 2, 3` cost anything
— has been moved out entirely into
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`
(`Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`), which bounds the
EXPONENT of the automorphism group by `12` over any field.  What is left here
is pure reduction theory and Néron–Ogg–Shafarevich, uniform in `q`.

`hlam` IS LOAD-BEARING: without it `lam` is an arbitrary character of `Γ ℚ`
and the statement is FALSE.  `hN19` is not needed for this leaf (only `q ≠ N`
is), and is carried so that the leaves of this cluster share one signature.

**PROVEN 2026-07-28 at every ODD `q`; SORRY-FREE AT EVERY `q` on 2026-07-29**,
when the `2`-adic leaf under it was retired in favour of the pair
`exists_aut_of_isTorsionReduction` / `..._two` at the Serre–Tate step (the section
note immediately above audits all three of the `q ≠ 2` hypotheses that leaf was
routing around; two were spurious and one was real).  The declaration-order
obstruction this paragraph used to record is GONE, and it was removed in the
direction OPPOSITE to the one every note here prescribed: the `B₀` cluster was
moved DOWN past `exists_reductionFrame_of_potentiallyGoodModel` (see the section
note above this cluster), rather than the `PotentiallyGoodModel` block being
hoisted UP.

THE PROOF is four `obtain`s and a transport; only the fourth `obtain` sees `q`:

* `exists_potentiallyGoodModel_of_jIntegral` turns `hj : 0 ≤ v_q(j)` into a good
  model `D` over a number field with residue degree one at `q`;
* `D.nonempty_localFrame` places its field inside `ℚ̄` at the PINNED subring
  `GaloisRepresentation.globalValuationSubring q`;
* `Fr.exists_isTorsionReduction` produces the reduction map `ψ₀` on `N`-torsion,
  coordinatewise-pinned;
* `Fr.exists_aut_of_isTorsionReduction` — Serre–Tate — applied to the image of
  `σ` in `Γ ℚ`, gives `C` with `ψ₀ ∘ ρ(τ) = autTorsionEnd C hC N ∘ ψ₀`.  This is
  the one step that splits on the residue characteristic, and the split is a
  `by_cases hq2 : q = 2` with the two branches differing only in which of
  `exists_aut_of_isTorsionReduction_two` / `exists_aut_of_isTorsionReduction` is
  applied — the statements are identical apart from `hq2`, so the `obtain`'s
  ascribed type is written out once and both branches close it by `exact`.  The
  two memberships it needs are exactly
  `GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring` and
  `GaloisRepresentation.map_mem_inertiaSubgroup_globalValuationSubring`, which is
  why the `∀ σ ∈ I_q` quantifier costs nothing over the frame's single inertia
  element: the frame constrains `ψ₀`, not `σ`, so `ψ₀` is chosen ONCE, before
  `σ` is used, and only the automorphism `C` depends on `σ`.

`Cⁿ = 1` then gives `(autTorsionEnd C hC N)ⁿ = 1` by
`WeierstrassCurve.autTorsionEnd_pow_eq_one` above, hence `ρ(τⁿ) = 1` on `E[N]`
by conjugating with the EQUIVALENCE `ψ₀`, hence `((λ τ)ⁿ).val • g = g` by
`hlam`, hence `(λ τ)ⁿ = 1` because `addOrderOf g = N`.  That last step is the
`(lam σ).val • g = g ⟹ lam σ = 1` argument copied from
`isogenyCharacter_pow_twelve_eq_of_localInertia` below.

WHY `q = 2` IS NOT A SEPARATE LEAF (corrected 2026-07-29; this paragraph used to
say the opposite, and to name a leaf that has since been deleted).  The statement
here is uniform in `q`, and so, it turns out, is the PROOF: none of the four
inputs above needs `2` invertible EXCEPT the Serre–Tate one, and that one is now
a PAIR of leaves rather than a restriction on this statement.  The model producer
became uniform on 2026-07-28; `exists_isTorsionReduction` was proven the same day
with its `hq2` unused, because injectivity of reduction on prime-to-`q` torsion
runs through `IsReductionAlong.redFun_eq_zero_iff` and `torsion_abscissa_mem`
rather than through the `2`-division polynomial; and the fourth `obtain` above
dispatches on `q = 2` in three lines onto
`exists_aut_of_isTorsionReduction_two` / `exists_aut_of_isTorsionReduction`, whose
statements differ only in that hypothesis.  So NOTHING in this file below the
Serre–Tate step carries a residue-characteristic restriction any more.

What does NOT distinguish `q = 2` here, contrary to what this paragraph said
until 2026-07-29: that `Q₈` and `SL₂(𝔽₃)` occur there.  That is a bound on the
SIZE of `Aut(Ẽ)`, which this statement does not assert and its proof does not
consume — it produces ONE automorphism per inertia element.  That bound is
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq`, proven over any
field, and it is applied by `B₀¹` above, not here.  The real `2`-adic cost is a
division by `2` in a coordinate computation, four hundred lines above.

`B₀¹` above is PROVEN over this leaf (`flt-lean-83`) and needs no `2`-adic
exception of its own — and now neither does this one. -/
theorem WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hqN : q ≠ N)
    (hj : 0 ≤ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∃ (W : WeierstrassCurve (AlgebraicClosure (ZMod q))) (_ : W.IsElliptic)
        (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q))),
        C • W = W ∧
        ∀ n : ℕ, C ^ n = 1 →
          lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ n = 1 := by
  classical
  haveI : NeZero N := ⟨hN.ne_zero⟩
  intro σ hσ
  -- the reduction datum and its placement inside `ℚ̄`; uniform in `q`, `2` included
  -- (`hq2` was an argument here until `exists_potentiallyGoodModel_of_jIntegral`
  -- became uniform in `q`; `q = 2` is now dispatched at the Serre–Tate step below.)
  obtain ⟨D⟩ := E.exists_potentiallyGoodModel_of_jIntegral hq hj
  obtain ⟨Fr⟩ := D.nonempty_localFrame hq
  obtain ⟨ψ₀, hψ₀⟩ := Fr.exists_isTorsionReduction hN hqN
  set τ : Field.absoluteGaloisGroup ℚ :=
    Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σ with hτdef
  -- SERRE–TATE: inertia acts, through `ψ₀`, as an automorphism of the reduction
  obtain ⟨C, hC, haut⟩ :
      ∃ (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
        (hC : C • ((D.redCurve.map
                (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
              (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
            = (D.redCurve.map
                (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
              (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))),
        ∀ x, ψ₀ (E.galoisRep N hN.pos τ x) =
          WeierstrassCurve.autTorsionEnd _ C hC N (ψ₀ x) := by
    by_cases hq2 : q = 2
    · exact Fr.exists_aut_of_isTorsionReduction_two hN hq2 hqN ψ₀ hψ₀ τ
        (GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring _ σ)
        (GaloisRepresentation.map_mem_inertiaSubgroup_globalValuationSubring _ σ hσ)
    · exact Fr.exists_aut_of_isTorsionReduction hN hq2 hqN ψ₀ hψ₀ τ
        (GaloisRepresentation.map_mem_decompositionSubgroup_globalValuationSubring _ σ)
        (GaloisRepresentation.map_mem_inertiaSubgroup_globalValuationSubring _ σ hσ)
  refine ⟨D.redCurve.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))), inferInstance,
    C, hC, ?_⟩
  intro n hCn
  -- `Cⁿ = 1` transports to the induced endomorphism of the `N`-torsion
  have hA : (WeierstrassCurve.autTorsionEnd _ C hC N) ^ n = 1 :=
    WeierstrassCurve.autTorsionEnd_pow_eq_one _ N C hC hCn
  -- iterate the intertwining `ψ₀ ∘ ρ(τ) = autTorsionEnd C ∘ ψ₀`
  have hiter : ∀ (k : ℕ) (x : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N),
      ψ₀ (((E.galoisRep N hN.pos) τ ^ k) x)
        = ((WeierstrassCurve.autTorsionEnd _ C hC N) ^ k) (ψ₀ x) := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
        intro x
        rw [pow_succ', pow_succ']
        show ψ₀ ((E.galoisRep N hN.pos) τ (((E.galoisRep N hN.pos) τ ^ m) x))
          = (WeierstrassCurve.autTorsionEnd _ C hC N)
              (((WeierstrassCurve.autTorsionEnd _ C hC N) ^ m) (ψ₀ x))
        rw [haut, ih x]
  -- so `τⁿ` acts trivially on the whole `N`-torsion, `ψ₀` being an EQUIVALENCE
  have hone : ((E.galoisRep N hN.pos) (τ ^ n)) = 1 := by
    refine LinearMap.ext fun x => ?_
    have h1 : ψ₀ (((E.galoisRep N hN.pos) τ ^ n) x) = ψ₀ x := by
      rw [hiter n x, hA]; rfl
    have h2 : ((E.galoisRep N hN.pos) τ ^ n) x = x := ψ₀.injective h1
    rw [map_pow]
    exact h2
  -- `g` is an `N`-torsion point, hence fixed by `τⁿ`
  have hgz : (N : ℤ) • g = 0 := by
    have h1 : addOrderOf g • g = 0 := addOrderOf_nsmul_eq_zero g
    rw [hg] at h1
    rw [natCast_zsmul]
    exact h1
  have hgtor : g ∈ Submodule.torsionBy ℤ ((E⁄(AlgebraicClosure ℚ)).Point) (N : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr hgz
  have h1 : (E.galoisRep N hN.pos) (τ ^ n)
      (⟨g, hgtor⟩ : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N)
      = ⟨g, hgtor⟩ := by rw [hone]; rfl
  have h2 : Affine.Point.map
      ((τ ^ n : Field.absoluteGaloisGroup ℚ) :
        AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g = g :=
    congrArg Subtype.val h1
  rw [hlam (τ ^ n), map_pow] at h2
  -- `k • g = g` with `k = ((λ τ)ⁿ).val` and `addOrderOf g = N` forces `(λ τ)ⁿ = 1`
  have h3 : ((((lam τ ^ n : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) • g = 0 := by
    rw [sub_smul, one_smul, natCast_zsmul, h2, sub_self]
  have h4 : ((N : ℤ)) ∣ ((((lam τ ^ n : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) := by
    have h5 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h3
    rwa [hg] at h5
  have h6 : ((((lam τ ^ n : (ZMod N)ˣ) : ZMod N).val : ZMod N) - 1) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((((lam τ ^ n : (ZMod N)ˣ) : ZMod N).val : ℤ) - 1) N).mpr h4
    push_cast at this ⊢
    exact this
  refine Units.ext ?_
  have h7 : ((((lam τ ^ n : (ZMod N)ˣ) : ZMod N).val : ZMod N))
      = ((lam τ ^ n : (ZMod N)ˣ) : ZMod N) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [h7] at h6
  rw [Units.val_one]
  exact sub_eq_zero.mp h6

/-- **`B₀¹` — Néron–Ogg–Shafarevich: the isogeny character has order
dividing `24` on inertia at `q`** (PROVEN 2026-07-28 over `B₀²ᵃ`
`WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg` immediately
above; Serre–Tate, *Ann. of Math.* 88 (1968), Cor. 2 and 3; Silverman *AEC*
VII.7; Kraus, *Manuscripta Math.* 69 (1990), for the two wild primes): at a
prime `q ≠ N` with `v_q(j) ≥ 0`, the twenty-fourth power of the isogeny
character kills the inertia group at `q`.

THE PROOF IS TWO LINES, and that is the point.  `B₀²ᵃ` produces, for each
`σ ∈ I_q`, an elliptic curve `W` over `𝔽̄_q` and an automorphism `C` of it
such that every relation `Cⁿ = 1` is inherited by `λ(σ)`; and
`WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq` supplies
`C¹² = 1` over ANY field.  So `λ(σ)¹² = 1`, and a fortiori `λ(σ)²⁴ = 1`.

WHERE THE MATHEMATICS WENT.  `v_q(j) ≥ 0` is potentially good reduction
(Silverman *AEC* VII.5.5), so `E` acquires good reduction over a finite
extension `K/ℚ_q`; since `N ≠ q`, Néron–Ogg–Shafarevich makes `I_K` act
trivially on `E[N]`, so the action of `I_q` on `E[N]` — and with it
`λ|_{I_q}`, which is that action read on the stable line `⟨g⟩` — factors
through the semistability defect `Φ = Gal(K^{nr}/ℚ_q^{nr})`; and every `|Φ|`
in the classification has element orders dividing `12` (`{1,2,3,4,6}` at
residue characteristic `≥ 5` by Serre–Tate, together with `Q₈` and `SL₂(𝔽₃)`
at `q = 2` and dicyclic-`12` at `q = 3`, by Kraus).  The FIRST half is
`B₀²ᵃ`; the SECOND is `pow_twelve_eq_one_of_smul_eq`, in
`Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`.  Neither is duplicated
here, and this declaration adds no mathematics of its own.

THIS IS NOW A CONSUMER, NOT A FRONTIER NODE.  It is sorry-free but
transitively open through `B₀²ᵃ`; there is nothing left to prove AT this
declaration, so a prover dispatched at it has no work.  The leaf to attack is
`exists_inertiaAut_of_padicValRat_j_nonneg`.

WHY `24` AND NOT `12`, given that the derivation plainly yields `λ(σ)¹² = 1`.
It is not that `24` is what is available — `12` is.  The `B₀¹`/`B₀²` cut
predates this route and both halves are separately cited, and `B₀`'s glue
(`d ∣ 24` and `8 ∤ d` imply `d ∣ 12`) is exactly what the two were written to
feed; the statement is left at `24` so that the cut is not silently rewritten
underneath its consumers.  A later pass that collapses `B₀¹`, `B₀²` and `B₀`
into one derivation from `B₀²ᵃ` would be correct and is not attempted here.

DECLARATION-ORDER NOTE, now HISTORY.  This docstring used to record that
`WeierstrassCurve.PotentiallyGoodModel` and
`WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral` sit ~1100 lines
BELOW here and were therefore out of reach, and it prescribed hoisting them
into an upstream module.  That prescription is WITHDRAWN **for this leaf** —
the route above needs neither.  It still applies to `B₀²ᵃ`, which does consume
them; see the section note above for why the hoist that was attempted (and
reverted) is not the way to give it them.

`hlam` IS LOAD-BEARING, not decoration: without it `lam` is an arbitrary
character of `Γ ℚ` and the statement is FALSE.  Everything the proof knows
about `lam` at `q` comes from its being the Galois action on the `N`-torsion
point `g`, and `B₀²ᵃ` is where that is used.  `hN19` is likewise not
mathematically needed here (only `q ≠ N` is); it is carried so that the halves
of the `B₀` cut share one signature, and is consumed below only by being
passed on to `B₀²ᵃ`, whose docstring records the same thing. -/
theorem WeierstrassCurve.isogenyCharacter_pow_twentyFour_eq_one_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {q : ℕ} (hq : q.Prime) (hqN : q ≠ N) (hj : 0 ≤ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 24 = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro σ hσ
  -- the Serre–Tate transport: `λ(σ)` is a character value of an automorphism
  -- `C` of the good reduction over `𝔽̄_q`
  obtain ⟨W, hW, C, hC, htrans⟩ :=
    E.exists_inertiaAut_of_padicValRat_j_nonneg g hN hN19 hg lam hlam hq hqN hj σ hσ
  haveI : W.IsElliptic := hW
  -- the classification input: `Aut(W)` has exponent dividing `12`
  have h12 : lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 = 1 :=
    htrans 12 (WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq hC)
  -- `24 = 12 * 2`
  have h242 : (24 : ℕ) = 12 * 2 := by norm_num
  rw [h242, pow_mul, h12, one_pow]

/-- **`B₀²` — no element of order `8` in the inertia image** (sorry leaf;
Kraus, *Manuscripta Math.* 69 (1990), the classification of the
semistability defect; Serre, *Invent. Math.* 15 (1972), §5.6): at a prime
`q ≠ N` with `v_q(j) ≥ 0`, no `σ` in the inertia group at `q` has
`orderOf (λ σ)` divisible by `8`.

This is the exact residue that `B₀¹` leaves: `orderOf (λ σ) ∣ 24`, and the
divisors of `24` that `B₀` must exclude are `8` and `24`, i.e. the ones
divisible by `8`.

Proof (not formalised), and it factors through the SAME `Φ` that `B₀¹`
produces.  `λ|_{I_q}` factors through `Φ`, and `(ZMod N)ˣ` is ABELIAN, so
it factors further through `Φ^{ab}`.  Kraus's list of the possible `Φ` at
potentially good reduction, with abelianizations:

| `Φ`             | occurs at | `Φ^{ab}`   | exponent |
|-----------------|-----------|------------|----------|
| cyclic, order `1,2,3,4,6` | every `q` | itself | `1,2,3,4,6` |
| `Q₈`            | `q = 2`   | `(ℤ/2)²`   | `2` |
| `SL₂(𝔽₃)`       | `q = 2`   | `ℤ/3`      | `3` |
| dicyclic, order `12` | `q = 3` | `ℤ/4`   | `4` |

Every entry has exponent dividing `12`, and in particular none is
divisible by `8` — which is the statement.

FRAMING CORRECTION to the pre-2026-07-27 prose of `B` (and to the
FAITHFULNESS NOTE below, which is amended accordingly).  That note is
right that `e ∈ {1,2,3,4,6}` is FALSE at `q = 2, 3` and that a proof
deriving `λ¹² = 1` from the ramification index `e` ALONE is wrong.  Its
final sentence went one step too far: it claimed that a proof not using
the rational `N`-isogeny is therefore wrong.  The `Φ^{ab}` argument above
uses no Borel and no line, only Kraus's list — because `λ` is a character,
so what bounds it is the exponent of `Φ^{ab}`, not `|Φ|`.  The two
available routes to this leaf are therefore:

* *abelianization* — the table above; needs Kraus's list, nothing else;
* *Borel/torus* — the isogeny puts the image of `I_q` in `GL₂(𝔽_N)` inside
  a Borel `T ⋉ U` with `|U| = N`, and `N > 19` prime does not divide
  `|Φ| ∣ 24`, so `Φ ∩ U = 1` and `Φ ↪ T` is abelian, excluding `Q₈` and
  `SL₂(𝔽₃)` outright.  This is the route the old prose took, and it is
  where `hN19` earns its keep.

Note that BOTH routes still need Kraus's list: abelianness alone does not
exclude a cyclic `Φ` of order `8` or `24` — it is the classification that
says no such `Φ` occurs.  So the isogeny is a convenience here, not a
necessity.  It remains a necessity where the conclusion is about `Φ`
itself rather than about a character of it, e.g. `A₀`'s
`e ∈ {1,2,3,4,6}` at `N`.

The stable line is of course still present in the hypotheses either way:
`hlam` is what makes `lam` the action on `⟨g⟩`, and without it the
statement is false for the same reason as in `B₀¹`.

DECOMPOSED and PROVEN 2026-07-28, and the cut takes NEITHER of the two
routes described above verbatim — it takes the sharper form of the first.
The abelianization route as written still asks for the isomorphism types of
the possible `Φ`, which is more than is needed: what a CHARACTER of `Φ` sees
is only the EXPONENT of `Φ`, and every group on Kraus's list has element
orders in `{1,2,3,4,6}`, hence exponent dividing `12`.  So the leaf splits
cleanly into

* `WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq` — the whole
  geometric input, in `Fermat/FLT/EllipticCurve/AutomorphismExponent.lean`:
  an admissible change of variables fixing an elliptic Weierstrass curve over
  ANY field has twelfth power the identity.  This is where Kraus's list is
  consumed and the only place `q = 2, 3` cost anything; it is proven there in
  the tame characteristics and left as two named leaves at `2` and `3`;
* `WeierstrassCurve.exists_inertiaAut_of_padicValRat_j_nonneg` above — the
  Serre–Tate transport, carrying no classification at all.

The glue is `8 ∤ 12`.  Note the derivation actually yields `orderOf (λ σ) ∣ 12`,
i.e. `B₀` outright, and with it `B₀¹`; the cut into `B₀¹`/`B₀²` is kept because
`B₀¹` is separately owned. -/
theorem WeierstrassCurve.not_eight_dvd_orderOf_isogenyCharacter_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {q : ℕ} (hq : q.Prime) (hqN : q ≠ N) (hj : 0 ≤ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ¬ (8 ∣ orderOf (lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σ))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro σ hσ
  -- the Serre–Tate transport: `λ(σ)` is a character value of an automorphism
  -- `C` of the good reduction over `𝔽̄_q`
  obtain ⟨W, hW, C, hC, htrans⟩ :=
    E.exists_inertiaAut_of_padicValRat_j_nonneg g hN hN19 hg lam hlam hq hqN hj σ hσ
  haveI : W.IsElliptic := hW
  -- the classification input: `Aut(W)` has exponent dividing `12`
  have h12 : lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 = 1 :=
    htrans 12 (WeierstrassCurve.VariableChange.pow_twelve_eq_one_of_smul_eq hC)
  intro h8
  -- `8 ∣ orderOf (λ σ) ∣ 12` is impossible
  exact absurd (h8.trans (orderOf_dvd_of_pow_eq_one h12)) (by norm_num)

/-- **`B₀` — the potentially GOOD half of leaf `B`** (DECOMPOSED and PROVEN
2026-07-27 from `B₀¹` and `B₀²` above;
Néron–Ogg–Shafarevich, Serre–Tate *Ann. of Math.* 88 (1968) Cor. 2 and 3;
Silverman *AEC* VII.7): for a prime `q ≠ N` at which `v_q(j) ≥ 0`, the
twelfth power of the isogeny character kills the inertia group at `q`.

This is `B` with its Tate-curve half removed (that half is leaf `T`
above), so all that is left is Néron–Ogg–Shafarevich at `q ≠ N` — and that
is now split again, into `B₀¹` (the `24` bound) and `B₀²` (no order-`8`
element).  What is left HERE is the arithmetic that joins them: a divisor
of `24` not divisible by `8` divides `12`.

FAITHFULNESS NOTE — this corrects the prose of the pre-2026-07-27 version
of `B`, which asserted `e ∈ {1,2,3,4,6}` outright.  That is the
Serre–Tate statement for residue characteristic `≥ 5` ONLY.  At `q = 2`
the semistability defect `Φ` can be `Q₈` (`e = 8`) or `SL₂(𝔽₃)`
(`e = 24`), and at `q = 3` it can be dicyclic of order `12` — and for
`e = 8` or `e = 24` the conclusion `λ¹² = 1` would NOT follow from `e`
alone.  That is exactly why the cut above bounds the order by `24` and
then removes `8 ∣ ·` separately, rather than claiming `e ∣ 12`.

AMENDED 2026-07-27, and the amendment is the reason `B₀²` is stated the
way it is.  The note used to end "a proof of this leaf that does not use
the stable line somewhere is therefore wrong".  That is too strong.  The
rational `N`-isogeny does rule out `Q₈` and `SL₂(𝔽₃)` — they are
non-abelian and cannot embed in the torus of a Borel — but so does a
cheaper observation that needs no Borel at all: `λ` is a CHARACTER, so
`λ|_{I_q}` factors through `Φ^{ab}`, and every `Φ` on Kraus's list has
abelianization of exponent dividing `12` (`Q₈ ↦ (ℤ/2)²`,
`SL₂(𝔽₃) ↦ ℤ/3`, dicyclic-`12` `↦ ℤ/4`).  See `B₀²`'s docstring for the
table and for what each route does and does not need.  The stable line is
present in the hypotheses regardless — `hlam` is what makes `lam` the
action on `⟨g⟩`, and without it every leaf in this cluster is false. -/
theorem WeierstrassCurve.isogenyCharacter_pow_twelve_eq_one_of_padicValRat_j_nonneg
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {q : ℕ} (hq : q.Prime) (hqN : q ≠ N) (hj : 0 ≤ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 = 1 := by
  -- the arithmetic step: the divisors of `24` that are not divisible by `8`
  -- are exactly the divisors of `12`
  have key : ∀ d : ℕ, d ∣ 24 → ¬ (8 ∣ d) → d ∣ 12 := by
    intro d h1 h2
    have hle : d ≤ 24 := Nat.le_of_dvd (by norm_num) h1
    interval_cases d <;> revert h1 h2 <;> decide
  intro σ hσ
  -- `B₀¹`: Néron–Ogg–Shafarevich bounds the order by `|Φ| ∣ 24`
  have h24 := E.isogenyCharacter_pow_twentyFour_eq_one_of_padicValRat_j_nonneg
    g hN hN19 hg lam hlam hq hqN hj σ hσ
  -- `B₀²`: the classification of `Φ` removes the two divisors `8` and `24`
  have h8 := E.not_eight_dvd_orderOf_isogenyCharacter_of_padicValRat_j_nonneg
    g hN hN19 hg lam hlam hq hqN hj σ hσ
  exact orderOf_dvd_iff_pow_eq_one.mp (key _ (orderOf_dvd_of_pow_eq_one h24) h8)

/-- **`B` — the isogeny character has unramified twelfth power away from
`N`** (DECOMPOSED and PROVEN 2026-07-27 from `T`, `B₀` and `D` above): for
every prime `q ≠ N`, `λ¹²` kills the inertia group at `q`.

The proof is the reduction-type dichotomy at `q`.  The potentially good
branch (`v_q(j) ≥ 0`) IS leaf `B₀`.  The potentially multiplicative branch
(`v_q(j) < 0`) is leaf `T` at `v = q`, which gives `λ¹² = χ^(12r)` on
`I_q`; leaf `D` — proven just above — kills `χ` on `I_q` because `q ≠ N`,
so the right-hand side collapses to `1` whatever `r` is.  That is why `T`
can be stated uniformly in `v` and still serve `B`: the difference between
`v = N` and `v ≠ N` is entirely carried by `D`. -/
theorem WeierstrassCurve.isogenyCharacter_pow_twelve_eq_one_of_mem_localInertiaGroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    {q : ℕ} (hq : q.Prime) (hqN : q ≠ N) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 = 1 := by
  intro σ hσ
  by_cases hj : 0 ≤ padicValRat q E.j
  · -- potentially good reduction at `q`: this IS leaf `B₀`
    exact E.isogenyCharacter_pow_twelve_eq_one_of_padicValRat_j_nonneg
      g hN hN19 hg lam hlam hq hqN hj σ hσ
  · -- potentially multiplicative reduction at `q`: leaf `T` at `v = q`,
    -- whose right-hand side `χ^(12r)` is `1` by leaf `D` since `q ≠ N`
    obtain ⟨r, -, hloc⟩ := E.exists_isogenyTateExponent_of_padicValRat_j_neg
      g hN hN19 hg lam hlam hq (not_le.mp hj)
    rw [hloc σ hσ,
      cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne hN hq hqN σ hσ,
      one_pow]

/-- **`C` — Minkowski globalization of the isogeny character** (PROVEN
2026-07-27, once the Minkowski block was hoisted out of this file into
`Fermat.FLT.GaloisRepresentation.MinkowskiUnramified`; see the section
note above): if `λ¹²` and `χ^s` agree on the inertia group at EVERY
finite place, they agree on all of `Γ ℚ`.

The statement carries the curve data `g`, `hg`, `hlam` for a reason that
is load-bearing rather than decorative: the corresponding statement for
an ARBITRARY `MonoidHom` `Γ ℚ →* (ZMod N)ˣ` is FALSE.  `Γ ℚ` is not
topologically finitely generated, so Nikolov–Segal does not apply, a
finite-index subgroup need not be open, and a discontinuous character
trivial on every inertia group is not excluded.  With `hlam` present the
character is forced continuous, and that is exactly what the proof below
uses: `ker lam` CONTAINS the kernel of the mod-`N` representation
`E.galoisRep N`, which is open by `isOpen_setOf_galoisRep_eq_one`.
Indeed if `galoisRep N σ = 1` then `σ` fixes every `N`-torsion point, in
particular `g`, so `hlam` reads `(lam σ).val • g = g`; with
`addOrderOf g = N` this forces `N ∣ (lam σ).val − 1`, i.e. `lam σ = 1`.

Proof, as the section note predicted.  `ψ := λ¹²·χ^{-s}` is a monoid
homomorphism (`(ZMod N)ˣ` is commutative) whose kernel contains
`ker lam ⊓ ker χ`; that intersection is open — `ker lam` by the paragraph
above, `ker χ` because `continuous_cyclotomicCharacterModL` makes `χ`
continuous into the discrete `ZMod N` — so `ker ψ` is open by
`Subgroup.isOpen_mono`.  `hloc` says `ψ` kills every local inertia image,
so `minkowski_character_trivial` gives `ψ = 1`, which is the claim. -/
theorem WeierstrassCurve.isogenyCharacter_pow_twelve_eq_of_localInertia
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (s : ℕ)
    (hloc : ∀ (q : ℕ) (hq : q.Prime),
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        lam (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)) σ) ^ 12 =
          (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
            (Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) σ)) ^ s) :
    ∀ σ : Field.absoluteGaloisGroup ℚ,
      lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ s := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set χ : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ :=
    GaloisRepresentation.cyclotomicCharacterModL N with hχdef
  -- the `N`-torsion of the base change is finite
  have hcard : Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) = N ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) N
      (Nat.cast_ne_zero.mpr hN.ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have := hN.pos
      positivity)
  -- `g` is an `N`-torsion point
  have hgz : (N : ℤ) • g = 0 := by
    have h1 : addOrderOf g • g = 0 := addOrderOf_nsmul_eq_zero g
    rw [hg] at h1
    rw [natCast_zsmul]
    exact h1
  have hgtor : g ∈ Submodule.torsionBy ℤ ((E⁄(AlgebraicClosure ℚ)).Point) (N : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr hgz
  set P₀ : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N := ⟨g, hgtor⟩
  -- the kernel of the mod-`N` representation is an open subgroup
  set Kρ : Subgroup (Field.absoluteGaloisGroup ℚ) :=
    { carrier := {σ | (E.galoisRep N hN.pos) σ = 1}
      one_mem' := map_one (E.galoisRep N hN.pos)
      mul_mem' := by
        intro a b ha hb
        show (E.galoisRep N hN.pos) (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show (E.galoisRep N hN.pos) a⁻¹ = 1
        have h1 : (E.galoisRep N hN.pos) a⁻¹ * (E.galoisRep N hN.pos) a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρopen : IsOpen (Kρ : Set (Field.absoluteGaloisGroup ℚ)) :=
    isOpen_setOf_galoisRep_eq_one (E.galoisRep N hN.pos) hfin
  -- `Kρ` lies in the kernel of `lam`: an element acting trivially on the
  -- whole `N`-torsion fixes `g`, and `addOrderOf g = N` cancels `g`
  have hKlam : Kρ ≤ lam.ker := by
    intro σ hσ
    have hσ1 : (E.galoisRep N hN.pos) σ = 1 := hσ
    rw [MonoidHom.mem_ker]
    have h1 : (E.galoisRep N hN.pos) σ P₀ = P₀ := by rw [hσ1]; rfl
    have h2 : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g = g :=
      congrArg Subtype.val h1
    rw [hlam σ] at h2
    -- `k • g = g` with `k = (lam σ).val`
    have h3 : (((lam σ : ZMod N).val : ℤ) - 1) • g = 0 := by
      rw [sub_smul, one_smul, natCast_zsmul, h2, sub_self]
    have h4 : ((N : ℤ)) ∣ (((lam σ : ZMod N).val : ℤ) - 1) := by
      have h5 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h3
      rwa [hg] at h5
    have h6 : (((lam σ : ZMod N).val : ZMod N) - 1) = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd
        (((lam σ : ZMod N).val : ℤ) - 1) N).mpr h4
      push_cast at this ⊢
      exact this
    refine Units.ext ?_
    have h7 : ((lam σ : ZMod N).val : ZMod N) = (lam σ : ZMod N) := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [h7] at h6
    rw [Units.val_one]
    exact sub_eq_zero.mp h6
  have hlamopen : IsOpen ((lam.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
      Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isOpen_mono hKlam hKρopen
  -- the cyclotomic character has open kernel: it is continuous into the
  -- discrete space `ZMod N`
  have hχopen : IsOpen ((χ.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
      Set (Field.absoluteGaloisGroup ℚ)) := by
    have hc := GaloisRepresentation.continuous_cyclotomicCharacterModL N
    have hset : ((χ.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
        Set (Field.absoluteGaloisGroup ℚ)) =
        (fun σ : Field.absoluteGaloisGroup ℚ =>
          ((GaloisRepresentation.cyclotomicCharacterModL N σ : (ZMod N)ˣ) : ZMod N)) ⁻¹'
          {(1 : ZMod N)} := by
      ext σ
      constructor
      · intro hσ
        have h1 : χ σ = 1 := MonoidHom.mem_ker.mp hσ
        show ((GaloisRepresentation.cyclotomicCharacterModL N σ : (ZMod N)ˣ) : ZMod N) ∈
          ({(1 : ZMod N)} : Set (ZMod N))
        rw [← hχdef, h1]
        rfl
      · intro hσ
        have h1 : ((GaloisRepresentation.cyclotomicCharacterModL N σ : (ZMod N)ˣ) :
          ZMod N) = 1 := hσ
        rw [← hχdef] at h1
        exact MonoidHom.mem_ker.mpr (Units.ext h1)
    rw [hset]
    exact (isOpen_discrete _).preimage hc
  -- the quotient character `ψ = λ¹² · χ^{-s}`
  set ψ : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ :=
    MonoidHom.mk' (fun σ => lam σ ^ 12 * (χ σ ^ s)⁻¹) (by
      intro a b
      simp only [map_mul, mul_pow, mul_inv]
      exact mul_mul_mul_comm _ _ _ _)
  have hψapp : ∀ σ, ψ σ = lam σ ^ 12 * (χ σ ^ s)⁻¹ := fun σ => rfl
  have hψopen : IsOpen ((ψ.ker : Subgroup (Field.absoluteGaloisGroup ℚ)) :
      Set (Field.absoluteGaloisGroup ℚ)) := by
    refine Subgroup.isOpen_mono (H₁ := lam.ker ⊓ χ.ker) ?_ ?_
    · intro σ hσ
      rw [MonoidHom.mem_ker, hψapp]
      have h1 : lam σ = 1 := MonoidHom.mem_ker.mp hσ.1
      have h2 : χ σ = 1 := MonoidHom.mem_ker.mp hσ.2
      rw [h1, h2, one_pow, one_pow, inv_one, mul_one]
    · exact hlamopen.inter hχopen
  -- Minkowski
  have hψ1 : ψ = 1 := by
    refine minkowski_character_trivial ψ hψopen ?_
    intro q hq σ hσ
    have h : ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
      rw [hψapp, hloc q hq σ hσ, mul_inv_cancel]
    exact MonoidHom.mem_ker.mpr h
  intro σ
  have h1 : ψ σ = 1 := by rw [hψ1]; rfl
  rw [hψapp] at h1
  exact mul_inv_eq_one.mp h1

/-- **Serre–Raynaud local data at `N`** (sorry leaf — the local theory at
`N` alone; Serre, Invent. Math. 15 (1972), Prop. 5 and §5.4, and Raynaud,
Bull. SMF 102 (1974), Cor. 3.4.4): the isogeny character satisfies
`λ¹² = χ_N^s` globally, where `s` comes from a ramification index
`e ∈ {1,2,3,4,6}` and a Raynaud exponent `r ≤ e` — even when `e` is —
through `s·e = 12r`; and the single pair `(e, r) = (4, 2)` forces
`N ≡ 3 (mod 4)`.

This is `exists_isogenySignature` with its combinatorial half removed:
`mazurIsogeny_signatureEnumeration` above turns the `(e, r)` data into
`s ∈ {0, 4, 6, 8, 12}` and `s = 6 → N ≡ 3 (mod 4)` with no further input.
What is left here is exactly the mathematics.

Proof (not formalised), in two halves.

*At `N`.* If `E` has potentially multiplicative reduction at `N` it is a
Tate curve or a quadratic twist of one, so `λ²|_{I_N}` is `1` or
`χ²|_{I_N}`; take sixth powers and read off `(e, r) = (1, 0)` or
`(1, 1)`. Otherwise `E` acquires good reduction over `K/ℚ_N` with
`e = e(K/ℚ_N) ∈ {1,2,3,4,6}` (the possible ramification indices of the
field of definition of the `ℓ`-torsion at a potentially good prime);
tame-inertia theory gives `λ|_{I_N} = χ^a|_{I_N}`, Raynaud's
classification of finite flat group schemes over a base of absolute
ramification `e < p − 1` gives `λ^e|_{I'_N} = χ^r|_{I'_N}` with
`0 ≤ r ≤ e` and `r` even when `e` is even, whence `ae ≡ r (mod N−1)` and
`s = 12r/e`. At `(e, r) = (4, 2)` the quartic ramified extension is
`ℚ_N(⁴√N)`-like and its existence forces `N ≡ 3 (mod 4)`.

*Away from `N`.* `λ¹²` is unramified at every `q ≠ N`, in BOTH reduction
types, so `λ¹²χ_N^{-s}` is unramified everywhere (including at `∞`, since
`s` is even) and therefore trivial by class field theory — `ℚ` has no
nontrivial everywhere-unramified abelian extension.

MACHINERY AUDIT — **CORRECTED 2026-07-27.** The 2026-07-26 version read:
"Missing here: tame-inertia theory at `N`, Raynaud's classification, the
Tate-curve description of the character at potentially multiplicative
reduction, and the class-field-theoretic triviality of an
everywhere-unramified abelian character of `ℚ`. None of these is modular
and none touches the Eisenstein ideal; the last is the only one for which
mathlib is likely to have usable pieces." Its guess about the last item
was right, and understated:

* **Minkowski IS in mathlib and is ALREADY IMPORTED by this file.**
  `Mathlib.NumberTheory.NumberField.ExistsRamified` (in the import block
  above) provides `NumberField.exists_not_isUnramifiedIn`,
  `NumberField.exists_not_isUnramifiedAt_int` and
  `NumberField.finrank_eq_one_of_unramified` — "a number field
  unramified over `ℤ` has rank one", i.e. exactly `ℚ` has no nontrivial
  everywhere-unramified extension, abelian or not. So the class-field
  half is NOT a missing theory; what is missing is only the BRIDGE from
  `Algebra.IsUnramifiedAt` (ramification of ideals) to
  `localInertiaGroup` (inertia inside `Γ ℚᵥ`).
* The idiom for saying "this character is trivial on inertia at `v`"
  already exists in the tree, fully worked, in
  `GaloisRepresentation.cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup`
  (`HardlyRamified/Threeadic.lean`) — but only at `ℓ = 3`; a general-`ℓ`
  version is a prerequisite for the cut below.  **It is now PROVEN here,
  as leaf `D`** (2026-07-27).

Genuinely missing, and unchanged from the previous audit: tame-inertia
theory at `N`, Raynaud's classification, and the Tate-curve description
at potentially multiplicative reduction.  Since 2026-07-27 those three
are the ONLY sorries in this cluster, and they sit in three separate
leaves rather than in two overlapping ones — see below.

EXECUTABLE CUT — **CARRIED OUT 2026-07-27**; this declaration is now
PROVEN from the four leaves stated immediately above (see the section
note there, which records what changed relative to the drafted plan).
The glue is the last twenty lines of this docstring's declaration:

* `A` = `exists_isogenyLocalRamificationDataAt` (local at `N`) — itself
  now PROVEN, as the reduction-type dichotomy over `T` and `A₀`;
* `B` = `isogenyCharacter_pow_twelve_eq_one_of_mem_localInertiaGroup`
  (`λ¹²` unramified away from `N`) — itself now PROVEN, as the same
  dichotomy over `T`, `B₀` and `D`;
* `D` = `cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne`
  (`χ_N` unramified away from `N`) — an ADDITION to the drafted plan,
  which had assumed this was available; it existed in the tree only at
  `ℓ = 3` and only downstream, and is now **PROVEN** here for every
  prime;
* `C` = `isogenyCharacter_pow_twelve_eq_of_localInertia` (Minkowski
  globalization) — CLOSED MATHEMATICS, blocked only by declaration
  order: `minkowski_character_trivial` and the ideal-to-inertia bridge
  are PROVEN in this same file, ~27000 lines below.

The three OPEN leaves of the cluster, after the 2026-07-27 second cut,
are therefore `T` (Tate curve, uniform in the prime, consumed by both `A`
and `B`), `A₀` (tame inertia + Raynaud at `N`) and `B₀`
(Néron–Ogg–Shafarevich at `q ≠ N`).  Each carries exactly one of the
three genuinely missing theories, and none carries two.

Two obligations the glue discharges, both flagged in the drafted plan as
easy to overlook: (i) `s * e = 12 * r` with `s := 12r/e` needs `e ∣ 12r`,
which holds because every admissible `e` divides `12`, so
`rcases he <;> omega` closes it; (ii) continuity of the globalized
character.  Obligation (ii) is NOT discharged in the glue — it is
absorbed into `C`, which carries `g`, `hg` and `hlam` and so derives it
internally.  Stating `C` for an abstract `MonoidHom` instead would have
made it FALSE (`Γ ℚ` is not topologically finitely generated, so
Nikolov–Segal does not apply and a discontinuous character trivial on
every inertia group is not excluded).

This leaf is INDEPENDENT of the formal-immersion leaf: nothing here uses
potentially good reduction away from `N`. -/
theorem WeierstrassCurve.exists_isogenyRamificationData
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g) :
    ∃ e r s : ℕ, (e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) ∧ r ≤ e ∧
      (e % 2 = 0 → r % 2 = 0) ∧ s * e = 12 * r ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ,
        lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ s) ∧
      (e = 4 → r = 2 → N % 4 = 3) := by
  obtain ⟨e, r, he, hre, hpar, hlocN, hmod⟩ :=
    E.exists_isogenyLocalRamificationDataAt g hN hN19 hg lam hlam
  refine ⟨e, r, 12 * r / e, he, hre, hpar, ?_, ?_, hmod⟩
  · -- `s * e = 12 * r`: every admissible `e` divides `12`, hence `12 * r`
    rcases he with rfl | rfl | rfl | rfl | rfl <;> omega
  · -- globalize the inertia-wise identity: at `N` by `A`, away from `N`
    -- both sides are `1` by `B` and `D`
    refine E.isogenyCharacter_pow_twelve_eq_of_localInertia g hN hg lam hlam (12 * r / e) ?_
    intro q hq σ hσ
    by_cases hqN : q = N
    · subst hqN
      exact hlocN σ hσ
    · rw [E.isogenyCharacter_pow_twelve_eq_one_of_mem_localInertiaGroup g hN hN19 hg lam hlam
        hq hqN σ hσ,
        cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup_of_ne hN hq hqN σ hσ,
        one_pow]

/-- **The isogeny signature** (PROVEN 2026-07-26 from
`exists_isogenyRamificationData` and `mazurIsogeny_signatureEnumeration`
— Serre's local theory at `N`
together with Raynaud's classification; Serre, Invent. Math. 15 (1972),
Prop. 5 and §5.4, and Raynaud, Bull. SMF 102 (1974), Cor. 3.4.4): for a
rational cyclic subgroup of prime order `N > 19` with isogeny character
`λ`, there is an integer `s ∈ {0, 4, 6, 8, 12}` — the *isogeny
signature* — with `λ¹² = χ_N^s` as characters of `Gal(ℚ̄/ℚ)`, and if
`s = 6` then `N ≡ 3 (mod 4)`.

Proof (not formalised), in two halves.

*At `N`.* If `E` has potentially multiplicative reduction at `N` it is a
Tate curve or a quadratic twist of one, so `λ²|_{I_N}` is `1` or
`χ²|_{I_N}`, and the claim follows on taking sixth powers. Otherwise `E`
acquires good reduction over `K/ℚ_N` with `e = e(K/ℚ_N) ∈ {1,2,3,4,6}`;
tame-inertia theory gives `λ|_{I_N} = χ^a|_{I_N}`, Raynaud gives
`λ^e|_{I'_N} = χ^r|_{I'_N}` with `0 ≤ r ≤ e`, whence `ae ≡ r (mod N−1)`
and `s = 12r/e`. Enumerating the admissible `(e, r)` — with `r` even
when `e` is even — leaves `s ∈ {0,4,6,8,12}`, and `s = 6` only at
`(e, r) = (4, 2)`, which forces `N ≡ 3 (mod 4)`.

*Away from `N`.* `λ¹²` is unramified at every `q ≠ N`, in BOTH reduction
types, so `λ¹²χ_N^{-s}` is unramified everywhere (including at `∞`,
since `s` is even) and therefore trivial by class field theory —
`ℚ` has no nontrivial everywhere-unramified abelian extension.

This leaf is INDEPENDENT of the formal-immersion leaf: nothing here uses
potentially good reduction away from `N`. -/
theorem WeierstrassCurve.exists_isogenySignature
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN19 : 19 < N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g) :
    ∃ s : ℕ, s ∈ ({0, 4, 6, 8, 12} : Finset ℕ) ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ,
        lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ s) ∧
      (s = 6 → N % 4 = 3) := by
  obtain ⟨e, r, s, he, hre, hpar, hs, hsig, hmod⟩ :=
    E.exists_isogenyRamificationData g hN hN19 hg lam hlam
  obtain ⟨hsmem, h6⟩ := mazurIsogeny_signatureEnumeration he hre hpar hs
  refine ⟨s, ?_, hsig, fun h => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hsmem
  · obtain ⟨he4, hr2⟩ := h6 h
    exact hmod he4 hr2

/-- **The GALOIS half: from a good model with residue degree one, `ρ(σ_q)` is an
automorphism composed with the Frobenius of the reduction** (PROVEN 2026-07-27
over `exists_reductionFrame_of_potentiallyGoodModel` immediately above; opened
the same day by decomposing
`exists_frobeniusAut_of_potentiallyGoodReduction` below). The reduction theory
is an INPUT — `D` hands over the model — and everything remaining is
Néron–Ogg–Shafarevich plus Serre–Tate, which is what the frame above carries.

THE PROOF HERE is the group bookkeeping the frame was cut to expose: the frame
supplies an inertia element `ι` with image `t` in `Γ ℚ` such that `t⁻¹ Frob_q`
acts as the Frobenius of `D.redCurve` and `t` itself acts as an automorphism;
since `galoisRep` is a monoid homomorphism and `Frob_q = t · (t⁻¹ Frob_q)`, the
two identities compose into the conclusion. The reduction curve is `D.redCurve`,
whose ellipticity is the instance proven above — so no existential choice of
`Wbar₀` is made here.

THE AUDITS BELOW DESCRIBE AN OPEN SUB-LEAF, NOT THIS DECLARATION. They are kept
in place because they were written for this statement's content, which since
2026-07-27 lives in `WeierstrassCurve.PotentiallyGoodModel.exists_torsionFrame`
— `exists_reductionFrame_of_potentiallyGoodModel` above is now PROVEN, over
that leaf plus `nonempty_localFrame` and `exists_frobeniusLift`. A prover should
read `exists_torsionFrame`'s docstring FIRST: it carries the ATOMICITY AUDIT
(why `ψ₀` must be constructed rather than received), the live `N = 2`
obligation, the machinery survey and the Chebotarev dead-end note.

THE CONTENT. Write `K`, `R`, `V` for the datum's field, DVR and good model, and
choose a valuation subring `𝒪` of `ℚ̄` above `R`; its residue field is `𝔽̄_q`
because `𝒪` is a valuation subring of an algebraically closed field, and the
residue field of `R` is `𝔽_q` by `D.resEquiv`. Hence the decomposition group of
`𝒪` inside `Γ K` still surjects onto `Gal(𝔽̄_q/𝔽_q)` — THIS IS WHAT RESIDUE
DEGREE ONE BUYS — so a Frobenius lift `σ_K` exists there. For the lift
`σ := globalFrob q` actually named in the conclusion, `τ := σ σ_K⁻¹` then lies
in inertia at `q`, whatever that lift is. Two theorems finish it:

* Néron–Ogg–Shafarevich (easy direction) makes `ρ|_{G_K}` unramified on
  `E[N]` and identifies `ρ(σ_K)` with the `q`-power Frobenius `F` of the
  reduction `Ẽ := V.reduction R`, transported along `D.resEquiv` to a curve
  over `ZMod q`. That transported curve is the `Wbar₀` of the conclusion.
* Serre–Tate (Invent. Math. 15 (1972), Thm 2) makes inertia act through a
  finite subgroup of `Aut(Ẽ_{𝔽̄_q})`, so `ρ(τ) = φ` is an AUTOMORPHISM — the
  `C` of the conclusion, presented as the variable change it is.

Hence `ρ(σ) = φ ∘ F`, which is what the conclusion says. That chain is also what
DISSOLVES the old faithfulness concern about `globalFrob` being defined only up
to inertia: the lift is unconstrained here, and changing it changes only WHICH
automorphism `C` appears — which is exactly why the conclusion carries `C`
EXISTENTIALLY. See
`exists_integerFrobeniusTrace_of_potentiallyGoodReduction`'s docstring for the
full resolution.

MACHINERY, GREPPED 2026-07-27 OVER ALL THREE TREES (`Fermat/`,
`.lake/packages/mathlib/`, `~/cs/FLT/`):

* **Néron–Ogg–Shafarevich is PARTLY PRESENT and must not be rebuilt.**
  `WeierstrassCurve.torsion_unramified_of_good_reduction`
  (`KnownIn1980s/EllipticCurves/GoodReduction.lean`, PROVEN, sorry-free) is
  precisely "good reduction over a DVR `R` ⟹ inertia at a valuation subring
  above `R` acts trivially on the `n`-torsion", for odd `n` invertible in the
  residue field — stated over a GENERAL `R`, which is why the datum above is
  phrased with a DVR. Its companions `torsion_abscissa_mem`,
  `torsion_ordinate_mem`, `torsion_abscissa_residue_ne` and
  `torsion_ordinate_eq_of_residue_eq` are the reduction-injectivity half. The
  assembly pattern to copy is the PROVEN
  `WeilPairing.exists_frobenius_reduction_model`, which does exactly this work
  at the primes of good reduction of a global integral model; the only new
  ingredient here is that the base is `K` rather than `ℚ` and that `σ_K` must
  be produced from residue degree one rather than from an unramified prime.
  Note `torsion_unramified_of_good_reduction` needs `Odd n`, i.e. `N ≠ 2`; the
  hypotheses `q ≠ 2` and `q ≠ N` do not by themselves exclude `N = 2`, so a
  prover should either handle `N = 2` separately or record why it cannot arise.
* **Serre–Tate is ABSENT from all three trees.** What is available and should
  be used rather than rebuilt is the point-level transport of a
  `VariableChange` — `Affine.Point.equivVariableChange` and its
  Galois-equivariant base-changed form `equivVariableChangeBaseChange_galois`,
  in the project shim
  `Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` — and
  the definition `WeierstrassCurve.autTorsionEnd` above, which is already built
  on it. An elementary route avoiding Néron models: `τ ∈ I_q` carries the
  variable change `C` of the datum to `C^τ`, and `D_τ := C^τ C⁻¹` is then a
  variable change between two good models of the same curve, hence has unit
  entries, hence reduces to a variable change over the residue field, which is
  the automorphism `φ`. That is the shape a prover should try first.

THE GLOBAL/CHEBOTAREV AXIS IS A DEAD END HERE, and the reason is structural
rather than technical — recorded so that nobody spends a cycle re-searching it
(the axis searched, 2026-07-27, was: imitate
`WeilPairing.det_galoisRep_eq_cyclotomic`, which pins the DETERMINANT at every
Frobenius globally and so avoids any integral model). `det ρ` is the cyclotomic
CHARACTER, hence unramified at `q ≠ N`, so its value at `σ_q` does not depend
on the choice of lift and a global identity of characters determines it. The
trace is not a character: at potentially-good-but-not-good reduction `ρ` is
genuinely RAMIFIED at `q`, and the trace really does change with the lift
(`a ↦ ζ_e a` for semistability defect `e`). A global argument cannot see inside
a Frobenius coset, so it cannot produce a lift-dependent value. The LOCAL axis
is the only one.

NOT VACUOUS: `ψ₀` is a linear EQUIVALENCE and the conclusion is a conjugation
identity, so it pins `ρ(σ_q)` into the coset `Aut · F`; in particular it forces
`det ρ(σ_q) = q` via `WeilPairing.det_frobeniusTorsionEnd`, which is
independently PROVEN, so a junk witness would have to reprove that. -/
theorem WeierstrassCurve.exists_frobeniusAut_of_potentiallyGoodModel
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (D : E.PotentiallyGoodModel q) :
    ∃ (Wbar₀ : WeierstrassCurve (ZMod q)) (_ : Wbar₀.IsElliptic)
      (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
      (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
        ((Wbar₀.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)),
      ∀ x, ψ₀ (E.galoisRep N hN.pos (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) x) =
        WeierstrassCurve.autTorsionEnd _ C hC N
          (WeilPairing.frobeniusTorsionEnd q Wbar₀ N (ψ₀ x)) := by
  obtain ⟨ψ₀, ι, C, hC, -, hfrob, haut⟩ :=
    E.exists_reductionFrame_of_potentiallyGoodModel hN hq hq2 hqN D
  refine ⟨D.redCurve, inferInstance, C, hC, ψ₀, fun x => ?_⟩
  have hsplit : E.galoisRep N hN.pos (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) x =
      E.galoisRep N hN.pos (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι)
        (E.galoisRep N hN.pos ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) ι)⁻¹ *
          GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, haut, hfrob]

/-- **The local half of Serre–Tate at a named prime: `ρ(σ_q)` is an
automorphism composed with the Frobenius of a good model over `𝔽_q`** (PROVEN
2026-07-27 over the two leaves immediately above,
`exists_potentiallyGoodModel_of_jIntegral` and
`exists_frobeniusAut_of_potentiallyGoodModel`; itself opened earlier the same
day by decomposing
`exists_frobenius_reduction_model_of_potentiallyGoodReduction` below, which is
PROVEN over this leaf and `exists_twist_frobeniusTorsionEnd`).

The proof is the anonymous eliminator: the arithmetic leaf produces a
`PotentiallyGoodModel` datum from `0 ≤ v_q(j(E))`, and the Galois leaf turns
that datum into the conclusion. `hj` is consumed ONLY by the first and the
Galois content is consumed ONLY by the second, which is the whole point of the
cut — see `PotentiallyGoodModel`'s docstring for why those two halves share no
technique. The audits that used to sit here have moved to the two leaves, which
is where a prover should read them:

* `exists_potentiallyGoodModel_of_jIntegral` carries the ARITHMETIC — the good
  model over a number field with residue degree `1` at `q`. `q = 3` is wildly
  ramified there and is used by the consumers, so it cannot be dodged.
* `exists_frobeniusAut_of_potentiallyGoodModel` carries the GALOIS content —
  Néron–Ogg–Shafarevich (partly PROVEN in the tree already, as
  `torsion_unramified_of_good_reduction`) and Serre–Tate (absent). It also
  records, with the reason, that the GLOBAL/Chebotarev axis is a dead end:
  `det ρ` is a character and is unramified at `q`, the trace is neither, and a
  global argument cannot see inside a Frobenius coset.

THE SUPERSEDED AUDIT KEPT FOR ITS REFUTATION CHECK. Before the cut, this leaf
recorded: "exhibit `E/ℚ_3` with `0 ≤ v_3(j(E))` acquiring good reduction over
NO finite totally ramified extension of `ℚ_3`, AND a Frobenius lift whose
action on `E[N]` is not `φ ∘ F` for any elliptic curve over `𝔽_3` and
automorphism `φ`." The first half now refutes only
`exists_potentiallyGoodModel_of_jIntegral`, and the second only
`exists_frobeniusAut_of_potentiallyGoodModel` — which is a further reason the
cut is the right one: the two halves have DIFFERENT refutation checks.

WHAT THE OLD LIST OF MISSING MACHINERY SAID (grepped 2026-07-27 over `Fermat/`,
`.lake/packages/mathlib/` and `~/cs/FLT/` — all three):

1. `0 ≤ v_q(j(E))` ⟹ `E` acquires good reduction over a finite TOTALLY
   RAMIFIED `K/ℚ_q`. Half of this is ALREADY OPEN in this tree as
   `exists_tameGoodModel_of_jIntegral`
   (`EllipticCurve/TorsionReduction.lean`, on `main`), whose `TameGoodModel`
   structure encodes total ramification in precisely the form wanted here —
   its `res : A →+* ZMod ℓ` lands in the PRIME field, which is the encoding.
   But `TameGoodModel` carries no Galois action at all, so it is an INPUT to
   this leaf, not a solution of it; whoever proves that one should expect to
   extend the structure with the `G_K`-equivariance before it is usable here.
   Note also that `exists_tameGoodModel_of_jIntegral` assumes `5 ≤ ℓ`, so it
   does not cover `q = 3` — see the non-uniformity paragraph below.
2. Serre–Tate's theorem that inertia acts through `Aut(Ẽ)`. Absent.

What is NO LONGER on this list, because it has been discharged: the passage
from an automorphism to a twist, which is now the separate leaf
`exists_twist_frobeniusTorsionEnd`; and the point-level action of an
automorphism, which is now the definition `WeierstrassCurve.autTorsionEnd`
above.

THE PROOF OBLIGATION THAT IS NOT UNIFORM IN `q`, STATED HONESTLY. Step 1 is
the standard statement for `q ≥ 5`, where the twisting is by `u` with
`v(u) = d/12` and the field is the TAME Kummer extension `ℚ_q(π^{1/e})`,
`e ∈ {1, 2, 3, 4, 6}` (Silverman *ATAEC* IV.10; Kraus, Manuscripta Math. 69
(1990)). At `q = 3` the semistability defect can be `12` and the extension is
wildly ramified. Two remarks keep that from being a hidden falsity rather than
an open obligation: an unramified layer can always be DROPPED (for `K'/K`
unramified `I_{K'} = I_K`, so good reduction over `K'` already gives good
reduction over `K`), and the singular point of an additive reduction is
unique, hence residue-rational, so the `r, s, t` part of the variable change
costs no extension. What is genuinely not carried out here is the descent of a
WILD totally ramified extension of `ℚ̆_q` to one of `ℚ_q`. `q = 3` IS used by
the consumers (they take `q ∈ {3, 5}`), so this cannot be dodged by adding
`5 ≤ q`.

THE GLOBAL AXIS WAS SEARCHED ON 2026-07-27, AND IT IS A DEAD END FOR THIS
LEAF — recorded so that nobody spends a cycle re-searching it. The suggestion
was to imitate `WeilPairing.det_galoisRep_eq_cyclotomic`, which pins the
DETERMINANT at every Frobenius by a global/Chebotarev argument and so avoids
any integral model. It does not transpose, for a reason that is structural
rather than technical: `det ρ` is the cyclotomic CHARACTER, hence unramified
at `q ≠ N`, so its value at `σ_q` does not depend on the choice of lift and a
global identity of characters determines it. The trace is not a character; at
potentially-good-but-not-good reduction `ρ` is genuinely RAMIFIED at `q`, and
the trace really does change with the lift (`a ↦ ζ_e a` for semistability
defect `e`). A global argument, by construction, cannot distinguish lifts
inside one Frobenius coset, so it cannot produce a lift-dependent value. This
is also why the conclusion here is existential in `C`: the lift-dependence is
carried structurally by which automorphism appears, exactly as
`exists_integerFrobeniusTrace_of_potentiallyGoodReduction`'s docstring
demands. The axis that remains open is therefore the LOCAL one, and step 1
above is its only genuinely missing ingredient. -/
theorem WeierstrassCurve.exists_frobeniusAut_of_potentiallyGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (hj : 0 ≤ padicValRat q E.j) :
    ∃ (Wbar₀ : WeierstrassCurve (ZMod q)) (_ : Wbar₀.IsElliptic)
      (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
      (hC : C • ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
          = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
      (ψ₀ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
        ((Wbar₀.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)),
      ∀ x, ψ₀ (E.galoisRep N hN.pos (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) x) =
        WeierstrassCurve.autTorsionEnd _ C hC N
          (WeilPairing.frobeniusTorsionEnd q Wbar₀ N (ψ₀ x)) :=
  (E.exists_potentiallyGoodModel_of_jIntegral hq hj).elim
    (E.exists_frobeniusAut_of_potentiallyGoodModel hN hq hq2 hqN)

open Polynomial in
/-- **Solvability of `x^n = a·x + b` over an algebraically closed field**
(PROVEN 2026-07-27): for `1 < n` the polynomial `X^n − aX − b` is nonconstant,
so it has a root. This is the only input Lang's theorem needs below: over
`𝔽̄_q` the additive components of a Lang equation are exactly equations of this
shape with `n = q`, and the multiplicative component is `x^{q−1} = a`, which is
`IsAlgClosed.exists_pow_nat_eq`. -/
theorem exists_pow_eq_linear {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 < n)
    (a b : k) : ∃ x : k, x ^ n = a * x + b := by
  set p : k[X] := X ^ n - (C a * X + C b) with hp
  have h1 : (C a * X + C b).degree < (X ^ n : k[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast hn)
  have hdeg : p.degree = (n : ℕ) := by
    rw [hp, degree_sub_eq_left_of_degree_lt h1, degree_X_pow]
  have hne : p.degree ≠ 0 := by
    rw [hdeg]
    exact_mod_cast (by omega : (n : ℕ) ≠ 0)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p hne
  refine ⟨x, ?_⟩
  have hev : x ^ n - (a * x + b) = 0 := by
    simpa only [hp, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] using hx
  linear_combination hev

/-- The `q`-power Frobenius of `𝔽̄_q`, as an algebra map, is `x ↦ x^q`. -/
theorem frobAlgHom_apply (q : ℕ) [Fact q.Prime] (x : AlgebraicClosure (ZMod q)) :
    WeilPairing.frobAlgHom q x = x ^ q := rfl

open Polynomial in
/-- **The fixed field of the `q`-power Frobenius on `𝔽̄_q` is `𝔽_q`**
(PROVEN 2026-07-27): if `x^q = x` then `x` is in the image of
`algebraMap (ZMod q) (AlgebraicClosure (ZMod q))`.

Counting: `X^q − X` has degree `q`, hence at most `q` roots; the `q` elements
of the image of `ZMod q` are all roots (Fermat's little theorem, `ZMod.pow_card`)
and are distinct (the algebra map is injective). So the root set IS the image.

This is the descent step of `exists_twist_curve` below. Note that
`EllipticCurve/FrobeniusFixedField.lean` develops the same fixed fields
`frobFixed q n` at every level `n`; that module is *not* in this file's import
cone, and reproving the `n = 1` case here in 25 lines is cheaper than importing
it. -/
theorem exists_algebraMap_eq_of_pow_card_eq (q : ℕ) [Fact q.Prime]
    {x : AlgebraicClosure (ZMod q)} (hx : x ^ q = x) :
    ∃ y : ZMod q, algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) y = x := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  set f := algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) with hf
  have hfinj : Function.Injective f := f.injective
  set p : (AlgebraicClosure (ZMod q))[X] := X ^ q - X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
  have hpdeg : p.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1
  have hroot : ∀ z : AlgebraicClosure (ZMod q), p.IsRoot z ↔ z ^ q = z := by
    intro z
    simp [hp, IsRoot.def, sub_eq_zero]
  set S : Finset (AlgebraicClosure (ZMod q)) := Finset.image f Finset.univ with hS
  have hScard : S.card = q := by
    rw [hS, Finset.card_image_of_injective _ hfinj, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ p.roots.toFinset := by
    intro z hz
    rw [hS, Finset.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz
    rw [Multiset.mem_toFinset, mem_roots hp0, hroot]
    rw [← map_pow, ZMod.pow_card]
  have hle : p.roots.toFinset.card ≤ S.card := by
    rw [hScard]
    exact le_trans p.roots.toFinset_card_le (le_trans (Polynomial.card_roots' p) hpdeg.le)
  have heq : S = p.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hle
  have hxmem : x ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hp0, hroot]
    exact hx
  rw [← heq, hS, Finset.mem_image] at hxmem
  obtain ⟨y, -, hy⟩ := hxmem
  exact ⟨y, hy⟩

/-- **Lang's theorem for the group of admissible variable changes over `𝔽̄_q`**
(PROVEN 2026-07-27): for every `C` there is a `D` with `φ(D) = C · D`, where `φ`
is the `q`-power Frobenius applied entrywise.

This is the whole cohomological content of the twist classification, and over
`𝔽̄_q` it is elementary rather than a general theorem about connected algebraic
groups. `VariableChange` is `𝔾_m ⋉ 𝔾_a³` with the group law of
`WeierstrassCurve.VariableChange.mul_def`, so the Lang equation splits into four
scalar equations solved in order:

* `u`: `u^q = C.u · u`, i.e. `u^{q−1} = C.u` — solvable because `𝔽̄_q` is
  algebraically closed (`IsAlgClosed.exists_pow_nat_eq`), and the solution is
  nonzero because `C.u` is;
* `r`, `s`, `t`: each of the shape `x^q = x + (known)`, i.e. Artin–Schreier,
  solvable by `exists_pow_eq_linear` above.

The order matters only in that `t`'s constant term mentions `s`.

Note the LEFT form `φ(D) = C · D`, not the right form `φ(D) = D · C`: it is the
left form that makes every map in the torsion transport of
`exists_torsionEquiv_of_twist_curve` a FORWARD map (no `AddEquiv.symm`), which
is what keeps that proof to a `simp only` plus two `ring` calls. Both forms are
solvable; only this one is convenient. -/
theorem exists_variableChange_lang (q : ℕ) [Fact q.Prime]
    (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q))) :
    ∃ D : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)),
      D.map (WeilPairing.frobAlgHom q).toRingHom = C * D := by
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    ((C.u : (AlgebraicClosure (ZMod q)))) (n := q - 1) (by omega)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : q - 1 ≠ 0)] at hz
    exact C.u.ne_zero hz.symm
  have hzq : z ^ q = (C.u : (AlgebraicClosure (ZMod q))) * z := by
    have h1 : z ^ q = z ^ (q - 1) * z := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, hz]
  obtain ⟨r, hr⟩ := exists_pow_eq_linear (k := (AlgebraicClosure (ZMod q))) hq1 1 (C.r * z ^ 2)
  obtain ⟨s, hs⟩ := exists_pow_eq_linear (k := (AlgebraicClosure (ZMod q))) hq1 1 (z * C.s)
  obtain ⟨t, ht⟩ := exists_pow_eq_linear (k := (AlgebraicClosure (ZMod q))) hq1 1
    (C.t * z ^ 3 + C.r * s * z ^ 2)
  refine ⟨⟨Units.mk0 z hz0, r, s, t⟩, ?_⟩
  ext <;>
    simp only [WeierstrassCurve.VariableChange.map, WeierstrassCurve.VariableChange.mul_def,
      Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe,
      Units.val_mk0, Units.val_mul, frobAlgHom_apply]
  · exact hzq
  · rw [hr]; ring
  · rw [hs]; ring
  · rw [ht]; ring

/-- Base change along the identity is the identity. -/
theorem WeierstrassCurve.map_algebraMap_self {F : Type*} [Field F] (W : WeierstrassCurve F) :
    W.map (algebraMap F F) = W := by
  rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]

/-- **Galois descent for Weierstrass curves over `𝔽̄_q`** (PROVEN 2026-07-27):
a curve whose coefficients are fixed by the `q`-power Frobenius is the base
change of a curve over `𝔽_q`. Immediate from
`exists_algebraMap_eq_of_pow_card_eq` applied to the five coefficients. -/
theorem exists_descent_weierstrass (q : ℕ) [Fact q.Prime]
    (V : WeierstrassCurve (AlgebraicClosure (ZMod q)))
    (hV : V.map (WeilPairing.frobAlgHom q).toRingHom = V) :
    ∃ Wbar : WeierstrassCurve (ZMod q),
      Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) = V := by
  have key : ∀ x : AlgebraicClosure (ZMod q),
      (WeilPairing.frobAlgHom q).toRingHom x = x →
      ∃ y : ZMod q, algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) y = x := by
    intro x hxx
    exact exists_algebraMap_eq_of_pow_card_eq q (by rw [← frobAlgHom_apply q x]; exact hxx)
  obtain ⟨b₁, hb₁⟩ := key V.a₁ (by rw [← WeierstrassCurve.map_a₁, hV])
  obtain ⟨b₂, hb₂⟩ := key V.a₂ (by rw [← WeierstrassCurve.map_a₂, hV])
  obtain ⟨b₃, hb₃⟩ := key V.a₃ (by rw [← WeierstrassCurve.map_a₃, hV])
  obtain ⟨b₄, hb₄⟩ := key V.a₄ (by rw [← WeierstrassCurve.map_a₄, hV])
  obtain ⟨b₆, hb₆⟩ := key V.a₆ (by rw [← WeierstrassCurve.map_a₆, hV])
  refine ⟨⟨b₁, b₂, b₃, b₄, b₆⟩, ?_⟩
  ext <;> simpa using ‹_›

/-- **The twist, at the level of CURVES** (PROVEN 2026-07-27): given an
automorphism `C` of `Wbar₀` over `𝔽̄_q`, there is a curve `Wbar` over `𝔽_q` and
an `𝔽̄_q`-variable change `d` carrying `Wbar` to `Wbar₀` and satisfying the Lang
relation `φ(d) = C · d`.

This is ALL the mathematics of `exists_twist_frobeniusTorsionEnd` below; what
remains there is point-level bookkeeping. The construction:

1. Lang (`exists_variableChange_lang`) supplies `d` with `φ(d) = C · d`.
2. `V := d⁻¹ • (Wbar₀ ⁄ 𝔽̄_q)` is Frobenius-stable:
   `φ(V) = φ(d)⁻¹ • φ(Wbar₀) = (C·d)⁻¹ • Wbar₀ = d⁻¹ • (C⁻¹ • Wbar₀) = V`,
   using `C • Wbar₀ = Wbar₀` (so also `C⁻¹ • Wbar₀ = Wbar₀`) and that `Wbar₀` is
   defined over `𝔽_q`, hence Frobenius-stable.
3. Descent (`exists_descent_weierstrass`) turns `V` into a curve `Wbar` over
   `𝔽_q`, and `d • V = Wbar₀` by `smul_inv_smul`.
4. `Wbar` is elliptic because `V` is and `algebraMap` is injective.

The old audit above (`H¹(Gal, Aut)`, Lang's theorem for connected groups, the
`j ∈ {0, 1728}` case analysis of Silverman *AEC* X.5) is RETIRED: none of it is
needed. Working in the full variable-change group `𝔾_m ⋉ 𝔾_a³` rather than in
`Aut` makes the Lang equation four scalar equations over an algebraically
closed field, and the descent is a root count for `X^q − X`. In particular
there is no case split on `j`, no restriction to `q ≥ 5`, and no cohomology. -/
theorem exists_twist_curve (q : ℕ) [Fact q.Prime]
    (Wbar₀ : WeierstrassCurve (ZMod q)) [Wbar₀.IsElliptic]
    (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
    (hC : C • ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
        = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))) :
    ∃ (Wbar : WeierstrassCurve (ZMod q)) (_ : Wbar.IsElliptic)
      (d : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q))),
      d • ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
        = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
            (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))
      ∧ d.map (WeilPairing.frobAlgHom q).toRingHom = C * d := by
  set k := (AlgebraicClosure (ZMod q))
  set E₀ : WeierstrassCurve k := (Wbar₀.map (algebraMap (ZMod q) k)).map (algebraMap k k) with hE₀
  obtain ⟨d, hd⟩ := exists_variableChange_lang q C
  have hCinv : C⁻¹ • E₀ = E₀ := by
    rw [inv_smul_eq_iff]; exact hC.symm
  have hE₀frob : E₀.map (WeilPairing.frobAlgHom q).toRingHom = E₀ := by
    rw [hE₀, WeierstrassCurve.map_algebraMap_self, WeierstrassCurve.map_map]
    congr 1
    exact (WeilPairing.frobAlgHom q).comp_algebraMap
  have hdinv : (d⁻¹).map (WeilPairing.frobAlgHom q).toRingHom
      = (C * d)⁻¹ := by
    have h : (d⁻¹).map (WeilPairing.frobAlgHom q).toRingHom
        = (d.map (WeilPairing.frobAlgHom q).toRingHom)⁻¹ :=
      map_inv (WeierstrassCurve.VariableChange.mapHom _) d
    rw [h, hd]
  have hVfrob : (d⁻¹ • E₀).map (WeilPairing.frobAlgHom q).toRingHom = d⁻¹ • E₀ := by
    rw [← WeierstrassCurve.map_variableChange, hdinv, hE₀frob, mul_inv_rev, mul_smul, hCinv]
  obtain ⟨Wbar, hWbar⟩ := exists_descent_weierstrass q (d⁻¹ • E₀) hVfrob
  haveI : E₀.IsElliptic := by rw [hE₀]; infer_instance
  haveI : (d⁻¹ • E₀).IsElliptic := inferInstance
  have hell : Wbar.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    have h1 : IsUnit ((d⁻¹ • E₀).Δ) := WeierstrassCurve.isUnit_Δ _
    rw [← hWbar, WeierstrassCurve.map_Δ] at h1
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    rw [h0, map_zero] at h1
    exact (isUnit_iff_ne_zero.mp h1) rfl
  refine ⟨Wbar, hell, d, ?_, hd⟩
  rw [WeierstrassCurve.map_algebraMap_self, hWbar, smul_inv_smul]

/-- **Transport of the twist to the `N`-torsion** (PROVEN 2026-07-27): the
curve-level data produced by `exists_twist_curve` induces the asserted
`ZMod N`-linear conjugation on `N`-torsion.

The whole proof is a coordinate computation on `Point.some x y`. Writing `c`
for `C` and `d` for the variable change, and using that both
`Affine.Point.equivVariableChange` and the Frobenius `Affine.Point.map` are
given on coordinates by `(x, y) ↦ (u²x + r, u³y + u²sx + t)` and
`(x, y) ↦ (x^q, y^q)`, the two sides are

* `d ∘ c ∘ φ : x ↦ d.u²(c.u²x^q + c.r) + d.r`,
* `φ ∘ d : x ↦ φ(d.u)²x^q + φ(d.r)`,

and these agree exactly because the Lang relation `φ(d) = C · d` reads
`φ(d.u) = c.u·d.u`, `φ(d.r) = c.r·d.u² + d.r`, `φ(d.s) = d.u·c.s + d.s`,
`φ(d.t) = c.t·d.u³ + c.r·d.s·d.u² + d.t` on components. The `y`-coordinates
match by the same four identities.

TWO FORMATTING FACTS THAT COST AN HOUR EACH, recorded because nothing in the
error messages points at them:

* `Affine.Point.map_some` only fires when the point's curve is written with the
  `baseChange` head (`W⁄K`), not with the unfolded `W.map (algebraMap ..)`. The
  two are definitionally equal, so the application typechecks and `simp`
  silently does nothing. Hence `hC'`/`hd'` here, which are `hC`/`hd` retyped.
* The `Module (ZMod N)` instance on the torsion, conversely, is keyed on the
  form `(Wbar.map (algebraMap ..))⁄K` that `nTorsion` produces. Hence the
  SECOND retyping `hd2`, used only in the final `refine`. Using one form
  everywhere fails at one end or the other. -/
theorem exists_torsionEquiv_of_twist_curve (q : ℕ) [Fact q.Prime]
    (Wbar₀ : WeierstrassCurve (ZMod q)) [Wbar₀.IsElliptic]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
    (hC : C • ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
        = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
    (d : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
    (hd : d • ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
        = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
    (hdlang : d.map (WeilPairing.frobAlgHom q).toRingHom = C * d) :
    ∃ χ : ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)
        ≃ₗ[ZMod N]
        ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N),
      ∀ y, χ (WeierstrassCurve.autTorsionEnd _ C hC N
          (WeilPairing.frobeniusTorsionEnd q Wbar₀ N y)) =
        WeilPairing.frobeniusTorsionEnd q Wbar N (χ y) := by
  have hC' : C • (Wbar₀.baseChange (AlgebraicClosure (ZMod q)))
      = (Wbar₀.baseChange (AlgebraicClosure (ZMod q))) := hC
  have hd' : d • (Wbar.baseChange (AlgebraicClosure (ZMod q)))
      = (Wbar₀.baseChange (AlgebraicClosure (ZMod q))) := hd
  have hd2 : d • ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).baseChange
        (AlgebraicClosure (ZMod q)))
      = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).baseChange
        (AlgebraicClosure (ZMod q)) := hd
  have key : ∀ P : (Wbar₀.baseChange (AlgebraicClosure (ZMod q))).toAffine.Point,
      ((WeierstrassCurve.Affine.Point.equivOfEq hd'.symm).trans
        (WeierstrassCurve.Affine.Point.equivVariableChange
          (Wbar.baseChange (AlgebraicClosure (ZMod q))) d))
        (((WeierstrassCurve.Affine.Point.equivOfEq hC'.symm).trans
          (WeierstrassCurve.Affine.Point.equivVariableChange
            (Wbar₀.baseChange (AlgebraicClosure (ZMod q))) C))
          (WeierstrassCurve.Affine.Point.map (W' := Wbar₀) (S := ZMod q)
            (WeilPairing.frobAlgHom q) P))
        = WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
            (WeilPairing.frobAlgHom q)
            (((WeierstrassCurve.Affine.Point.equivOfEq hd'.symm).trans
              (WeierstrassCurve.Affine.Point.equivVariableChange
                (Wbar.baseChange (AlgebraicClosure (ZMod q))) d)) P) := by
    have hu : (WeilPairing.frobAlgHom q) ((d.u : (AlgebraicClosure (ZMod q)))) =
        (C.u : (AlgebraicClosure (ZMod q))) * (d.u : (AlgebraicClosure (ZMod q))) := by
      have h := congrArg (fun X : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)) =>
        ((X.u : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q)))) hdlang
      simpa [WeierstrassCurve.VariableChange.map,
        WeierstrassCurve.VariableChange.mul_def] using h
    have hr : (WeilPairing.frobAlgHom q) d.r =
        C.r * (d.u : (AlgebraicClosure (ZMod q))) ^ 2 + d.r := by
      have h := congrArg WeierstrassCurve.VariableChange.r hdlang
      simpa [WeierstrassCurve.VariableChange.map,
        WeierstrassCurve.VariableChange.mul_def] using h
    have hs : (WeilPairing.frobAlgHom q) d.s =
        (d.u : (AlgebraicClosure (ZMod q))) * C.s + d.s := by
      have h := congrArg WeierstrassCurve.VariableChange.s hdlang
      simpa [WeierstrassCurve.VariableChange.map,
        WeierstrassCurve.VariableChange.mul_def] using h
    have ht : (WeilPairing.frobAlgHom q) d.t =
        C.t * (d.u : (AlgebraicClosure (ZMod q))) ^ 3
          + C.r * d.s * (d.u : (AlgebraicClosure (ZMod q))) ^ 2 + d.t := by
      have h := congrArg WeierstrassCurve.VariableChange.t hdlang
      simpa [WeierstrassCurve.VariableChange.map,
        WeierstrassCurve.VariableChange.mul_def] using h
    rintro (_ | ⟨x, y, hns⟩)
    · simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero]
    · simp only [AddEquiv.trans_apply, WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.equivVariableChange_some]
      refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
      · simp only [map_add, map_mul, map_pow, hu, hr]
        ring
      · simp only [map_add, map_mul, map_pow, hu, hs, ht]
        ring
  refine ⟨{ TorsionCounting.torsionByCongr (N : ℤ)
      ((WeierstrassCurve.Affine.Point.equivOfEq hd2.symm).trans
        (WeierstrassCurve.Affine.Point.equivVariableChange
          ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).baseChange
            (AlgebraicClosure (ZMod q))) d)) with
      map_smul' := ZMod.map_smul (TorsionCounting.torsionByCongr (N : ℤ)
        ((WeierstrassCurve.Affine.Point.equivOfEq hd2.symm).trans
          (WeierstrassCurve.Affine.Point.equivVariableChange
            ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).baseChange
              (AlgebraicClosure (ZMod q))) d))).toAddMonoidHom }, ?_⟩
  intro y
  apply Subtype.ext
  exact key y.1

/-- **Twisting over a finite field: an automorphism composed with the
Frobenius is the Frobenius of a twist** (PROVEN 2026-07-27, over
`exists_twist_curve` and `exists_torsionEquiv_of_twist_curve` immediately
above; opened the same day by decomposing
`exists_frobenius_reduction_model_of_potentiallyGoodReduction` below). This is
the half of that leaf which is purely a statement about elliptic curves over
`𝔽_q` — no number field, no inertia, no reduction theory — and it is the
standard classification of twists.

THE CONTENT. Twists of `Wbar₀/𝔽_q` are classified by
`H¹(Gal(𝔽̄_q/𝔽_q), Aut(Wbar₀_{𝔽̄_q}))`. The Galois group is procyclic,
topologically generated by Frobenius, and the automorphism group is finite, so
a continuous cocycle is determined by its single value `ξ` at Frobenius and
EVERY `ξ` occurs (`H¹` is `Aut` modulo twisted conjugacy, i.e. the cokernel of
the Lang map). The twist `Wbar` attached to `ξ := C` comes with an isomorphism
`f : Wbar₀_{𝔽̄_q} → Wbar_{𝔽̄_q}` over `𝔽̄_q` intertwining `C ∘ F₀` with the
`q`-power Frobenius of `Wbar` itself; restricting `f` to `N`-torsion gives the
`χ` asserted here. Because `C` ranges over ALL automorphisms, the direction of
the twisting convention is immaterial to the truth of the statement.

HOW IT WAS PROVEN, AND WHY THE OLD MACHINERY AUDIT WAS WRONG. That audit said
`H¹` classification of twists, Lang's theorem and a "Frobenius of a twist"
lemma are absent from all three trees. All three claims about ABSENCE are
still true, and all three turned out to be UNNECESSARY. The route actually
taken avoids `Aut` entirely:

* **Work in the full variable-change group, not in `Aut`.** `VariableChange`
  over `𝔽̄_q` is `𝔾_m ⋉ 𝔾_a³`, a connected solvable group, and its Lang
  equation `φ(d) = C · d` splits into `u^{q−1} = C.u` (solvable because `𝔽̄_q`
  is algebraically closed) and three Artin–Schreier equations `x^q = x + …`
  (likewise). That is `exists_variableChange_lang`, and it is ~25 lines with
  no cohomology, no connectedness theorem, and no case split on `j`.
* **Descend by counting roots of `X^q − X`.** The twisted curve `d⁻¹ • Wbar₀`
  is Frobenius-stable by the Lang relation, so its five coefficients lie in
  the fixed field, which is `𝔽_q` because `X^q − X` has at most `q` roots and
  the image of `𝔽_q` already supplies `q` of them
  (`exists_algebraMap_eq_of_pow_card_eq`).
* **Transport to torsion by coordinates.** `equivVariableChange` and the
  Frobenius `Affine.Point.map` are both explicit on `Point.some x y`, so the
  conjugation identity is two polynomial identities discharged by `ring` from
  the four components of the Lang relation.

The audit's suggestion to use `equivVariableChangeBaseChange_galois` was also
not needed: that lemma is for a variable change defined over the BASE field,
and `C` here is only defined over `𝔽̄_q`.

NOT VACUOUS: `χ` is a linear EQUIVALENCE and the conclusion is a conjugation
identity, so it pins `C ∘ F₀` into the `q`-Frobenius conjugacy class of a
genuine curve over `𝔽_q`; in particular it forces `det (C ∘ F₀) = q` via
`WeilPairing.det_frobeniusTorsionEnd`, which is independently PROVEN, so a
junk witness would have to reprove that. -/
theorem WeierstrassCurve.exists_twist_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar₀ : WeierstrassCurve (ZMod q)) [Wbar₀.IsElliptic] (N : ℕ)
    (C : WeierstrassCurve.VariableChange (AlgebraicClosure (ZMod q)))
    (hC : C • ((Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q))))
        = (Wbar₀.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).map
          (algebraMap (AlgebraicClosure (ZMod q)) (AlgebraicClosure (ZMod q)))) :
    ∃ (Wbar : WeierstrassCurve (ZMod q)) (_ : Wbar.IsElliptic)
      (χ : ((Wbar₀.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)
        ≃ₗ[ZMod N]
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)),
      ∀ y, χ (WeierstrassCurve.autTorsionEnd _ C hC N
          (WeilPairing.frobeniusTorsionEnd q Wbar₀ N y)) =
        WeilPairing.frobeniusTorsionEnd q Wbar N (χ y) := by
  obtain ⟨Wbar, hell, d, hd, hdlang⟩ := exists_twist_curve q Wbar₀ C hC
  haveI := hell
  obtain ⟨χ, hχ⟩ :=
    exists_torsionEquiv_of_twist_curve q Wbar₀ Wbar N C hC d hd hdlang
  exact ⟨Wbar, hell, χ, hχ⟩

/-- **Serre–Tate at a prime of potentially good reduction: the Frobenius
acts as the `q`-power Frobenius of an elliptic curve over `𝔽_q`** (PROVEN
2026-07-27 over the two leaves immediately above,
`exists_frobeniusAut_of_potentiallyGoodReduction` and
`exists_twist_frobeniusTorsionEnd`; itself opened earlier the same day by
decomposing `exists_integerFrobeniusTrace_of_potentiallyGoodReduction` below,
which is PROVEN over this leaf and `hasseWeil_trace_frobeniusTorsionEnd`).

The proof is two lines of bookkeeping: the first leaf writes `ρ(σ_q)` as
`C ∘ F₀` for a good model `Wbar₀/𝔽_q` and an automorphism `C`, and the second
replaces `Wbar₀` by the twist whose own Frobenius that composite is. The two
conjugating equivalences compose.

This is the exact analogue of `WeilPairing.exists_frobenius_reduction_model`
(PROVEN, axiom-clean) with the two quantifiers traded. That theorem covers
EVERY prime outside an *unnamed* finite set `S`, which is useless at a
NAMED prime `q`; this one covers every prime `q ∉ {2, N}` at which `E` has
potentially good reduction — at the price that `Wbar` is then a TWIST of
the reduction rather than the reduction itself. Its conclusion is
otherwise byte-for-byte the same, deliberately, so that the two can be
consumed by the same downstream bookkeeping.

WHY A TWIST, AND WHY THAT IS THE WHOLE POINT. Let `K/ℚ_q` be a finite
TOTALLY RAMIFIED extension over which `E` acquires good reduction, and
`Ẽ/𝔽_q` the good model — the residue field of `K` is still `𝔽_q`, which is
exactly what "totally ramified" buys. Because the residue field did not
grow, `G_K` still surjects onto `Gal(𝔽̄_q/𝔽_q)`, so a Frobenius
`σ_K ∈ G_K` exists; for the lift `σ := globalFrob q` actually named in the
statement we then have `τ := σ σ_K⁻¹ ∈ I_q`, whatever that lift is.
Néron–Ogg–Shafarevich makes `ρ|_{G_K}` unramified and identifies `ρ(σ_K)`
with the `q`-power Frobenius `F ∈ End(Ẽ)`; Serre–Tate (Invent. Math. 15
(1972), Thm 2) makes `I_q` act through a finite subgroup of
`Aut(Ẽ_{𝔽̄_q})`, so `ρ(τ) = φ` is an AUTOMORPHISM. Hence
`ρ(σ) = φ ∘ F`, an ENDOMORPHISM of `Ẽ_{𝔽̄_q}` of degree
`deg φ · deg F = 1 · q = q`. Finally `Gal(𝔽̄_q/𝔽_q) ≅ Ẑ` is procyclic, so
every `φ ∈ Aut(Ẽ_{𝔽̄_q})` is the Frobenius value of a cocycle, and the
corresponding twist `Wbar/𝔽_q` has `φ ∘ F` as ITS own `q`-power
Frobenius. That `Wbar` is the one this statement asserts.

That chain is also what DISSOLVES the parent's old faithfulness concern
about `globalFrob` being defined only up to inertia: the lift is
unconstrained here, and changing it changes only WHICH twist appears. See
the parent's docstring for the full resolution.

WHERE THE REMAINING WORK LIVES. The audits that used to sit here have moved
to the two leaves above, which is where a prover should read them:

* `exists_frobeniusAut_of_potentiallyGoodReduction` carries the LOCAL
  content — the totally ramified good model (`q = 3` is wildly ramified and
  is used by the consumers, so it cannot be dodged) and Serre–Tate. It also
  records, with the reason, that the GLOBAL/Chebotarev axis is a dead end for
  this leaf: `det ρ` is a character and is unramified at `q`, the trace is
  neither, and a global argument cannot see inside a Frobenius coset.
* `exists_twist_frobeniusTorsionEnd` carried the twist classification over
  `𝔽_q`. It is now PROVEN (2026-07-27) and carries no remaining work: the
  route was Lang's equation in the full variable-change group `𝔾_m ⋉ 𝔾_a³`
  over `𝔽̄_q` (four scalar equations over an algebraically closed field),
  Galois descent by a root count for `X^q − X`, and a coordinate computation
  on `Point.some`. No `H¹`, no `Aut` classification, no case split on `j`.
  So the LOCAL leaf above is the only thing still standing between this node
  and its consumers.

NOT VACUOUS: `ψ` is a linear EQUIVALENCE and the conclusion is a
conjugation identity, so it pins `ρ(σ_q)` into the `q`-Frobenius
conjugacy class. In particular it already implies
`det ρ(σ_q) = q` via `WeilPairing.det_frobeniusTorsionEnd`, a nontrivial
consequence that is independently PROVEN — so a junk witness would have
to reprove that. -/
theorem WeierstrassCurve.exists_frobenius_reduction_model_of_potentiallyGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} (hN : N.Prime)
    {q : ℕ} [Fact q.Prime] (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (hj : 0 ≤ padicValRat q E.j) :
    ∃ (Wbar : WeierstrassCurve (ZMod q)) (_ : Wbar.IsElliptic)
      (ψ : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) ≃ₗ[ZMod N]
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)),
      ∀ x, ψ (E.galoisRep N hN.pos (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) x) =
        WeilPairing.frobeniusTorsionEnd q Wbar N (ψ x) := by
  obtain ⟨Wbar₀, hell₀, C, hC, ψ₀, hψ₀⟩ :=
    E.exists_frobeniusAut_of_potentiallyGoodReduction hN hq hq2 hqN hj
  haveI := hell₀
  obtain ⟨Wbar, hell, χ, hχ⟩ :=
    WeierstrassCurve.exists_twist_frobeniusTorsionEnd q Wbar₀ N C hC
  refine ⟨Wbar, hell, ψ₀.trans χ, fun x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hψ₀ x, hχ]

/-- **Hasse's bound** (PROVEN 2026-07-27 — see
`Fermat/FLT/EllipticCurve/HasseBound.lean`, where it is
`HasseBound.sq_frobeniusTrace_le`, proven over the single isogeny-degree
leaf `HasseBound.natCard_ker_degreeFormEnd`; opened as a sorry leaf earlier
the same day by decomposing `hasseWeil_trace_frobeniusTorsionEnd` below):
for an elliptic curve over `𝔽_q`, the trace `a := q + 1 − #Wbar(𝔽_q)`
satisfies `a² ≤ 4q`.

WHERE THE WORK WENT, AND WHAT IS LEFT.  The whole of the inequality is now
machine-checked; what remains is one leaf in the new module, and it is a
NAMED classical theorem rather than an inert inequality:

    HasseBound.natCard_ker_degreeFormEnd :
      q ∤ m → (#ker ([m] − [n]∘F) : ℤ) = m² − a·m·n + n²·q

i.e. the degree of `[m] − [n]∘F` on `Wbar(𝔽̄_q)`, counted by its kernel
(Silverman *AEC* III.6.2 + III.4.10 + V.1.1).  The point of routing
through it is that the value of the quadratic form becomes a CARDINALITY,
so its positivity is `Int.natCast_nonneg` rather than an assumption; the
bound then follows from two explicit evaluations, both arranged to
respect the separability condition `q ∤ m`.  That module also supplies
`HasseBound.frobeniusPointEnd` (the `q`-power Frobenius on the full point
group, of which `WeilPairing.frobeniusTorsionEnd` is the restriction to
the `N`-torsion) and `HasseBound.degreeFormEnd`, which are exactly the
shared infrastructure that
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` below also needs
— note that `natCard_ker_degreeFormEnd` at `(m, n) = (1, 1)` says
`#ker(1 − F) = #Wbar(𝔽_q)`, which is that leaf's own "cheap first step".

THE AUDIT BELOW IS RETAINED because it records the three cuts that were
tried and rejected on the ALGEBRAIC axis, and it is still correct on that
axis: it is the reason the cut finally taken is a geometric one.  The
missing-machinery claim is likewise unchanged — the degree of an isogeny
is still absent from all three trees; it has simply been isolated into one
named leaf instead of hiding inside an inequality.

This is the ARITHMETIC half of that leaf, and it mentions neither `N` nor the
torsion: it is a statement about the point count alone. It is genuinely
Hasse's theorem, and it is what the tree does not have — see the machinery
audit below.

Proof (not formalised): positive definiteness of the degree form on
`End(Wbar_{𝔽̄_q})`. Writing `F` for the `q`-power Frobenius,
`deg(m − nF) = m² − mn·a + n²q ≥ 0` for all `m, n : ℤ`, and the single choice
`(m, n) = (a, 2)` already gives `a² − 4q ≤ 0`. The identity
`#Wbar(𝔽_q) = deg(1 − F)` is what makes `a` the trace of `F`; it is the input
the companion leaf `trace_frobeniusTorsionEnd_eq_natCard` also needs.

**DO NOT ROUTE THIS THROUGH `WeierstrassCurve.End.exists_charPoly`**
(`EllipticCurve/IsogenyTrace.lean`, publicly imported here). It reads as
exactly this statement for a general endomorphism — `ψ² − tψ + n = 0` with
`t² ≤ 4n` — and it is PROVEN there, so it is a natural thing to reach for. It
is unusable here, and worse than unusable: its `n` is `Nat.card (ker ψ)`,
i.e. the SEPARABLE degree, and `Isogeny.frobIsog_degree` in
`EllipticCurve/Isogeny.lean` PROVES that this is `1` for Frobenius, with the
comment "Frobenius is purely inseparable, so its kernel *of points* is trivial
— and this file's `degree` counts exactly that. This is the whole defect."
Feeding Frobenius to `exists_charPoly` would therefore yield `t² ≤ 4` and
`F² + 1 = tF`, which is false for every `q ≥ 5` with `|a| > 2` — and indeed
forces `q = 1` on the Tate module. (Consequently `End.exists_dual`, the leaf
`exists_charPoly` rests on, is itself false in characteristic `p`: it would
make the inverse Frobenius a rational map, which the same file REFUTES in
`isRationalMap_dualHom_is_false`. A repair adding `[CharZero F]` to both was
reported on branch `flt-lean-60`; that is another owner's region and is not
touched here.) The moral is that this leaf needs the TRUE degree, which in
this tree means point counting.

MACHINERY. Point counting over a finite field IS present and PROVEN:
`natCard_affine_point_eq`, `natCard_affine_point_le`,
`natCard_affine_point_pos` in `EllipticCurve/TorsionReduction.lean`, which is
on `main` as of 2026-07-27. What is absent from all three trees (this one,
mathlib, `~/cs/FLT`; grepped 2026-07-27) is the degree form on `End`, the
identity `#E(𝔽_q) = deg(1 − F)`, and the bound itself —
`TorsionReduction.lean`'s own `natCard_affine_point_le` docstring says so in
as many words ("not Hasse's `#W(𝔽_q) = q + 1 − a` with `|a| ≤ 2√q`, which
mathlib does not have").

THE CHECK THAT WOULD REFUTE THE "absent" CLAIM: a declaration in any of those
trees stating `deg (1 - frobenius)`, a `Nat.card` bound of the shape
`|#E(𝔽_q) − q − 1| ≤ 2√q`, or a degree function on isogenies that is not
`Nat.card (ker ·)`. THE AXIS SEARCHED was name-level grep over the three trees
plus a read of this development's own isogeny-degree API.

CUT AUDIT OF 2026-07-27 — THIS LEAF WAS DELIBERATELY LEFT UNDECOMPOSED, AND
HERE IS WHICH CUTS WERE TRIED AND WHY THEY WERE REJECTED. Recording this so
the next owner does not repeat the survey.

* *Degree-form positivity*, i.e. the leaf `∀ m n : ℤ, 0 ≤ m² − a·m·n + n²q`
  with `a := q + 1 − #Wbar(𝔽_q)`, from which this bound is `(m, n) = (a, 2)`
  and two lines of `nlinarith`. REJECTED as a cut because it is EQUIVALENT,
  not smaller: positive semidefiniteness of a binary quadratic form over `ℤ`
  is precisely the discriminant condition `a² ≤ 4q`. It would add a leaf and
  remove no difficulty. It is still the right SHAPE to aim at, because it is
  what a `deg` theory outputs and it covers all twists and extensions at once.
* *Interface-only cut* (`∃ deg : End → ℕ, …axioms…`, then derive the bound).
  REJECTED: the axioms that make it non-vacuous are exactly the quadraticity
  and positivity of `deg`, so the existential leaf is again equivalent.
* *Character-sum route*: `a = −Σ_x χ(f(x))` for `y² = f(x)`, `q` odd, reducing
  the bound to Weil's character-sum estimate. Elementary proofs exist
  (Stepanov's method) but are a multi-hundred-line polynomial-counting
  development, and the reduction needs `q` odd while the consumers use
  `q ∈ {3, 5}`.

THE AXIS THAT WAS NOT SEARCHED THEN, AND WAS TAKEN ON 2026-07-27: the ISOGENY
axis, i.e. giving this tree a `deg` that is the true degree rather than
`Nat.card (ker ·)`. It is now `Fermat/FLT/EllipticCurve/HasseBound.lean`; see
the head of this docstring. The key observation, which is what the three
rejected cuts all miss, is that the quadratic form does not have to be
POSTULATED nonnegative — for `q ∤ m` it IS the cardinality of a kernel. -/
theorem hasse_bound_natCard_affine_point (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] :
    ((q : ℤ) + 1 - (Nat.card Wbar.toAffine.Point : ℤ)) ^ 2 ≤ 4 * (q : ℤ) :=
  _root_.HasseBound.sq_frobeniusTrace_le q Wbar

/-- **Rank-two linear algebra: `det (1 − f) = 1 − tr f + det f`** (PROVEN
2026-07-27). Over an arbitrary commutative ring, for a module with a basis
indexed by `Fin 2`. Pass to matrices (`LinearMap.det_toMatrix`,
`LinearMap.trace_eq_matrix_trace`, `LinearMap.toMatrix_one`) and expand with
`Matrix.det_fin_two` / `Matrix.trace_fin_two`.

This is what lets `trace_frobeniusTorsionEnd_eq_natCard` below be assembled
from a DETERMINANT statement — the Lefschetz congruence
`#Wbar(𝔽_q) ≡ det(1 − F)` — together with `det F = q`. Stating the Lefschetz
half as a determinant rather than as a trace is what makes it the shape a
degree theory actually produces. -/
theorem det_one_sub_fin_two {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (f : Module.End R M) :
    LinearMap.det ((1 : Module.End R M) - f)
      = 1 - LinearMap.trace R M f + LinearMap.det f := by
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- The matrix identity, isolated so that no ambient `simp` lemma can fold
  -- `(toMatrix b b g).det` back into `LinearMap.det g` (which is what a bare
  -- `simp` does here, leaving the goal unprovable by `ring`).
  have hmat : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ((1 : Matrix (Fin 2) (Fin 2) R) - A).det = 1 - A.trace + A.det := by
    intro A
    have h00 : (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := Matrix.one_apply_eq 0
    have h11 : (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := Matrix.one_apply_eq 1
    have h01 : (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 :=
      Matrix.one_apply_ne (by decide)
    have h10 : (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
      Matrix.one_apply_ne (by decide)
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
      h00, h11, h01, h10]
    ring
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b f,
    LinearMap.trace_eq_matrix_trace R b f, map_sub, LinearMap.toMatrix_one, hmat]

/-- **`Wbar[N]` is free of rank two over `ZMod N` when `N` is coprime to `q`**
(PROVEN 2026-07-27). This is exactly what coprimality buys, and it is the
hypothesis whose failure at `N = q^k`, `k ≥ 2`, made the predecessor of
`hasseWeil_trace_frobeniusTorsionEnd` FALSE (see its falsity audit below).

From `WeierstrassCurve.n_torsion_dimension` (`EllipticCurve/Torsion.lean`),
which needs `(N : 𝔽̄_q) ≠ 0`; the algebraic closure has characteristic `q`, so
that is `¬ q ∣ N`, which is `Nat.Coprime N q` for prime `q`. The additive
equivalence is made `ZMod N`-linear by `ZMod.map_smul`, exactly as in
`WeierstrassCurve.p_torsion_rank`. -/
theorem nonempty_basis_nTorsion (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    Nonempty (Module.Basis (Fin 2) (ZMod N)
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)) := by
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqN : ¬ (q ∣ N) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mp hNq.symm
  have hNk : ((N : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := fun hz =>
    hqN ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q N).mp hz)
  obtain ⟨φ⟩ := WeierstrassCurve.n_torsion_dimension
    (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) hNk
  let ψ : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N) ≃ₗ[ZMod N] (ZMod N × ZMod N) :=
    { φ with map_smul' := ZMod.map_smul φ.toAddMonoidHom }
  exact ⟨(Module.Basis.finTwoProd (ZMod N)).map ψ.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Rank-two pairing transformation over a COMMUTATIVE RING** (PROVEN
2026-07-27): for a module with a basis indexed by `Fin 2` over any commutative
ring `R`, an alternating bilinear form `e` transforms under any endomorphism
`f` by the determinant, `e (f x) (f y) = det f * e x y`.

This is `WeilPairing.pairing_map_eq_det_smul` (`EllipticCurve/WeilPairing.lean`,
PROVEN) with its `[Field F]` + `Module.rank F V = 2` hypotheses replaced by
`[CommRing R]` + a given `Fin 2` basis. Nothing in that proof used division:
it passes to matrices in the basis and expands `Matrix.det_fin_two`. The only
step that genuinely needed a field was manufacturing the basis out of the rank
hypothesis, and here the basis is supplied by the caller
(`nonempty_basis_nTorsion` above, whenever `N` is coprime to `q`).

This is what makes the Weil-pairing determinant argument available at
COMPOSITE level `N`, where `ZMod N` is not a field. -/
lemma pairing_map_eq_det_smul_of_basis_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M)
    (e : M →ₗ[R] M →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (f : M →ₗ[R] M) (x y : M) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- skew-symmetry from the alternating property
  have hskew : ∀ v w : M, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add,
      add_zero] at h
    linear_combination h
  -- the matrix of `f` in the basis `b`
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  -- both sides are bilinear; compare on basis pairs
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ f f = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : M →ₗ[R] M →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- **Rank-two determinant from a UNIMODULAR alternating form** (PROVEN
2026-07-27): over a commutative ring, on a module with a `Fin 2` basis, an
endomorphism scaling an alternating form by `c` has determinant `c` — provided
the form takes at least one value that is a UNIT.

`WeilPairing.det_eq_of_conj` is this over a field, where `e x y ≠ 0` suffices
because a nonzero element of a field is cancellable. **Over `ZMod N` with `N`
composite, `e x y ≠ 0` is NOT enough** — `2 ∈ ZMod 4` is a nonzero
non-cancellable value, and `det f * 2 = c * 2` does not pin `det f`. That is
exactly why the composite-level input leaf below has to assert SURJECTIVITY of
the Weil pairing onto `μ_N` (equivalently: some value is a primitive `N`-th
root of unity) rather than merely its nondegeneracy. -/
lemma det_eq_of_conj_of_basis_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M)
    (e : M →ₗ[R] M →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (hnd : ∃ x y, IsUnit (e x y))
    {f : M →ₗ[R] M} {c : R} (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h1 := pairing_map_eq_det_smul_of_basis_fin_two b e halt f x y
  exact hxy.mul_right_cancel (h1.symm.trans (hc x y))

/-- **Surjectivity of a rank-two nondegenerate alternating pairing at
COMPOSITE level** (PROVEN 2026-07-27): on a module carrying a `Fin 2` basis
over `ZMod N`, a multiplicatively bilinear alternating pairing that is killed
by `N` and NONDEGENERATE takes a PRIMITIVE `N`-th root of unity as a value —
namely at the reference basis pair `(b 0, b 1)`.

This is Silverman *AEC* III.8.1(d) ("the Weil pairing is surjective onto
`μ_N`") in its purely linear-algebraic form, and it is what converts the
prime-level shape of the Weil-pairing statement (nondegeneracy,
`∀ x ≠ 0, ∃ y, e x y ≠ 1`) into the shape the composite-level determinant
argument actually consumes (`∃ x y, IsPrimitiveRoot (e x y) N`; see
`det_eq_of_conj_of_basis_fin_two` above for why a unit value, not merely a
nonzero one, is required over `ZMod N`).

The argument is Silverman's, with the cyclicity of `μ_N` replaced by the
rank-two structure, which makes it work verbatim over a non-field: writing
`y = c • b 0 + d • b 1`, bilinearity and alternation give
`e (b 0) y = e (b 0) (b 1) ^ d.val`, so EVERY value against `b 0` is a power
of the single reference value `ζ := e (b 0) (b 1)`. Hence if `ζ ^ l = 1` then
`e (l • b 0) y = e (b 0) y ^ l = 1` for every `y`, so nondegeneracy forces
`l • b 0 = 0`, and reading off the first coordinate of the basis gives
`(l : ZMod N) = 0`, i.e. `N ∣ l`. That is exactly `IsPrimitiveRoot ζ N`.

Note this needs NO cyclic-group theory and no root-of-unity existence input:
the primitive value is produced, not found. -/
lemma isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two
    {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M] [Module (ZMod N) M]
    (b : Module.Basis (Fin 2) (ZMod N) M)
    {G : Type*} [CommGroup G] (e : M → M → G)
    (hl : ∀ x y z, e (x + y) z = e x z * e y z)
    (hr : ∀ x y z, e x (y + z) = e x y * e x z)
    (halt : ∀ x, e x x = 1)
    (hnd : ∀ x, x ≠ 0 → ∃ y, e x y ≠ 1)
    (hpow : ∀ x y, e x y ^ N = 1) :
    IsPrimitiveRoot (e (b 0) (b 1)) N := by
  classical
  -- zero laws by cancellation
  have hzl : ∀ y, e 0 y = 1 := fun y => by
    have h := hl 0 0 y
    rw [add_zero] at h
    have h2 : e 0 y * e 0 y = e 0 y * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h2
  have hzr : ∀ u, e u 0 = 1 := fun u => by
    have h := hr u 0 0
    rw [add_zero] at h
    have h2 : e u 0 * e u 0 = e u 0 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h2
  -- ℕ-power laws
  have hnl : ∀ (n : ℕ) (u v : M), e (n • u) v = e u v ^ n := by
    intro n u v
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact hzl v
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hnr : ∀ (n : ℕ) (u v : M), e u (n • v) = e u v ^ n := by
    intro n u v
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact hzr u
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  -- `ZMod N`-scalars through their ℕ-lift
  have hcast : ∀ (c : ZMod N) (u : M), c • u = c.val • u := by
    intro c u
    have h1 : ((c.val : ℕ) : ZMod N) = c := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    conv_lhs => rw [← h1]
    exact Nat.cast_smul_eq_nsmul _ _ _
  -- every value against `b 0` is a power of the reference value
  have hpowval : ∀ y : M, ∃ k : ℕ, e (b 0) y = e (b 0) (b 1) ^ k := by
    intro y
    have hy : b.repr y 0 • b 0 + b.repr y 1 • b 1 = y := by
      have h := b.sum_repr y
      rwa [Fin.sum_univ_two] at h
    refine ⟨(b.repr y 1).val, ?_⟩
    conv_lhs => rw [← hy]
    rw [hr, hcast, hcast, hnr, hnr, halt, one_pow, one_mul]
  refine ⟨hpow _ _, ?_⟩
  intro l hl1
  -- `l • b 0` pairs trivially with everything, hence vanishes
  have hkill : ∀ y, e (l • b 0) y = 1 := by
    intro y
    obtain ⟨k, hk⟩ := hpowval y
    rw [hnl, hk, ← pow_mul, mul_comm, pow_mul, hl1, one_pow]
  have hzero : l • (b 0) = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := hnd _ hne
    exact hy (hkill y)
  -- read off the first coordinate
  have hzero' : ((l : ZMod N)) • (b 0) = 0 :=
    (Nat.cast_smul_eq_nsmul (ZMod N) l (b 0)).trans hzero
  have hc : (l : ZMod N) = 0 := by
    have h := congrArg (fun z => b.repr z 0) hzero'
    simpa using h
  exact (ZMod.natCast_eq_zero_iff l N).mp hc

/-- **The `μ_N`-valued Weil pairing over `𝔽_q` at COMPOSITE level, in
NONDEGENERATE form** (sorry leaf, opened 2026-07-27 by decomposing
`exists_weilPairing_mu_of_coprime` below): on the `N`-torsion of an elliptic
curve over `𝔽_q`, `N` coprime to `q`, there is a multiplicatively bilinear
alternating pairing valued in the `N`-th roots of unity of `𝔽̄_q`,
NONDEGENERATE, and natural for the `q`-power Frobenius:
`e(Fx, Fy) = F(e(x, y))`.

THIS IS THE VERBATIM LEVEL-`N` ANALOGUE of `WeilPairing.exists_weilPairing_mu`
(`EllipticCurve/WeilPairing.lean`, PROVEN) — clause for clause, with the
prime `p` replaced by `N` and the hypothesis `hqp : q ≠ p` replaced by
`Nat.Coprime N q` (for prime `p` the two say the same thing). Nothing else
differs. The surjectivity clause that the determinant argument needs is
DERIVED from this one — see `exists_weilPairing_mu_of_coprime` immediately
below and `isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two` above — so
this leaf is now the ONLY composite-level arithmetic input, and it is a pure
"re-run the existing construction at level `N`" task.

WHAT THE RE-RUN COSTS, from an audit of the prime-level file (2026-07-27).
The divisor-theoretic construction is level-generic: `N·(P) − N·(O)` is
principal for every `P ∈ E[N]`, and the Miller-generator / Weil-reciprocity
argument never uses primality. Concretely, in `WeilPairing.lean`:

* `weilValueProp` (the admissible-setup predicate that IS the pairing's
  definition) and `weilValueProp_frobenius_transport` already take a BARE
  `(p : ℕ)` with no `[Fact p.Prime]` — they are level-generic today.
* `exists_weilValueSetup_avoiding` and `translationChar_setup_value` carry
  `[Fact p.Prime]` and `_hqp : q ≠ p`, but the coprimality hypothesis is
  UNUSED (it is underscore-named in both).
* `weilValueProp_translationChar_witness`, `weilValue_of_translationChar` and
  `weilValueProp_all_one_torsion_trivial` use primality only to produce
  `((p : 𝔽̄_q) : _) ≠ 0` (via `CharP.cast_ne_zero_of_ne_of_prime`) and
  `p ≠ 0` — both of which follow at composite level from `Nat.Coprime N q`
  exactly as in `nonempty_basis_nTorsion` above.
* `weilValueProp_self_of_two` is the `p = 2` branch of alternation; at level
  `N` the branch condition becomes `2 ∣ N` and the same `2`-torsion geometry
  applies.
* `pairing_trivial_of_radical` is the ONE genuinely field-dependent node (it
  builds a spanning pair by DIVIDING coordinates). It is not needed here:
  `nonempty_basis_nTorsion` supplies the basis directly, and the surjectivity
  consumer above replaces the radical argument entirely.

So the remaining work is confined to `EllipticCurve/WeilPairing.lean` and is
a mechanical `p := N` generalization of that file's Weil-pairing chain, NOT
new mathematics. It was deliberately not attempted here because that file has
a separate owner.

WHY IT CANNOT BE REDUCED TO THE PRIME CASE BY CRT: the prime case covers
`N = p`, not `N = p^k`, and every `N` divisible by a square needs the
prime-power level. -/
theorem exists_weilPairing_mu_nondeg_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →
        (AlgebraicClosure (ZMod q))ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x, x ≠ 0 → ∃ y, e x y ≠ 1) ∧
      (∀ x y, (e x y) ^ N = 1) ∧
      (∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
        Units.map (WeilPairing.frobAlgHom q).toRingHom.toMonoidHom (e x y)) :=
  sorry

/-- **The `μ_N`-valued Weil pairing over `𝔽_q` at COMPOSITE level** (PROVEN
2026-07-27 over `exists_weilPairing_mu_nondeg_of_coprime` above): on the
`N`-torsion of an elliptic curve over `𝔽_q`, `N` coprime to
`q`, there is a multiplicatively bilinear alternating pairing valued in the
`N`-th roots of unity of `𝔽̄_q`, SURJECTIVE onto `μ_N`, and natural for the
`q`-power Frobenius: `e(Fx, Fy) = F(e(x, y))`.

This is Silverman *AEC* III.8.1 (existence, bilinearity, alternation,
surjectivity III.8.1(d)) together with the Galois-equivariance III.8.1(e)
specialised to Frobenius — stated at level `N` rather than at a prime `p`.

WHAT IS AND IS NOT NEW HERE. `WeilPairing.exists_weilPairing_mu`
(`EllipticCurve/WeilPairing.lean`) is the VERBATIM prime-level analogue and is
PROVEN there by the divisor-theoretic construction (the coordinate ring is a
Dedekind domain; `Point.toClass` embeds the points in its class group; for an
`N`-torsion point the `N`-th power of the point ideal is principal with a
Miller generator `f_P`; the pairing is the evaluation ratio
`e(P,Q) = f_P(D_Q)/f_Q(D_P)`, well-defined and bilinear by Weil reciprocity).
**That construction never uses primality of the level** — `N·(P) − N·(O)` is
principal for any `P ∈ E[N]` — so the intended route is to re-run it with `p`
replaced by `N` under `Nat.Coprime N q`, not to invent anything new. Primality
enters the prime-level file only downstream of the construction, in the
`ZMod p`-linear-algebra layer, and THAT layer is what has already been
generalised here: see `pairing_map_eq_det_smul_of_basis_fin_two`,
`det_eq_of_conj_of_basis_fin_two` and `nonempty_basis_nTorsion` above, and
`exists_weilPairing_frobenius_of_coprime` immediately below, which are all
PROVEN at composite level.

WHY SURJECTIVITY AND NOT NONDEGENERACY. The prime-level statement asserts
`∀ x ≠ 0, ∃ y, e x y ≠ 1`, which over a field is enough to cancel. Over
`ZMod N` it is not (see `det_eq_of_conj_of_basis_fin_two`), so the clause here
is `∃ x y, IsPrimitiveRoot (e x y) N`, i.e. the pairing hits a generator of
`μ_N`. That is the standard surjectivity statement and it is what the
determinant argument consumes.

HOW THE SURJECTIVITY IS OBTAINED (2026-07-27, and this is the whole content
of the proof below). It is NOT assumed: it is DERIVED from the nondegeneracy
form `exists_weilPairing_mu_nondeg_of_coprime` above by
`isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two`, using the rank-two
freeness of `Wbar[N]` from `nonempty_basis_nTorsion`. That is Silverman *AEC*
III.8.1(d), and it works over a non-field because rank two makes every value
against `b 0` a power of the single value `e (b 0) (b 1)`, so nondegeneracy
pins that value's order to exactly `N`. Consequently the sorried arithmetic
input is now stated in EXACTLY the prime-level shape, and closing it is a
mechanical `p := N` re-run of `WeilPairing.exists_weilPairing_mu` rather than
a differently-shaped statement.

WHY IT CANNOT BE REDUCED TO THE PRIME CASE BY CRT: the prime case covers
`N = p`, not `N = p^k`, and every `N` divisible by a square needs the
prime-power level. So this is genuinely "redo the level-`N` pairing", not
"assemble the prime cases".

NOT VACUOUS, and here is the junk-witness test it survives: a constant
`e ≡ 1` satisfies bilinearity, alternation, `e^N = 1` and Frobenius naturality
but has no primitive value once `N > 1`; and an alternating form on a rank-two
module is determined up to a scalar, so the surjectivity clause forces `e` to
be the Weil pairing up to a unit. The Frobenius clause then carries the
arithmetic — it is what yields `det F = q`.

THE CHECK THAT WOULD REFUTE THE "missing" CLAIM: a `μ_N`-valued pairing on
`nTorsion N` anywhere in `Fermat/`, `.lake/packages/mathlib/` or `~/cs/FLT/`
without a primality hypothesis. THE AXIS SEARCHED was the primality binders of
this project's own Weil-pairing development (grepped 2026-07-27). -/
theorem exists_weilPairing_mu_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →
        (AlgebraicClosure (ZMod q))ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x y, (e x y) ^ N = 1) ∧
      (∃ x y, IsPrimitiveRoot (e x y) N) ∧
      (∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
        Units.map (WeilPairing.frobAlgHom q).toRingHom.toMonoidHom (e x y)) := by
  classical
  obtain ⟨e, hbl, hbr, halt, hnd, hord, hfrob⟩ :=
    exists_weilPairing_mu_nondeg_of_coprime q Wbar N hNq
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).ne_one (Nat.coprime_zero_left q |>.mp hNq)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  exact ⟨e, hbl, hbr, halt, hord, ⟨b 0, b 1,
    isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two b e hbl hbr halt
      hnd hord⟩, hfrob⟩

/-- **The `ZMod N`-valued Frobenius-twisted Weil pairing at composite level**
(PROVEN 2026-07-27 over `exists_weilPairing_mu_of_coprime` above, by discrete
logarithm): on the `N`-torsion of an elliptic curve over `𝔽_q` with `N`
coprime to `q` there is an alternating `ZMod N`-bilinear pairing taking a UNIT
value which the `q`-power Frobenius scales by `q`.

This is the exact composite-level analogue of
`WeilPairing.exists_weilPairing_frobenius`, and — unlike the `μ_N`-valued leaf
above — its derivation is entirely level-generic, which is why it is proven
here rather than left open. The discrete logarithm is taken base the primitive
value `ζ := e(x₀, y₀)` supplied by the surjectivity clause, so no separate
root-of-unity existence argument is needed: `IsPrimitiveRoot.zpowers_eq`
identifies `μ_N` with `zpowers ζ`, and `IsPrimitiveRoot.zmodEquivZPowers`
identifies that with `ZMod N` additively. The reference pair then logs to `1`,
which is where the unit value comes from — this is precisely the step that
fails if one only assumes nondegeneracy. -/
theorem exists_weilPairing_frobenius_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
        (((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      (∀ v, e v v = 0) ∧ (∃ x y, IsUnit (e x y)) ∧
      ∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (q : ZMod N) * e x y := by
  classical
  obtain ⟨e₀, hbl, hbr, halt, hord, ⟨x₀, y₀, hprim⟩, hfrob⟩ :=
    exists_weilPairing_mu_of_coprime q Wbar N hNq
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).ne_one (Nat.coprime_zero_left q |>.mp hNq)
  haveI : NeZero N := ⟨hN0⟩
  -- the discrete logarithm base the primitive value produced by surjectivity
  set ζu : (AlgebraicClosure (ZMod q))ˣ := e₀ x₀ y₀
  have hmem : ∀ x y, e₀ x y ∈ Subgroup.zpowers ζu := by
    intro x y
    rw [hprim.zpowers_eq]
    exact (mem_rootsOfUnity N _).mpr (hord x y)
  set dlog : ∀ (_ _ : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N)), ZMod N :=
    fun x y => hprim.zmodEquivZPowers.symm
      (Additive.ofMul (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu))
    with hdlogdef
  -- the reference pair logs to `1`, which is the unit value
  have hdunit : IsUnit (dlog x₀ y₀) := by
    have hval1 : ((Additive.toMul
        (hprim.zmodEquivZPowers (((1 : ℕ) : ZMod N)))) :
        Subgroup.zpowers ζu).1 = ζu := by
      rw [hprim.zmodEquivZPowers_apply_coe_nat 1]
      exact pow_one ζu
    have helt : (⟨e₀ x₀ y₀, hmem x₀ y₀⟩ : Subgroup.zpowers ζu) =
        Additive.toMul (hprim.zmodEquivZPowers (((1 : ℕ) : ZMod N))) :=
      Subtype.ext hval1.symm
    have h2 : dlog x₀ y₀ = ((1 : ℕ) : ZMod N) := by
      show hprim.zmodEquivZPowers.symm
        (Additive.ofMul (⟨e₀ x₀ y₀, hmem x₀ y₀⟩ : Subgroup.zpowers ζu)) = _
      rw [helt]
      exact hprim.zmodEquivZPowers.symm_apply_apply _
    rw [h2, Nat.cast_one]
    exact isUnit_one
  -- transfer of the pairing laws through the logarithm
  have hdadd_l : ∀ x y z, dlog (x + y) z = dlog x z + dlog y z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ (x + y) z, hmem (x + y) z⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x z, hmem x z⟩ : Subgroup.zpowers ζu) * ⟨e₀ y z, hmem y z⟩ :=
      Subtype.ext (hbl x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdadd_r : ∀ x y z, dlog x (y + z) = dlog x y + dlog x z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ x (y + z), hmem x (y + z)⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) * ⟨e₀ x z, hmem x z⟩ :=
      Subtype.ext (hbr x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdalt : ∀ x, dlog x x = 0 := by
    intro x
    simp only [hdlogdef]
    have hsub : (⟨e₀ x x, hmem x x⟩ : Subgroup.zpowers ζu) = 1 :=
      Subtype.ext (halt x)
    rw [hsub]
    rw [show Additive.ofMul (1 : Subgroup.zpowers ζu) = 0 from rfl, map_zero]
  have hdfrob : ∀ x y, dlog (WeilPairing.frobeniusTorsionEnd q Wbar N x)
      (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (q : ZMod N) * dlog x y := by
    intro x y
    simp only [hdlogdef]
    have hval : e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
        (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (e₀ x y) ^ q := by
      rw [hfrob]
      refine Units.ext ?_
      show WeilPairing.frobAlgHom q
          ((e₀ x y : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q))) =
        (((e₀ x y) ^ q : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q)))
      rw [Units.val_pow_eq_pow_val]
      rfl
    have hsub : (⟨e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
        (WeilPairing.frobeniusTorsionEnd q Wbar N y), hmem _ _⟩ :
        Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :=
      Subtype.ext (by
        show e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
          ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :
            Subgroup.zpowers ζu).1
        rw [hval]
        rfl)
    refine Eq.trans (congrArg (fun g : Subgroup.zpowers ζu =>
      hprim.zmodEquivZPowers.symm (Additive.ofMul g)) hsub) ?_
    show hprim.zmodEquivZPowers.symm
      (Additive.ofMul ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q)) = _
    rw [ofMul_pow, map_nsmul, nsmul_eq_mul]
  -- zero laws, then the two linear-map packagings
  have hdzero_r : ∀ x, dlog x 0 = 0 := by
    intro x
    have h2 := hdadd_r x 0 0
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  have hdzero_l : ∀ y, dlog 0 y = 0 := by
    intro y
    have h2 := hdadd_l 0 0 y
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  have heinner : ∀ x : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N),
      ∃ f : (((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      ∀ y, f y = dlog x y := by
    intro x
    refine ⟨AddMonoidHom.toZModLinearMap N
      ⟨⟨dlog x, hdzero_r x⟩, hdadd_r x⟩, fun y => rfl⟩
  choose einner heinnerval using heinner
  have houter : ∃ e : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
      (((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      ∀ x y, e x y = dlog x y := by
    refine ⟨AddMonoidHom.toZModLinearMap N
      ⟨⟨einner, ?_⟩, ?_⟩, fun x y => heinnerval x y⟩
    · refine LinearMap.ext fun y => ?_
      rw [heinnerval]
      exact hdzero_l y
    · intro x₁ x₂
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.add_apply, heinnerval, heinnerval, heinnerval]
      exact hdadd_l x₁ x₂ y
  obtain ⟨e, he⟩ := houter
  refine ⟨e, fun v => (he v v).trans (hdalt v), ⟨x₀, y₀, ?_⟩, ?_⟩
  · rw [he]
    exact hdunit
  · intro x y
    rw [he, he]
    exact hdfrob x y

/-- **The Frobenius determinant on the `N`-torsion for `N` coprime to `q`**
(PROVEN 2026-07-27 over `exists_weilPairing_mu_of_coprime` above; itself
opened the same day by decomposing `trace_frobeniusTorsionEnd_eq_natCard`
below): `det F = q` on `Wbar[N]`.

This is `WeilPairing.det_frobeniusTorsionEnd` (`EllipticCurve/WeilPairing.lean`)
generalised from a PRIME level `p ≠ q` to any level coprime to `q`, and the
proof is the same three-line assembly: `nonempty_basis_nTorsion` supplies the
`Fin 2` basis, `exists_weilPairing_frobenius_of_coprime` supplies an
alternating `ZMod N`-valued form with a UNIT value that Frobenius scales by
`q`, and `det_eq_of_conj_of_basis_fin_two` reads off the determinant.

WHAT REMAINS OPEN is only the arithmetic input, isolated as the single leaf
`exists_weilPairing_mu_of_coprime` above: the `μ_N`-valued Weil pairing at
composite level. Everything between that leaf and this statement — the
rank-two linear algebra over a commutative ring, the discrete logarithm, and
the freeness of `Wbar[N]` — is now proven at composite level. -/
theorem det_frobeniusTorsionEnd_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    LinearMap.det (WeilPairing.frobeniusTorsionEnd q Wbar N) = (q : ZMod N) := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  obtain ⟨e, halt, hnd, hconj⟩ :=
    exists_weilPairing_frobenius_of_coprime q Wbar N hNq
  exact det_eq_of_conj_of_basis_fin_two b e halt hnd hconj

/-- **Rank-two: an alternating bilinear form transforms under an endomorphism by
its determinant** (PROVEN 2026-07-27), over an arbitrary COMMUTATIVE RING, for a
module with a basis indexed by `Fin 2`.

THIS IS THE COMPOSITE-LEVEL REPLACEMENT FOR `WeilPairing.pairing_map_eq_det_smul`,
AND IT IS SHARED INFRASTRUCTURE. That lemma (`EllipticCurve/WeilPairing.lean`) is
stated for a `2`-dimensional vector space over a FIELD, which is exactly why the
prime-level `WeilPairing.det_frobeniusTorsionEnd` does not generalise to composite
`N`: the coefficient ring at level `N` is `ZMod N`, which is not a field. The proof
here is the same argument with the rank hypothesis replaced by a given `Fin 2`
basis — nothing in it ever divides — so the field is not needed at all.

Consumers: `det_eq_of_pairing_scaling_fin_two` immediately below, and hence
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd`. It is equally the last
step of `det_frobeniusTorsionEnd_of_coprime` above, whose prime-level model
(`WeilPairing.det_frobeniusTorsionEnd`) closes with `WeilPairing.det_eq_of_conj`;
that leaf's owner should use `det_eq_of_pairing_scaling_fin_two` in its place and
supply the rank-two input from `nonempty_basis_nTorsion` above. -/
theorem pairing_map_eq_det_mul_fin_two {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (e : M →ₗ[R] M →ₗ[R] R)
    (halt : ∀ v, e v v = 0) (f : Module.End R M) (x y : M) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- skew-symmetry from the alternating property
  have hskew : ∀ v w : M, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add, add_zero] at h
    linear_combination h
  -- the matrix of `f` in the basis `b`
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  -- both sides are bilinear; compare on basis pairs
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ (f : M →ₗ[R] M) (f : M →ₗ[R] M) = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : M →ₗ[R] M →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

/-- **Rank-two: an endomorphism scaling a unit-valued alternating form by `c` has
determinant `c`** (PROVEN 2026-07-27), over an arbitrary commutative ring.

The composite-level replacement for `WeilPairing.det_eq_of_conj`, which needs a
field and `Module.rank = 2`. Nondegeneracy is asked for in the only form that
survives over a ring that is not a field: SOME value of the form is a UNIT (over a
field, "nonzero" and "a unit" agree, which is why `det_eq_of_conj` can ask for the
weaker-looking `∃ x y, e x y ≠ 0`). For the level-`N` Weil pairing this is exactly
the statement that `e(P, Q)` is a PRIMITIVE `N`-th root of unity on a basis `P, Q`
of `Wbar[N]`, i.e. that the pairing is perfect rather than merely nonzero. -/
theorem det_eq_of_pairing_scaling_fin_two {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (e : M →ₗ[R] M →ₗ[R] R)
    (halt : ∀ v, e v v = 0) (hnd : ∃ x y, IsUnit (e x y)) {f : Module.End R M} {c : R}
    (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h2 : LinearMap.det f * e x y = c * e x y :=
    (pairing_map_eq_det_mul_fin_two b e halt f x y).symm.trans (hc x y)
  have h3 : e x y * LinearMap.det f = e x y * c := by linear_combination h2
  exact hxy.mul_left_cancel h3

/-- **`Wbar(𝔽_q)` is the Frobenius-fixed locus of `Wbar(𝔽̄_q)`** (PROVEN
2026-07-27): the number of `𝔽_q`-points of `Wbar` equals the number of points of
the base change to `𝔽̄_q` fixed by the `q`-power Frobenius.

This is the "cheap first step" that the audit of
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` below identified, and it
is the GALOIS-DESCENT half of that leaf, now discharged. Read the right-hand side
as `#ker(1 − F)` acting on `Wbar(𝔽̄_q)`: it is what turns a point count into a
statement about the isogeny `1 − F`, which is the object a degree theory speaks
about.

The proof is a bijection, not an inequality-and-count:

* the base-change map `Wbar(𝔽_q) → Wbar(𝔽̄_q)` is injective
  (`Affine.Point.map_injective`);
* its image is Frobenius-stable for free — `Affine.Point.map_baseChange` says
  `map φ ∘ baseChange = baseChange` for any `𝔽_q`-algebra map `φ`, and
  `WeilPairing.frobAlgHom q` is one (that is the whole reason it was built as an
  `AlgHom` over `ZMod q`);
* conversely a fixed point is either `0` or `some x y h` with `x^q = x` and
  `y^q = y`, so `x` and `y` descend by `exists_algebraMap_eq_of_pow_card_eq` above
  (the fixed field of `x ↦ x^q` on `𝔽̄_q` is `𝔽_q`), and the nonsingularity
  descends with them along the injective `algebraMap`
  (`Affine.baseChange_nonsingular`).

No ellipticity is needed, and no finiteness: `Nat.card` of a bijection is an
equality whether or not either side is finite. -/
theorem natCard_affine_point_eq_natCard_frobFixed (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Nat.card Wbar.toAffine.Point =
      Nat.card {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
        WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
          (WeilPairing.frobAlgHom q) P = P} := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun P : Wbar.toAffine.Point =>
      (⟨WeierstrassCurve.Affine.Point.baseChange (W' := Wbar) (ZMod q)
            (AlgebraicClosure (ZMod q)) P,
        WeierstrassCurve.Affine.Point.map_baseChange (W' := Wbar)
          (WeilPairing.frobAlgHom q) P⟩ :
        {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
          WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
            (WeilPairing.frobAlgHom q) P = P})) ⟨?_, ?_⟩)
  · intro P₁ P₂ h
    exact WeierstrassCurve.Affine.Point.map_injective
      (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))) (Subtype.ext_iff.mp h)
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨0, Subtype.ext (map_zero _)⟩
    · rw [WeierstrassCurve.Affine.Point.map_some] at hP
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
      obtain ⟨hx, hy⟩ := hP
      obtain ⟨x₀, hx₀⟩ := exists_algebraMap_eq_of_pow_card_eq q
        (show x ^ q = x by rw [← frobAlgHom_apply q x]; exact hx)
      obtain ⟨y₀, hy₀⟩ := exists_algebraMap_eq_of_pow_card_eq q
        (show y ^ q = y by rw [← frobAlgHom_apply q y]; exact hy)
      subst hx₀
      subst hy₀
      have hns : (Wbar⁄(ZMod q)).Nonsingular x₀ y₀ :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := Wbar)
          (f := Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q)))
          (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))).injective x₀ y₀).mp h
      exact ⟨WeierstrassCurve.Affine.Point.some x₀ y₀ hns,
        Subtype.ext (WeierstrassCurve.Affine.Point.map_some
          (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))) hns)⟩

/-- **Rank-two Cayley–Hamilton** (PROVEN 2026-07-27): over an arbitrary
commutative ring, on a module with a `Fin 2` basis,
`f² = (tr f) • f − (det f) • 1`.

The companion of `det_one_sub_fin_two` above — that one expands `det (1 − f)`,
this one expands `f²` — and proven the same way, by transporting through
`LinearMap.toMatrix b b` and computing with `Matrix.trace_fin_two` and
`Matrix.det_fin_two`. Neither needs a field nor a `Module.rank` hypothesis, which
is exactly what makes them usable at COMPOSITE level `N`, where the coefficient
ring `ZMod N` is not a field. -/
theorem sq_eq_trace_smul_sub_det_smul_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M) (f : Module.End R M) :
    f * f = LinearMap.trace R M f • f - LinearMap.det f • (1 : Module.End R M) := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  have hmat : ∀ A : Matrix (Fin 2) (Fin 2) R,
      A * A = Matrix.trace A • A - Matrix.det A • (1 : Matrix (Fin 2) (Fin 2) R) := by
    intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
      ring
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul, map_sub, map_smul, map_smul, LinearMap.toMatrix_one,
    LinearMap.trace_eq_matrix_trace R b f, ← LinearMap.det_toMatrix b f]
  exact hmat _

/-- **A scalar that kills an invertible endomorphism is zero** (PROVEN
2026-07-27), on a module with a `Fin 2` basis.

Over a ring that is not a field this needs the invertibility, not merely
`f ≠ 0`: in `Module.End (ZMod 4) (ZMod 4)²` the scalar `2` kills the
endomorphism `2 • 1` without being zero. Multiplying by `f⁻¹` reduces to
`c • 1 = 0`, and evaluating at a basis vector reduces that to `c = 0`. -/
theorem eq_zero_of_smul_eq_zero_of_isUnit_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M) {f : Module.End R M}
    (hf : IsUnit f) {c : R} (hc : c • f = 0) : c = 0 := by
  obtain ⟨u, hu⟩ := hf
  have h1 : c • (1 : Module.End R M) = 0 := by
    have h0 : (c • f) * (↑u⁻¹ : Module.End R M) = 0 := by rw [hc, zero_mul]
    rw [smul_mul_assoc, ← hu, u.mul_inv] at h0
    exact h0
  have h2 : c • b 0 = 0 := by
    have h := congrArg (fun g : Module.End R M => g (b 0)) h1
    simpa using h
  have h3 := congrArg (fun v => b.repr v 0) h2
  simpa using h3

/-- **The Frobenius characteristic equation on points** (PROVEN 2026-07-28 over
`HasseBound.charEquation_frobeniusPointEnd`; opened 2026-07-27 by decomposing
`det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed` below, of which it is the
ENTIRE remaining content): on `Wbar(𝔽̄_q)` the `q`-power Frobenius satisfies

    F² P = a • F P − q • P     for every point `P`,  with  `a = q + 1 − #Wbar(𝔽_q)`.

This is Silverman *AEC* V.2.3.1 (the Frobenius satisfies a monic quadratic with
constant term `deg F = q`) together with V.1.1 (which evaluates the middle
coefficient as `q + 1 − #Wbar(𝔽_q)`), stated on points rather than in `End(E)` so
that it can be used without the `End` layer — which this tree has only over
`[CharZero F]` and which is refuted in characteristic `p`
(`Isogeny.isRationalMap_dualHom_is_false`).

WHAT IT COSTS, EXACTLY, AND WHAT IT DOES NOT. Split the statement in two:

* the RING IDENTITY `∃ c : ℤ, ∀ P, F² P = c • F P − q • P`. This needs NO degree
  theory: it is the endomorphism-algebra axis that
  `EllipticCurve/HasseBound.lean`'s ROUTE NOTES recommend, where it is step 1 of
  four and is written with the coefficient left existential.
* the NORMALISATION `c = q + 1 − #Wbar(𝔽_q)`, which is what naming the
  coefficient here adds. Given the ring identity, `(1 − F) ∘ ((1 − c) + F)` is
  multiplication by `1 − c + q`, so pinning `c` is exactly
  `deg(1 − F) = #ker(1 − F)` — the SEPARABILITY of `1 − F`, at the single point
  `(m, n) = (1, 1)`. `HasseBound.natCard_ker_one_sub_frobeniusPointEnd` (PROVEN)
  supplies `#ker(1 − F) = #Wbar(𝔽_q)`, so the separability is all that is left.

SO THIS LEAF IS *SHARED* WITH HASSE'S BOUND, BUT IS STRICTLY WEAKER THAN IT.
`HasseBound.exists_natCard_ker_degreeFormEnd` needs the same step 1 and then, for
general `(m, n)`, the SEPARATION `#ker ψ · #ker ψ' = d² ⟹ #ker ψ = d` (its route
note's step 4, the `ℓ`-adic argument plus the ordinary/supersingular dichotomy at
`ℓ = q`). The Lefschetz half below never meets that step, because it wants the
determinant on `Wbar[N]` — where the characteristic equation acts directly
through rank-two linear algebra — and not a kernel cardinality. That is the
difference between the two leaves, and it is why closing this one does not close
Hasse.

CORRECTION TO AN EARLIER VERSION OF THIS AUDIT, written a few hours before by the
same owner. It said the Lefschetz half "DOES need the degree theory, and it IS
shared with Hasse's bound", reasoning that `e(ψx, ψy) = e(x, y)^{deg ψ}` rests on
the dual isogeny. That was correct about the *pairing-shaped* route and wrong as
a claim about the leaf: the pairing route is not the only one, and the
characteristic equation reaches `det(1 − F | Wbar[N])` without any `deg`. The
lesson is the standing one — an irreducibility verdict is only as wide as the
axis the auditor searched, and that audit searched the pairing/dual axis only.

NOT VACUOUS, AND THE COEFFICIENT IS UNIQUE. If `a'` also satisfied the equation
then `(a − a') • F P = 0` for every `P`; `F` is injective
(`Affine.Point.map_injective`) and `Wbar(𝔽̄_q)` contains points of order larger
than any given integer (`Wbar[n] ≅ (ℤ/n)²` for `n` coprime to `q`), so
`a = a'`. Hence the coefficient carries genuine arithmetic and cannot be
satisfied by a junk value. Sanity check at a supersingular curve over `𝔽_p`,
where `#Wbar(𝔽_p) = p + 1` and so `a = 0`: the equation reads `F² = −p`, which is
the standard description of the supersingular Frobenius.

THE CHECK THAT WOULD REFUTE THE "missing" CLAIM: a statement of the Frobenius
characteristic equation, or of `deg(1 − F) = #E(𝔽_q)`, in `Fermat/`,
`.lake/packages/mathlib/` or `~/cs/FLT/`. `EllipticCurve/IsogenyTrace.lean`'s
`WeierstrassCurve.End.exists_charPoly` is the nearest thing and does NOT serve:
its whole `End` layer carries `[CharZero F]`, and its constant term is
`Isogeny.degree`, i.e. `Nat.card (ker ·)`, which is `1` for Frobenius rather than
`q`. THE AXIS SEARCHED was this development's isogeny, isogeny-trace and
Weil-pairing developments by binder (`CharZero`, `Fact p.Prime`) and by name,
plus `EllipticCurve/HasseBound.lean` as it stands on 2026-07-27.

WHERE THE CONTENT NOW LIVES (2026-07-28).  This declaration is no longer a leaf.
A proof stated HERE is unusable by the cluster that shares the same step: this
module `public import`s `EllipticCurve/HasseBound.lean`, so
`HasseBound.exists_natCard_ker_degreeFormEnd` — which needs the very same
characteristic equation as step 1 of its endomorphism-algebra route — is strictly
UPSTREAM and cannot consume anything declared here.  The equation is therefore
stated and pinned in `HasseBound.lean`, and this declaration is
`HasseBound.charEquation_frobeniusPointEnd` verbatim (`HasseBound.frobeniusPointEnd`
is `Affine.Point.map (frobAlgHom q)` by definition).

The three open leaves under it are all in `HasseBound.lean`:
`exists_sq_frobeniusPointEnd` (the ring identity `∃ c, F² = c·F − q`, the shared
step 1), `natCard_ker_degreeFormEnd_le` and `natCard_ker_degreeFormEnd_of_dvd`
(the two halves of the separation step, which are what NAME the coefficient).
Read their audits before attacking this cluster.  In particular, naming the
coefficient is NOT free given `natCard_ker_one_sub_frobeniusPointEnd`: that
theorem is the first equality of
`#Wbar(𝔽_q) = #ker([1] − F) = deg([1] − F) = 1 − c + q`, and the missing one is
the separability, carried by the two degree-form leaves. -/
theorem charEquation_point_map_frobAlgHom (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic]
    (P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point) :
    WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q) (WeilPairing.frobAlgHom q)
        (WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
          (WeilPairing.frobAlgHom q) P)
      = HasseBound.frobeniusTrace q Wbar •
          WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
            (WeilPairing.frobAlgHom q) P - (q : ℤ) • P :=
  HasseBound.charEquation_frobeniusPointEnd q Wbar P

/-- **The characteristic equation on the `N`-torsion** (PROVEN 2026-07-27 over
`charEquation_point_map_frobAlgHom` above): the same identity, read in
`Module.End (ZMod N) (Wbar[N])`.

The transfer is bookkeeping and nothing else, which is why the leaf is stated on
points: `Wbar[N]` is a submodule of the point group and
`WeilPairing.frobeniusTorsionEnd` is `Affine.Point.map (frobAlgHom q)` restricted
to it, so both sides have the same underlying point. The only real step is that
the `ZMod N`-action on an `N`-torsion group is the `ℤ`-action through the
reduction (`Int.cast_smul_eq_zsmul`), which is what turns the integer
coefficients `a` and `q` into elements of `ZMod N`. No coprimality is needed
here; it enters only below, where the determinant is read off. -/
theorem charEquation_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ) :
    WeilPairing.frobeniusTorsionEnd q Wbar N * WeilPairing.frobeniusTorsionEnd q Wbar N
      = ((HasseBound.frobeniusTrace q Wbar : ℤ) : ZMod N) •
          WeilPairing.frobeniusTorsionEnd q Wbar N - ((q : ℕ) : ZMod N) •
          (1 : Module.End (ZMod N)
            ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hstep := charEquation_point_map_frobAlgHom q Wbar x.1
  have hq : ((q : ℕ) : ZMod N) = ((q : ℤ) : ZMod N) := by push_cast; ring
  rw [hq]
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Int.cast_smul_eq_zsmul, Submodule.coe_sub,
    AddSubgroupClass.coe_zsmul]
  exact hstep

/-- **`det(1 − F) = #Wbar(𝔽_q)` on the `N`-torsion** (PROVEN 2026-07-27 over
`charEquation_point_map_frobAlgHom` above; opened the same day by decomposing
`exists_weilPairing_scaling_one_sub_frobeniusTorsionEnd` below, of which it is
the ENTIRE remaining content): for `N` coprime to `q`, the determinant of
`1 − F` on `Wbar[N]` is the reduction mod `N` of the number of `F`-fixed points
of `Wbar(𝔽̄_q)` — equivalently, by `natCard_affine_point_eq_natCard_frobFixed`
above, of `#Wbar(𝔽_q)`.

THE PROOF, WHICH IS RANK-TWO LINEAR ALGEBRA AND NOTHING ELSE. The characteristic
equation gives `F² = a • F − q • 1` on `Wbar[N]`; Cayley–Hamilton
(`sq_eq_trace_smul_sub_det_smul_fin_two` above) gives
`F² = (tr F) • F − (det F) • 1`; and `det F = q` is
`det_frobeniusTorsionEnd_of_coprime` above. Subtracting,
`(a − tr F) • F = 0`, and `F` is INVERTIBLE on `Wbar[N]` because its determinant
`q` is a unit in `ZMod N` — this is the one place the coprimality is used, and it
is what lets the scalar be cancelled over a ring that is not a field
(`eq_zero_of_smul_eq_zero_of_isUnit_fin_two`). So `tr F = a`, and
`det (1 − F) = 1 − tr F + det F = 1 − a + q = #Wbar(𝔽_q)` by
`det_one_sub_fin_two` and the definition of `HasseBound.frobeniusTrace`.

WHY THE LEAF MOVED HERE, AND WHAT THAT REMOVED. The leaf below used to bundle
TWO things: the existence of an alternating PERFECT `ZMod N`-valued pairing on
`Wbar[N]`, and the scaling of that pairing by the fixed-point count. The first
half was pure duplication — `exists_weilPairing_frobenius_of_coprime` above is
PROVEN and already produces exactly such a pairing, over the single
composite-level arithmetic leaf `exists_weilPairing_mu_of_coprime`, which is
separately owned. The second half is not about a pairing at all: by
`pairing_map_eq_det_mul_fin_two` above, EVERY alternating form on a rank-two
module is scaled by `LinearMap.det f` under any `f`, so the scaling constant is
forced by the endomorphism and the only content is which ring element it equals.
Hence this statement, which mentions no pairing — and, once stated that way, the
classical Frobenius characteristic equation closes it outright.

WHAT IS *NOT* NEEDED, contrary to the classical framing. The chain usually
written is `#Wbar(𝔽_q) = #ker(1 − F) = deg(1 − F) = det(1 − F | T_ℓ)`, whose last
two joints need a genuine degree of an isogeny (`#ker ψ = deg ψ` is the
separability of `1 − F`; `deg ψ = det(ψ | T_ℓ)` rests on the dual isogeny). None
of that is used here. The characteristic equation `F² = a • F − q` pins
`tr(F | Wbar[N])` directly, and `det (1 − F) = 1 − tr F + det F` finishes; the
only separability that survives is the normalisation of the coefficient `a`,
which is absorbed into the leaf above and is a single evaluation rather than a
theory. See that leaf's audit for the precise split, and for why the
Weil-pairing/dual-isogeny route — which does need the degree theory — is not the
only one.

RELATION TO HASSE'S BOUND, stated precisely because the two have been conflated
in both directions. `HasseBound.exists_natCard_ker_degreeFormEnd`
(`EllipticCurve/HasseBound.lean`, the only remaining input of
`hasse_bound_natCard_affine_point` above) needs the SAME characteristic equation
— it is step 1 of the endomorphism-algebra route recorded in its own docstring —
and then needs, for general `(m, n)`, the separation
`#ker ψ · #ker ψ' = d² ⟹ #ker ψ = d`, which is step 4 there and is still open.
So: the two leaves share their first input and diverge after it, and closing this
cluster does NOT close Hasse. The reverse also holds — proving Hasse's leaf would
not have closed this one, because a kernel cardinality does not determine a
determinant over `ZMod N`. Note as a free consistency check that
`natCard_ker_degreeFormEnd` at `(m, n) = (1, 1)` is already PROVEN, in this file
as `natCard_affine_point_eq_natCard_frobFixed` and in `HasseBound.lean` as
`natCard_ker_one_sub_frobeniusPointEnd`.

WHAT IS AVAILABLE IN THE TREE, checked 2026-07-27 rather than assumed.
`Isogeny.dualHom` and `Isogeny.dualHom_comp` (`EllipticCurve/Isogeny.lean`) DO
exist in characteristic `p` — `ψ̂ (ψ P) = ψ.degree • P` as a homomorphism of
point groups, with no `CharZero` binder — because they are Lagrange in `ker ψ`
plus descent along surjectivity. What carries `[CharZero F]`, and must, is
`isRationalMap_dualHom` / `Isogeny.dual`: that `ψ̂` is again a MORPHISM. The same
file refutes the characteristic-`p` version in `isRationalMap_dualHom_is_false`,
and the reason is exactly that `Isogeny.degree` is `Nat.card (ker ·)`, i.e. the
SEPARABLE degree (`frobIsog_degree = 1`, not `q`). So the tree has no
scheme-theoretic `deg` at all, and the group-level factorisation it does have is
not enough for the divisor-theoretic proof of pairing adjointness, which needs
`ψ̂` rational.

A ROUTE ALREADY REFUTED — recorded so that nobody re-searches it while attacking
the characteristic equation above. Computing `#ker(1 − F)` `ℓ`-part by `ℓ`-part
from Smith normal form on the Tate module recovers only the VALUATIONS
`v_ℓ(det)`, never the congruence: over `ZMod N` a kernel count sees an
endomorphism only through `gcd(dᵢ, N)` for its elementary divisors, so it cannot
see that `det(1 − F | T_ℓ)` is a rational integer independent of `ℓ` and
POSITIVE. Positivity is not group theory — for a bare group endomorphism `#ker`
and `det` agree only up to sign. That is also why a proof of Hasse's leaf would
not have given this one. -/
theorem det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    LinearMap.det (1 - WeilPairing.frobeniusTorsionEnd q Wbar N) =
      ((Nat.card {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
          WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
            (WeilPairing.frobAlgHom q) P = P} : ℕ) : ZMod N) := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  haveI : Module.Finite (ZMod N)
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) :=
    Module.Finite.of_basis b
  haveI : Module.Free (ZMod N)
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) :=
    Module.Free.of_basis b
  have hdet : LinearMap.det (WeilPairing.frobeniusTorsionEnd q Wbar N) = ((q : ℕ) : ZMod N) :=
    det_frobeniusTorsionEnd_of_coprime q Wbar N hNq
  have hchar := charEquation_frobeniusTorsionEnd q Wbar N
  have hCH := sq_eq_trace_smul_sub_det_smul_fin_two b (WeilPairing.frobeniusTorsionEnd q Wbar N)
  rw [hCH, hdet] at hchar
  have hkey : (((HasseBound.frobeniusTrace q Wbar : ℤ) : ZMod N) -
      LinearMap.trace (ZMod N) _ (WeilPairing.frobeniusTorsionEnd q Wbar N)) •
      WeilPairing.frobeniusTorsionEnd q Wbar N = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact (sub_left_inj.mp hchar).symm
  have hunit : IsUnit (WeilPairing.frobeniusTorsionEnd q Wbar N) := by
    rw [LinearMap.isUnit_iff_isUnit_det, hdet]
    exact (ZMod.isUnit_iff_coprime q N).mpr hNq.symm
  have htr : LinearMap.trace (ZMod N) _ (WeilPairing.frobeniusTorsionEnd q Wbar N)
      = ((HasseBound.frobeniusTrace q Wbar : ℤ) : ZMod N) :=
    (sub_eq_zero.mp (eq_zero_of_smul_eq_zero_of_isUnit_fin_two b hunit hkey)).symm
  rw [det_one_sub_fin_two b (WeilPairing.frobeniusTorsionEnd q Wbar N), htr, hdet,
    ← natCard_affine_point_eq_natCard_frobFixed q Wbar, HasseBound.frobeniusTrace]
  push_cast
  ring

/-- **The level-`N` Weil pairing, scaled by the degree of `1 − F`** (PROVEN
2026-07-27 over `det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed`
immediately above together with the PROVEN
`exists_weilPairing_frobenius_of_coprime`; opened the same day by decomposing
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` below, of which it is
the ENTIRE remaining content): for `N` coprime to `q` there is an alternating,
PERFECT (`ZMod N`-valued, unit somewhere) pairing on `Wbar[N]` which the
endomorphism `1 − F` scales by `#{P ∈ Wbar(𝔽̄_q) : F P = P}`.

THE PROOF IS THREE LINES, AND THAT IS THE POINT. The pairing is the one
`exists_weilPairing_frobenius_of_coprime` above already builds; its Frobenius
clause is discarded here (`1 − F` is a different endomorphism), and the scaling
clause is not an extra property of the pairing at all —
`pairing_map_eq_det_mul_fin_two` scales EVERY alternating form on a rank-two
module by `LinearMap.det`. So the arithmetic all sits in the determinant leaf
above; read its audit before attacking this cluster.

WHAT THIS IS. It is the level-`N` Weil pairing `e_N : Wbar[N] × Wbar[N] → μ_N`
(transported to `ZMod N` by a discrete logarithm, which is available because
`N` is coprime to `q` so `μ_N(𝔽̄_q)` is cyclic of order `N`), together with the
single classical compatibility

    e_N(ψ x, ψ y) = e_N(x, y) ^ (deg ψ)          [Silverman AEC III.8.2]

specialised to `ψ = 1 − F`. The scaling constant is written as the FIXED-POINT
COUNT rather than as `deg(1 − F)` because those are equal — and their equality is
the *separability* of `1 − F`: `deg ψ = #ker ψ` holds exactly for separable `ψ`,
`F` itself is purely inseparable (so `#ker F = 1 ≠ q = deg F`, the defect that
`EllipticCurve/Isogeny.lean`'s `frobIsog_degree` records), and `1 − F` is
separable because `d(1 − F) = 1 ≠ 0`. Writing it as the count puts that
asymmetry where a prover must confront it rather than hiding it behind a `deg`
that this tree does not have.

That framing is right about the mathematics and turned out to be the WRONG guide
to the proof, which is worth recording. The route it points at — build the
level-`N` pairing, then its degree compatibility — needs the dual isogeny in
characteristic `p` and is genuinely blocked. The route actually taken above needs
neither: the Frobenius characteristic equation pins `tr(F | Wbar[N])` and
rank-two linear algebra does the rest, so the separability enters only as the
normalisation of one integer coefficient. Both statements are true; only one of
them is attackable in this tree.

NOT VACUOUS. Dropping the unit-valued clause would make the leaf trivial (take
`e = 0`), and dropping the scaling clause would make it independent of `F`. With
both, the leaf pins `det(1 − F | Wbar[N])` to the point count — see the assembly
below, which is three lines over `det_eq_of_pairing_scaling_fin_two`.

MACHINERY. Everything this statement needs beyond the determinant leaf is proven
and generic: `exists_weilPairing_frobenius_of_coprime` for the pairing (itself
over the composite-level arithmetic leaf `exists_weilPairing_mu_of_coprime`),
`nonempty_basis_nTorsion` for the rank-two input at every `N` coprime to `q`, and
`pairing_map_eq_det_mul_fin_two` / `det_eq_of_pairing_scaling_fin_two` for the
linear algebra, which hold over an arbitrary commutative ring so that composite
`N` is not an obstruction. The determinant leaf above is PROVEN, so the only
sorry left under this whole cluster is `charEquation_point_map_frobAlgHom` — the
Frobenius characteristic equation on points — plus the separately owned
composite-level pairing `exists_weilPairing_mu_of_coprime`. Read the
characteristic equation's audit before attacking either; in particular it records
why the dual-isogeny route is not needed and how the leaf relates to
`HasseBound`. -/
theorem exists_weilPairing_scaling_one_sub_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ) (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
        ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
        ZMod N,
      (∀ v, e v v = 0) ∧ (∃ x y, IsUnit (e x y)) ∧
      ∀ x y, e ((1 - WeilPairing.frobeniusTorsionEnd q Wbar N) x)
            ((1 - WeilPairing.frobeniusTorsionEnd q Wbar N) y)
          = ((Nat.card {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
                WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
                  (WeilPairing.frobAlgHom q) P = P} : ℕ) : ZMod N) * e x y := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  obtain ⟨e, halt, hnd, -⟩ := exists_weilPairing_frobenius_of_coprime q Wbar N hNq
  exact ⟨e, halt, hnd, fun x y => by
    rw [pairing_map_eq_det_mul_fin_two b e halt
        (1 - WeilPairing.frobeniusTorsionEnd q Wbar N) x y,
      det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed q Wbar N hNq]⟩

/-- **The Lefschetz congruence: `#Wbar(𝔽_q) ≡ det(1 − F)` on `Wbar[N]`** (PROVEN
2026-07-27 over `exists_weilPairing_scaling_one_sub_frobeniusTorsionEnd` and
`natCard_affine_point_eq_natCard_frobFixed` above; itself opened the same day by
decomposing `trace_frobeniusTorsionEnd_eq_natCard` below, of which it is the
ENTIRE remaining arithmetic content).

THE CONTENT. The classical chain is
`#Wbar(𝔽_q) = #ker(1 − F) = deg(1 − F) = det(1 − F | T_ℓ)`, the middle step
because `1 − F` is separable and the last because the degree of an isogeny is
the determinant of its action on the Tate module; reducing mod `N` gives this
statement. Every ingredient of that chain is a statement about the point count
alone — no trace, no `ZMod N`-linear algebra — which is exactly why the trace
leaf below can be assembled from this plus `det F = q` by pure rank-two linear
algebra (`det_one_sub_fin_two`).

Stating the Lefschetz half as a DETERMINANT rather than as a trace is
deliberate: `det(1 − F)` is what a degree theory produces directly, whereas the
trace only appears after expanding the characteristic polynomial. The
expansion is now done once, generically, in `det_one_sub_fin_two`.

HOW THE 2026-07-27 DECOMPOSITION SPLITS IT, and what each half cost. The chain
above has exactly two joints, and they are separated here:

* the FIRST equality `#Wbar(𝔽_q) = #ker(1 − F)` is Galois descent and needed no
  new theory — it is `natCard_affine_point_eq_natCard_frobFixed` above, PROVEN,
  as an explicit bijection over `exists_algebraMap_eq_of_pow_card_eq`. The old
  audit here flagged it as "separately available and cheap"; that was right.
* the REST — `#ker(1 − F) = deg(1 − F) = det(1 − F)` — is
  `exists_weilPairing_scaling_one_sub_frobeniusTorsionEnd` above, now PROVEN, and
  through it the single leaf
  `det_one_sub_frobeniusTorsionEnd_eq_natCard_frobFixed` above, which carries the
  whole of it. Read that leaf's audit before attacking this cluster.

WHAT WAS NEEDED, after two corrections on 2026-07-27 that are worth keeping
because they went in opposite directions. The original note said no `deg`
function was needed; a second pass reversed it, on the ground that the residue
leaf's Weil-pairing shape hides the degree theory inside its scaling clause
(`e(ψx, ψy) = e(x, y)^{deg ψ}` IS the isogeny-degree compatibility, which rests
on the dual isogeny, absent in characteristic `p`). That reversal was right about
the pairing route and wrong about the leaf, and the third pass — which is what is
in the file — resolves it: with the pairing factored out into the PROVEN
`exists_weilPairing_frobenius_of_coprime`, the residue is a bare DETERMINANT
identity, and a determinant on `Wbar[N]` is reachable from the Frobenius
CHARACTERISTIC EQUATION `F² = a·F − q` by rank-two linear algebra, with no `deg`
anywhere. So the original note was correct after all, for a reason it did not
give.

The one remaining leaf under this whole cluster is therefore
`charEquation_point_map_frobAlgHom` above. It is SHARED with
`hasse_bound_natCard_affine_point` — it is step 1 of the endomorphism-algebra
route recorded in `HasseBound.exists_natCard_ker_degreeFormEnd`'s docstring — but
only shared, not equivalent: Hasse needs in addition the separation step for
general `(m, n)`, which the Lefschetz half never meets. Everything else here is
generic (`pairing_map_eq_det_mul_fin_two`, `det_eq_of_pairing_scaling_fin_two`,
`sq_eq_trace_smul_sub_det_smul_fin_two`, `det_one_sub_fin_two`, all over an
arbitrary commutative ring so that composite `N` is not an obstruction). -/
theorem natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ((Nat.card Wbar.toAffine.Point : ℤ) : ZMod N) =
      LinearMap.det (1 - WeilPairing.frobeniusTorsionEnd q Wbar N) := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  obtain ⟨e, halt, hnd, hsc⟩ :=
    exists_weilPairing_scaling_one_sub_frobeniusTorsionEnd q Wbar N hNq
  rw [natCard_affine_point_eq_natCard_frobFixed q Wbar,
    det_eq_of_pairing_scaling_fin_two b e halt hnd hsc]
  push_cast
  ring

/-- **The Frobenius trace on the `N`-torsion is the point-count trace**
(PROVEN 2026-07-27 over `det_frobeniusTorsionEnd_of_coprime` and
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` immediately above;
itself opened the same day by decomposing
`hasseWeil_trace_frobeniusTorsionEnd` below): for `N` COPRIME TO `q`, the
trace of the `q`-power Frobenius on `Wbar[N]` is the reduction mod `N` of the
rational integer `q + 1 − #Wbar(𝔽_q)`.

This is the LEFSCHETZ half, and it is the exact companion of
`WeilPairing.det_frobeniusTorsionEnd` (PROVEN, from the Weil pairing: the
determinant is `q`) — same operator, same module, the other coefficient of the
same characteristic polynomial. Together the two say
`char(F | Wbar[N]) = X² − aX + q` over `ZMod N`.

Proof (not formalised): `#Wbar(𝔽_q) = #ker(1 − F) = deg(1 − F)` — the middle
equality because `1 − F` is separable — together with the quadratic expansion
`deg(1 − F) = 1 − tr(F) + deg(F) = 1 − tr(F) + q` of the degree form. That
identifies `a := q + 1 − #Wbar(𝔽_q)` with `tr(F)` in `ℤ`; its reduction is the
trace on `Wbar[N]` because for `N` coprime to `q` the module `Wbar[N]` is free
of rank `2` over `ZMod N` and the characteristic polynomial of `F` on it is
the reduction of the integral one.

**COPRIMALITY IS LOAD-BEARING, AND `q ≠ N` IS NOT ENOUGH — this leaf's
predecessor was FALSE for that reason.** See the falsity audit in
`hasseWeil_trace_frobeniusTorsionEnd`'s docstring immediately below for the
explicit counterexample at `q = 5`, `N = 25`. The short version: at `N = q^k`
with `k ≥ 2` the module `Wbar[N]` is NOT free of rank `2` — for an ordinary
curve it is free of rank `1`, Frobenius acts on it by the `q`-adic UNIT ROOT,
and that unit root is not congruent mod `q²` to any integer of square `≤ 4q`.

MACHINERY: as for `hasse_bound_natCard_affine_point` above — the point count
is available, the degree form and `#E(𝔽_q) = deg(1 − F)` are not. This half
additionally needs the freeness of `Wbar[N]` over `ZMod N` for `N` coprime to
`q`, which is the same statement `WeilPairing.det_frobeniusTorsionEnd` already
relies on — and which is now PROVEN in general as `nonempty_basis_nTorsion`
above.

HOW THE DECOMPOSITION SPLITS THE WORK. The two leaves above are genuinely
independent and neither carries any of this leaf's linear algebra:

* `det_frobeniusTorsionEnd_of_coprime` — the Weil-pairing half, `det F = q`.
  A direct generalisation of the PROVEN prime-level
  `WeilPairing.det_frobeniusTorsionEnd`, and now itself PROVEN
  (2026-07-27) over the single arithmetic leaf
  `exists_weilPairing_mu_of_coprime` (the `μ_N`-valued Weil pairing at
  composite level); all the linear algebra between the two is proven.
* `natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` — the Lefschetz
  half, `#Wbar(𝔽_q) ≡ det(1 − F)`. Mentions no trace.

and the assembly is `det(1 − F) = 1 − tr F + det F` in rank two
(`det_one_sub_fin_two`, PROVEN generically over any commutative ring), which
is where the freeness input `nonempty_basis_nTorsion` is consumed. -/
theorem trace_frobeniusTorsionEnd_eq_natCard (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    (((q : ℤ) + 1 - (Nat.card Wbar.toAffine.Point : ℤ) : ℤ) : ZMod N) =
      LinearMap.trace (ZMod N)
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)
        (WeilPairing.frobeniusTorsionEnd q Wbar N) := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  have h1 := det_one_sub_fin_two b (WeilPairing.frobeniusTorsionEnd q Wbar N)
  rw [det_frobeniusTorsionEnd_of_coprime q Wbar N hNq,
    ← natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd q Wbar N hNq] at h1
  push_cast at h1 ⊢
  linear_combination -h1

/-- **Hasse–Weil for the `q`-power Frobenius on the `N`-torsion** (PROVEN
2026-07-27 over the two leaves immediately above; itself opened earlier the
same day by decomposing
`exists_integerFrobeniusTrace_of_potentiallyGoodReduction` below): the
trace of the `q`-power Frobenius acting on the `N`-torsion of an elliptic
curve over `𝔽_q` (`N` COPRIME TO `q`) is the reduction of a RATIONAL INTEGER
`a` with `a² ≤ 4q`.

The witness is `a := q + 1 − #Wbar(𝔽_q)`, so the two halves split cleanly:
`hasse_bound_natCard_affine_point` is the bound and mentions no torsion at
all, and `trace_frobeniusTorsionEnd_eq_natCard` is the congruence and needs no
inequality. The assembly is the anonymous constructor.

**FALSITY AUDIT OF 2026-07-27 — THE PREVIOUS HYPOTHESIS `q ≠ N` MADE THIS
STATEMENT FALSE, AND IT HAS BEEN REPAIRED TO `Nat.Coprime N q`.**

Counterexample to the old statement, verified in PARI/GP. Take `q = 5` and
`Wbar : y² = x³ + x` over `𝔽_5`, which is elliptic (`Δ = −64 ≡ 1`) and has
`#Wbar(𝔽_5) = 4`, hence `a_true = 5 + 1 − 4 = 2`; since `5 ∤ 2` it is
ORDINARY. Take `N = 25`, which satisfies the old hypothesis `q ≠ N` (`5 ≠ 25`)
but is not coprime to `q`. Then:

* `Wbar[25](𝔽̄_5) ≅ ℤ/25` — for an ordinary curve the `q`-power torsion is the
  étale quotient, of rank ONE, not two. So as a `ZMod 25`-module it is free of
  rank `1` and `LinearMap.trace` is simply the scalar by which `F` acts.
* `F` acts on the étale part by the `5`-adic UNIT ROOT `α` of `X² − 2X + 5`.
  Solving `α = 2 + 5t` gives `10t + 5 ≡ 0 (mod 25)`, i.e. `t ≡ 2 (mod 5)`, so
  `α ≡ 12 (mod 25)`.
* The integers `a` with `a² ≤ 4·5 = 20` are exactly `−4 … 4`, and NONE of them
  is `≡ 12 (mod 25)`.

So no `a` exists, and the old statement was false. This is not an artefact of
`N` being a prime power in general: the same computation kills every `N = q^k`,
`k ≥ 2`, for which `a_true − q·(a_true⁻¹ mod q)` falls outside `[−2√q, 2√q]`.

**Why the repair is the right one and costs the consumer nothing.** The single
consumer, `exists_integerFrobeniusTrace_of_potentiallyGoodReduction` below, has
`hN : N.Prime` and `hq : q.Prime` and `hqN : q ≠ N` all in scope, so it
supplies `Nat.Coprime N q` by `(Nat.coprime_primes hN hq).mpr (Ne.symm hqN)` —
one term, no new obligation, no change to the consumer's own statement. The old
hypothesis was an oversight in which "distinct primes" was written as the
weaker "distinct naturals"; `Nat.Coprime N q` is the sharp hypothesis, and it
still covers the degenerate `N = 1` (where `ZMod 1` is trivial and `a = 0`
works). THE CHECK THAT WOULD REFUTE THIS REPAIR: an `N` coprime to `q` at which
`Wbar[N]` fails to be free of rank `2` over `ZMod N`. There is none — that is
exactly what coprimality buys. -/
theorem hasseWeil_trace_frobeniusTorsionEnd (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * (q : ℤ) ∧
      (a : ZMod N) = LinearMap.trace (ZMod N)
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N)
        (WeilPairing.frobeniusTorsionEnd q Wbar N) :=
  ⟨(q : ℤ) + 1 - (Nat.card Wbar.toAffine.Point : ℤ),
    hasse_bound_natCard_affine_point q Wbar,
    trace_frobeniusTorsionEnd_eq_natCard q Wbar N hNq⟩

/-- **The integral Frobenius trace at a prime of potentially good
reduction** (PROVEN 2026-07-27 over the two leaves immediately above;
Mazur 1978 §5, [Michaud-Jacobs, proof of Prop. 4.3]). This is the leaf CUT
OUT of `exists_frobeniusTrace_of_potentiallyGoodReduction` (2026-07-27):
at a prime `q ∉ {2, N}` where `E` has potentially good reduction, the trace
of the mod-`N` representation at the global arithmetic Frobenius is the
reduction of a RATIONAL INTEGER `a` obeying the Hasse–Weil bound
`a² ≤ 4q`.

Everything else that the parent leaf used to bundle is now PROVEN there:
the eigenvalue step (`mazurIsogeny_eigenvalue_quadratic_of_finrank_two`
above) and the determinant step
(`WeilPairing.det_galoisRep_eq_cyclotomic` composed with
`GaloisRepresentation.cyclotomicCharacterModL_globalFrob`). So this
statement is exactly the arithmetic input and nothing else.

The proof is now pure conjugation bookkeeping over the two leaves above:
`exists_frobenius_reduction_model_of_potentiallyGoodReduction` puts
`ρ_{E,N}(σ_q)` into the `q`-Frobenius conjugacy class of an elliptic curve
`Wbar/𝔽_q`, and `hasseWeil_trace_frobeniusTorsionEnd` bounds THAT
Frobenius's trace; `LinearMap.trace_conj'` carries the trace across the
conjugating equivalence. It mirrors `WeilPairing.det_galoisRep_globalFrob`
line for line with `trace` in place of `det`.

`hN23` is NOT used: nothing in this argument needs `N ≥ 23`. It is kept
because the statement is consumed with it in scope, and underscored so
that the emptiness is mechanically visible rather than merely asserted.

FAITHFULNESS CONCERN OF 2026-07-27 — **RESOLVED. The statement is TRUE AS
WRITTEN, for EVERY Frobenius lift; it needs no semistability-defect
hypothesis and no exclusion of `j(E) ∈ {0, 1728}`.**

The concern read: `GaloisRepresentation.globalFrob` is well-defined only
up to inertia at `q` (its own docstring says so, adding that its
statements "concern places where the representations at hand are
unramified"), and at potentially-good-but-NOT-good reduction `ρ_{E,N}` is
precisely ramified there — so different lifts `σ` and `στ` (`τ ∈ I_q`) can
have different traces. For semistability defect `e ≤ 2` that is harmless
(the traces are `±a`), but for `e ∈ {3, 4, 6}` — which forces
`j(E) ∈ {0, 1728}` — the trace of a lift outside `G_K` was recorded as
`ζ_e · a`, whose congruence mod `N` to a rational integer of square
`≤ 4q` "is not automatic".

**The error is in that last step, and it is instructive.** `ζ_e · a` is
the trace computed in the CM FIELD, and from an algebraic-integer trace
one cannot conclude that no RATIONAL integer of square `≤ 4q` has the same
reduction mod `N`. Computing in `End(Ẽ)` instead settles it outright.
Write `σ = τ σ_K` with `K/ℚ_q` finite totally ramified realising good
reduction, `σ_K ∈ G_K` a Frobenius (available because `K` has residue
field `𝔽_q`) and `τ ∈ I_q`. Then `ρ(σ_K) = F`, the `q`-power Frobenius of
`Ẽ/𝔽_q`, and `ρ(τ) = φ ∈ Aut(Ẽ_{𝔽̄_q})` by Serre–Tate. So
`ρ(σ) = φ ∘ F` is an ENDOMORPHISM of `Ẽ_{𝔽̄_q}`, of degree
`deg φ · deg F = 1 · q = q`. Every endomorphism `α` of an elliptic curve
satisfies `α² − tr(α)·α + deg(α) = 0` with `tr(α) ∈ ℤ`, and
`tr(α)² ≤ 4·deg(α)`, because `deg(m − nα) = m² − mn·tr(α) + n²·deg(α) ≥ 0`
for all integers `m, n`. Take `a := tr(φ ∘ F)`: then `a ∈ ℤ`, `a² ≤ 4q`,
and `a mod N` is the trace of `ρ(σ)` on `E[N]`. The lift was arbitrary;
changing it changes `φ`, hence changes `a`, but never the EXISTENCE of
`a`. In the very case the concern feared — `j = 0`, `e = 6` — the witness
is explicit: `φ ∘ F = ζ₆ π` in `ℤ[ζ₃]` with `N(ζ₆ π) = N(π) = q`, so
`a = Tr_{ℚ(ζ₃)/ℚ}(ζ₆ π)` is a rational integer with `a² ≤ 4q` because
`|ζ₆ π| = √q`. No circular appeal to the available `j`-invariants is
needed, and the vacuity argument the old note fell back on (FAITHFULNESS
AUDIT B on `potentiallyGoodReduction_of_isogenyCharacter`) is not used.

**What the concern got right, and what survives it.** The traces at
different lifts really are different, so no consumer may treat `a` as
canonical — and this statement correctly returns `a` EXISTENTIALLY rather
than as a function of `E` and `q`. The decomposition above records the
dependence structurally: the twist `Wbar` produced by
`exists_frobenius_reduction_model_of_potentiallyGoodReduction` is the one
that depends on the lift, and its Frobenius trace is the `a` that comes
out. The concern was therefore a correct reading of a real
non-canonicity, mislocated as a falsity.

**THE CHECK THAT WOULD REFUTE THIS RESOLUTION**: exhibit
`φ ∈ Aut(Ẽ_{𝔽̄_q})` with `deg(φ ∘ F) ≠ q`, or an endomorphism of an
elliptic curve whose reduced trace is not a rational integer. Both are
false — the first because `deg` is multiplicative and automorphisms have
degree `1`, the second because `End` is an order in an imaginary quadratic
field or a quaternion algebra, where `α + α^† ∈ ℤ`. THE AXIS SEARCHED:
the local one at `q` (models over `ℚ_q`, inertia, `End(Ẽ)`); the
resolution does not depend on anything global, which is why it is
available to a prover of this leaf without circularity.

MACHINERY AUDIT (2026-07-27, superseding the previous one — which was
right that Hasse–Weil is absent and STALE on the rest). The three items it
listed have been re-cut into the two leaves above, where the current
audits live; read those, not this paragraph. Two corrections of record:
`EllipticCurve/TorsionReduction.lean` IS on `main` (the previous note said
it existed "only on the unreleased branch `flt-lean-132`"), and its point
counting is available; and `WeierstrassCurve.End.exists_charPoly` — which
looks like exactly the Hasse bound and is PROVEN — must NOT be used for
Frobenius, because its degree is the SEPARABLE degree. The full argument
is in `hasse_bound_natCard_affine_point`'s docstring above. What is NOT
missing and must not be rebuilt is unchanged: the representation
`WeierstrassCurve.galoisRep`, `WeilPairing.det_galoisRep_eq_cyclotomic`,
and the good-reduction transfer
`WeilPairing.exists_frobenius_reduction_model`.

STATE OF THE DECOMPOSITION AS OF 2026-07-27 (second cut of the same day —
both of the two leaves this statement was opened over are now themselves
PROVEN over sharper leaves, so the FOUR open leaves below are the whole
remaining obligation of this subtree):

* `exists_frobeniusAut_of_potentiallyGoodReduction` — the local content:
  a totally ramified good model at `q` (WILD at `q = 3`, which the consumers
  use) plus Serre–Tate. Its docstring also records that the global/Chebotarev
  axis is a DEAD END here, with the reason.
* `exists_twist_frobeniusTorsionEnd` — twists over `𝔽_q`. Elementary and
  self-contained; needs no number theory at all.
* `hasse_bound_natCard_affine_point` — Hasse's `|q + 1 − #Wbar(𝔽_q)| ≤ 2√q`.
  Mentions no torsion.
* `trace_frobeniusTorsionEnd_eq_natCard` — the Lefschetz congruence. Mentions
  no inequality.

A NOTE ON THE `hqN` HYPOTHESIS, because it caught a real falsity. The
Hasse–Weil leaf used to be stated with `q ≠ N`, which is FALSE at `N = q^k`
for `k ≥ 2`; it now takes `Nat.Coprime N q`, which this statement supplies
from `hN`, `hq` and `hqN` in one term. See that leaf's FALSITY AUDIT for the
explicit counterexample. -/
theorem WeierstrassCurve.exists_integerFrobeniusTrace_of_potentiallyGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ}
    (hN : N.Prime) (_hN23 : 23 ≤ N)
    (hpg : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ N → 0 ≤ padicValRat q E.j)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * (q : ℤ) ∧
      (a : ZMod N) =
        LinearMap.trace (ZMod N)
          ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N)
          (E.galoisRep N hN.pos (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) := by
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Wbar, hell, ψ, hψ⟩ :=
    E.exists_frobenius_reduction_model_of_potentiallyGoodReduction hN hq hq2 hqN
      (hpg q hq hq2 hqN)
  haveI := hell
  -- `N` and `q` are DISTINCT PRIMES, hence coprime; `q ≠ N` alone would not do
  -- (see the falsity audit on `hasseWeil_trace_frobeniusTorsionEnd`).
  obtain ⟨a, ha, hatr⟩ := hasseWeil_trace_frobeniusTorsionEnd q Wbar N
    ((Nat.coprime_primes hN hq).mpr (Ne.symm hqN))
  refine ⟨a, ha, ?_⟩
  -- the representation at `σ_q` is the `q`-Frobenius conjugated by `ψ`
  have hρ : (E.galoisRep N hN.pos
      (GaloisRepresentation.globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat) : Module.End (ZMod N)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N)) =
      ψ.symm.conj (WeilPairing.frobeniusTorsionEnd q Wbar N) := by
    apply LinearMap.ext
    intro x
    show _ = ψ.symm (WeilPairing.frobeniusTorsionEnd q Wbar N (ψ.symm.symm x))
    rw [LinearEquiv.symm_symm, ← hψ x, LinearEquiv.symm_apply_apply]
  rw [hρ, LinearMap.trace_conj']
  exact hatr

/-- **The Frobenius characteristic-polynomial relation** (PROVEN
2026-07-27 from `exists_integerFrobeniusTrace_of_potentiallyGoodReduction`
and `mazurIsogeny_eigenvalue_quadratic_of_finrank_two`; Mazur 1978 §5,
[Michaud-Jacobs, proof of Prop. 4.3]): at a prime `q ∉ {2, N}` of
potentially good reduction, the value `λ(σ_q)` of the isogeny character
at the global arithmetic Frobenius is a root, in `ZMod N`, of
`X² − aX + q` for some RATIONAL INTEGER `a` with `a² ≤ 4q`.

This is the ONE input the resultant elimination needs, and it is now the
only unproven ingredient of
`not_isogenyCharacter_of_isogenySignature_ne_six`. The companion input,
`χ_N(σ_q) = q`, is already available and PROVEN as
`GaloisRepresentation.cyclotomicCharacterModL_globalFrob`.

Proof (not formalised), in three steps.

1. *`λ(σ_q)` is an eigenvalue of `ρ_{E,N}(σ_q)`.* The subgroup `⟨g⟩` is
   Galois-stable of order `N`, so `g` spans a line in `E[N] ≅ (ZMod N)²`
   on which `Γ_ℚ` acts by `λ`; `hlam` says exactly that. Hence `λ(σ_q)`
   is a root of the characteristic polynomial of `ρ_{E,N}(σ_q)`, which
   is `X² − Tr ρ_{E,N}(σ_q) X + det ρ_{E,N}(σ_q)`.
2. *The determinant is `q`.* `det ρ_{E,N} = χ_N` by the Weil pairing, and
   `χ_N(σ_q) = q` by `cyclotomicCharacterModL_globalFrob` (PROVEN).
3. *The trace is an integer of absolute value `≤ 2√q`.* Since `E` has
   potentially good reduction at `q` — which is what `hpg` supplies, via
   `v_q(j(E)) ≥ 0` — it acquires good reduction over a finite extension
   `K/ℚ_q`, and `ρ_{E,N}` is unramified at `q` on inertia acting through
   a finite quotient; Serre–Tate (Invent. Math. 15 (1972), Thm 3) makes
   `Tr ρ_{E,N}(σ_q)` the reduction mod `N` of the trace of Frobenius
   `a_q(Ẽ) ∈ ℤ` of the good-reduction model `Ẽ/𝔽_{q^f}`, and Hasse–Weil
   bounds it by `2√q`.

MACHINERY AUDIT — **CORRECTED 2026-07-27; the previous version was
STALE and wrong on two of its three claims.** It read: "What does NOT
exist in this development is the mod-`N` Galois representation
`ρ_{E,N} : Γ_ℚ → GL₂(ZMod N)` attached to an elliptic curve over `ℚ`
together with its `det = χ_N` and its Néron–Ogg–Shafarevich / Serre–Tate
comparison with the reduced curve, nor the Hasse–Weil bound over a finite
field." In fact, re-checked by grep and by `#print axioms` against the
built module:

* the representation EXISTS — `WeierstrassCurve.galoisRep`
  (`EllipticCurve/Torsion.lean`), on `E[N]` as a `Module.End (ZMod N)`
  rather than a matrix group, publicly imported here;
* `det = χ_N` EXISTS and is PROVEN for a GENERAL `E/ℚ` —
  `WeilPairing.det_galoisRep_eq_cyclotomic`, publicly imported and
  already consumed twice inside this very file (at the
  `cyclotomicCharacterModL` triviality argument and at the
  Frey-curve character splitting);
* the Néron–Ogg–Shafarevich comparison EXISTS in the good-reduction case
  as `WeilPairing.exists_frobenius_reduction_model` (PROVEN, and its
  `#print axioms` is clean: `[propext, Classical.choice, Quot.sound]`);
* only the HASSE–WEIL bound, and the potentially-good-but-not-good
  reduction model, are genuinely absent.

Consequently steps 1 and 2 are now discharged HERE, and the residue was
isolated as `exists_integerFrobeniusTrace_of_potentiallyGoodReduction`
above — which is itself now PROVEN (2026-07-27) over two sharper leaves,
`exists_frobenius_reduction_model_of_potentiallyGoodReduction`
(Serre–Tate: `ρ(σ_q)` is the `q`-Frobenius of a TWIST over `𝔽_q`) and
`hasseWeil_trace_frobeniusTorsionEnd` (the bound on that Frobenius's
trace). Those two are the dispatchable leaves; read their audits before
attacking either. The FAITHFULNESS CONCERN that used to be recorded
against this whole cluster — `globalFrob` being defined only up to
inertia at a prime where `ρ` is ramified — is RESOLVED, not open: see the
resolution in `exists_integerFrobeniusTrace_of_potentiallyGoodReduction`'s
docstring. Its one-line form: `ρ(σ_q) = φ ∘ F` is an endomorphism of
degree `q` for EVERY lift, and `tr(α)² ≤ 4 deg(α)` holds for every
endomorphism, so the bound is lift-independent even though `a` is not.

FAITHFULNESS. `q ≠ 2` and `q ≠ N` are both genuinely needed: `q = 2` is
excluded because the formal-immersion input `hpg` is silent there, and
`q = N` because `χ_N(σ_N)` is not `N` (the cyclotomic character is
ramified at `N`). The bound is stated as `a² ≤ 4q` over `ℤ` rather than
`|a| ≤ 2√q` to keep it rational; the two are equivalent. -/
theorem WeierstrassCurve.exists_frobeniusTrace_of_potentiallyGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN23 : 23 ≤ N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hpg : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ N → 0 ≤ padicValRat q E.j)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqN : q ≠ N) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * (q : ℤ) ∧
      ((lam (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) : ZMod N)) ^ 2
        - (a : ZMod N) * ((lam (GaloisRepresentation.globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) : ZMod N))
        + ((q : ℕ) : ZMod N) = 0 := by
  classical
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hNpos : 0 < N := hN.pos
  have hodd : Odd N := hN.odd_of_ne_two (by omega)
  set σq := GaloisRepresentation.globalFrob
    hq.toHeightOneSpectrumRingOfIntegersRat
  set ρ := E.galoisRep N hNpos
  -- the eigenvector: `g` lies in the `N`-torsion and is nonzero
  have hgN : ((N : ℤ)) • g = 0 := by
    rw [natCast_zsmul, ← hg]
    exact addOrderOf_nsmul_eq_zero g
  have hgmem : g ∈ Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point (N : ℤ) :=
    (Submodule.mem_torsionBy_iff _ _).mpr hgN
  set G : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N := ⟨g, hgmem⟩
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hg
    omega
  have hG0 : G ≠ 0 := fun h => hg0 (congrArg Subtype.val h)
  -- the `N`-torsion is `2`-dimensional over `ZMod N`
  have hfr : Module.finrank (ZMod N)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N) = 2 :=
    Module.finrank_eq_of_rank_eq
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
        (Nat.cast_ne_zero.mpr hNpos.ne'))
  -- the `ZMod N`-action on the torsion is the `ℕ`-action through `val`
  have hsmulcoe : ∀ (c : ZMod N)
      (P : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion N),
      (c • P).1 = (c.val) • P.1 := by
    intro c P
    haveI : NeZero N := ⟨hNpos.ne'⟩
    conv_lhs => rw [← ZMod.natCast_rightInverse c]
    rw [Nat.cast_smul_eq_nsmul]
    simp
  -- STEP 1: `hlam` says exactly that `G` is an eigenvector with eigenvalue `λ(σ_q)`
  have heig : ρ σq G = ((lam σq : ZMod N)) • G := by
    refine Subtype.ext ?_
    show Affine.Point.map
      (σq : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g = _
    have hGval : G.1 = g := rfl
    rw [hlam σq, hsmulcoe, hGval]
    rfl
  -- STEP 2: the determinant is `q`, by the Weil pairing and the cyclotomic character
  have hdet : LinearMap.det (ρ σq) = ((q : ℕ) : ZMod N) := by
    have h1 : LinearMap.det (ρ σq) =
        ((GaloisRepresentation.cyclotomicCharacterModL N σq : (ZMod N)ˣ) : ZMod N) := by
      rw [WeilPairing.cyclotomicCharacterModL_eq_toZMod]
      exact WeilPairing.det_galoisRep_eq_cyclotomic E N hNpos hodd σq
    rw [h1, GaloisRepresentation.cyclotomicCharacterModL_globalFrob hq hqN]
  -- STEP 3: the trace is the reduction of a rational integer obeying Hasse–Weil
  obtain ⟨a, ha, hatr⟩ :=
    E.exists_integerFrobeniusTrace_of_potentiallyGoodReduction hN hN23 hpg hq hq2 hqN
  refine ⟨a, ha, ?_⟩
  have hquad := mazurIsogeny_eigenvalue_quadratic_of_finrank_two hfr (ρ σq) hG0 heig
  rw [← hdet, hatr]
  exact hquad

/-- **Signature `≠ 6` is impossible for `N ≥ 23`, `N ≠ 37`** (PROVEN
2026-07-26 from `exists_frobeniusTrace_of_potentiallyGoodReduction` and
the resultant elimination above; Mazur 1978 §5, in the form of
[Michaud-Jacobs, Prop. 4.3]). This is the ARITHMETIC leaf: no modular
curve, no class field theory, just Frobenius traces and a finite integer
computation.

Proof (not formalised). Fix a prime `q ∈ {3, 5}`; both differ from `2`
and from `N ≥ 23`, so `hpg` says `E` has potentially good reduction at
`q`. Let `σ_q` be a Frobenius at `q`. Then `λ(σ_q)` is a root mod `N` of
BOTH `X¹² − q^s` (by the signature hypothesis, since `χ_N(σ_q) = q`) and
`X² − Tr ρ_{E,N}(σ_q) X + q` (it is an eigenvalue of `ρ_{E,N}(σ_q)`,
whose determinant is `χ_N(σ_q) = q`). Potential good reduction at `q`
makes `Tr ρ_{E,N}(σ_q)` the reduction of a RATIONAL integer `a` with
`|a| ≤ 2√q` (Serre–Tate, Thm 3; Hasse–Weil after passing to the totally
ramified extension over which `E` has good reduction). Two polynomials
with a common root mod `N` have `N`-divisible resultant, so
`N ∣ R_{q,s} := lcm_{|a| ≤ 2√q} Res(X² − aX + q, X¹² − q^s)`.

The finite computation (values and factorisations in the section note
above; they must be recomputed IN-KERNEL, PARI/GP was only the searcher):
for `s ∈ {4, 8}`, `R(3,s)` has no prime factor `> 19`, contradicting
`N ≥ 23` outright. For `s ∈ {0, 12}`, the primes `> 19` dividing `R(3,s)`
are `{37, 97}` and those dividing `R(5,s)` are `{31,37,61,157,229}`;
their intersection is `{37}`, excluded by `hN37`.

`s = 6` is genuinely absent from the hypothesis rather than merely
untreated: `X² − aX + q` and `X¹² − q⁶` always share a root over `ℂ` for
some admissible `a` (already `a = 0` gives the common root `√−q`), so
`R(q,6) = 0` for every `q` and the divisibility is vacuous. That case is
the next leaf. -/
theorem WeierstrassCurve.not_isogenyCharacter_of_isogenySignature_ne_six
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN23 : 23 ≤ N) (hN37 : N ≠ 37)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hpg : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ N → 0 ≤ padicValRat q E.j)
    {s : ℕ} (hs : s ∈ ({0, 4, 8, 12} : Finset ℕ))
    (hsig : ∀ σ : Field.absoluteGaloisGroup ℚ,
      lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ s) :
    False := by
  haveI : Fact N.Prime := ⟨hN⟩
  have hq3 : Nat.Prime 3 := by norm_num
  have hq5 : Nat.Prime 5 := by norm_num
  -- The twelfth-power relation at a Frobenius, using `χ_N(σ_q) = q`
  -- (`cyclotomicCharacterModL_globalFrob`, PROVEN in `Chebotarev.lean`).
  have hpow : ∀ (q : ℕ) (hq : q.Prime), q ≠ N →
      ((lam (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) : ZMod N)) ^ 12
        = ((q : ℕ) : ZMod N) ^ s := by
    intro q hq hqN
    have h1 := hsig (GaloisRepresentation.globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)
    have h2 : ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩
        (GaloisRepresentation.globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) : (ZMod N)ˣ) : ZMod N)
        = ((q : ℕ) : ZMod N) :=
      @GaloisRepresentation.cyclotomicCharacterModL_globalFrob N q ⟨hN⟩ hq hqN
    have h3 := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) h1
    simpa [Units.val_pow_eq_pow_val, h2] using h3
  -- The characteristic-polynomial relation at `q = 3` and `q = 5`
  -- (the single deep input).
  obtain ⟨a3, ha3, hx3⟩ := E.exists_frobeniusTrace_of_potentiallyGoodReduction g hN hN23 hg
    lam hlam hpg hq3 (by norm_num) (by omega)
  obtain ⟨a5, ha5, hx5⟩ := E.exists_frobeniusTrace_of_potentiallyGoodReduction g hN hN23 hg
    lam hlam hpg hq5 (by norm_num) (by omega)
  -- The finite computation.
  refine mazurIsogeny_resultantElimination hN23 hN37 ?_ (by norm_num at ha3; linarith)
    (by norm_num at ha5; linarith) hx3 hx5 (hpow 3 hq3 (by omega)) (hpow 5 hq5 (by omega))
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hs

/-- **The trace relation at a non-inert prime is impossible** (PROVEN
2026-07-26 — the elementary core of [Michaud-Jacobs, Prop. 4.4], isolated
from every elliptic curve so that it can be kernel-checked on its own): if
`q` is prime, `4q < N`, and some integer `a` with `a² ≤ 4q` satisfies
`N ∣ a² − q` or `N ∣ a² − 4q`, then `False`.

Proof. In the first case `−q ≤ a² − q ≤ 3q`, so `|a² − q| < N` and the
divisibility forces `a² = q` (`Int.eq_zero_of_abs_lt_dvd`); in the second
`−4q ≤ a² − 4q ≤ 0`, so `|a² − 4q| < N` and `a² = 4q`, whence `a` is even,
`a = 2b`, and `b² = q`. Either way a prime is a perfect square, which
`Prime.not_isSquare` refutes.

This is exactly the step "`|Tr| ≤ 2√q` together with `4q < N` is
incompatible with `N ∣ Tr² − rq` for `r ∈ {1, 4}`". Note `N` is NOT assumed
prime: only `4q < N` is used, so the lemma is reusable at any modulus. -/
theorem mazurIsogeny_traceRelation_impossible {N q : ℕ} (hq : q.Prime)
    (hqN : 4 * q < N) {a : ℤ} (ha : a ^ 2 ≤ 4 * (q : ℤ))
    (hdvd : (N : ℤ) ∣ a ^ 2 - (q : ℤ) ∨ (N : ℤ) ∣ a ^ 2 - 4 * (q : ℤ)) : False := by
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hsq0 : (0 : ℤ) ≤ a ^ 2 := sq_nonneg a
  have hN4q : (4 : ℤ) * (q : ℤ) < (N : ℤ) := by exact_mod_cast hqN
  have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnsq : ∀ b : ℤ, b ^ 2 ≠ (q : ℤ) := fun b hb =>
    hqprime.not_isSquare ⟨b, by rw [← hb]; ring⟩
  rcases hdvd with h | h
  · have hlt : |a ^ 2 - (q : ℤ)| < (N : ℤ) := by
      rw [abs_lt]; constructor <;> linarith
    exact hnsq a (by have := Int.eq_zero_of_abs_lt_dvd h hlt; linarith)
  · have hlt : |a ^ 2 - 4 * (q : ℤ)| < (N : ℤ) := by
      rw [abs_lt]; constructor <;> linarith
    have h4 : a ^ 2 = 4 * (q : ℤ) := by
      have := Int.eq_zero_of_abs_lt_dvd h hlt; linarith
    have heven : Even a := by
      have h2 : Even (a ^ 2) := ⟨2 * (q : ℤ), by rw [h4]; ring⟩
      exact (Int.even_pow.mp h2).1
    obtain ⟨b, rfl⟩ := heven
    exact hnsq b (by nlinarith)

/-- **Reciprocity bridge: `(−N/q) = (q/N)` when `N ≡ 3 (mod 4)`** (PROVEN
2026-07-26): for distinct odd primes `N, q` with `N ≡ 3 (mod 4)`, if `−N` is
a square mod `q` then `q` is a square mod `N`.

Proof. `legendreSym q (−N) = χ₄(q) · legendreSym q N` (`legendreSym.at_neg`),
and `legendreSym q N = (−1)^{(N/2)(q/2)} · legendreSym N q`
(`legendreSym.quadratic_reciprocity'`). `N ≡ 3 (mod 4)` makes `N/2` ODD, so
`(−1)^{(N/2)(q/2)} = (−1)^{q/2} = χ₄(q)`, and `χ₄(q)² = 1`. The two copies of
`χ₄(q)` cancel, leaving `legendreSym q (−N) = legendreSym N q`.

This is the only place the signature-`6` branch needs reciprocity, and it is
what lets `mazurIsogeny_classNumberOne_of_inert` be stated in terms of `−N`
mod `q` — the form the class-number-one theorem needs — while the Frobenius
argument works with `q` mod `N`. -/
theorem mazurIsogeny_isSquare_of_isSquare_neg {N q : ℕ} [Fact N.Prime] [Fact q.Prime]
    (hmod : N % 4 = 3) (hq2 : q ≠ 2) (hqN : q ≠ N)
    (h : IsSquare ((-(N : ℤ) : ZMod q))) : IsSquare ((q : ℕ) : ZMod N) := by
  have hN2 : N ≠ 2 := by omega
  have hNz : ((N : ℕ) : ZMod q) ≠ 0 := ZMod.prime_ne_zero q N hqN
  have hqz : ((q : ℕ) : ZMod N) ≠ 0 := ZMod.prime_ne_zero N q (fun hh => hqN hh.symm)
  have hne : ((-(N : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_natCast]; exact neg_ne_zero.mpr hNz
  have hqodd : q % 2 = 1 := by
    rcases (Nat.Prime.eq_two_or_odd (Fact.out : q.Prime)) with h' | h'
    · exact absurd h' hq2
    · exact h'
  have h1 : legendreSym q (-(N : ℤ)) = 1 :=
    (legendreSym.eq_one_iff (p := q) hne).mpr (by rw [Int.cast_neg]; exact h)
  have hhalf : N / 2 % 2 = 1 := by omega
  have hchi : ZMod.χ₄ (q : ℕ) * ZMod.χ₄ (q : ℕ) = 1 := by
    rw [ZMod.χ₄_eq_neg_one_pow (n := q) hqodd, ← pow_add]
    exact Even.neg_one_pow ⟨q / 2, rfl⟩
  have hqr : legendreSym q (N : ℤ) = (-1 : ℤ) ^ (N / 2 * (q / 2)) * legendreSym N (q : ℤ) :=
    legendreSym.quadratic_reciprocity' hN2 hq2
  have hpow : (-1 : ℤ) ^ (N / 2 * (q / 2)) = ZMod.χ₄ (q : ℕ) := by
    rw [pow_mul, Odd.neg_one_pow (Nat.odd_iff.mpr hhalf)]
    exact (ZMod.χ₄_eq_neg_one_pow (n := q) hqodd).symm
  have h2 : legendreSym N (q : ℤ) = 1 := by
    rw [legendreSym.at_neg hq2, hqr, hpow] at h1
    calc legendreSym N (q : ℤ)
        = (ZMod.χ₄ (q : ℕ) * ZMod.χ₄ (q : ℕ)) * legendreSym N (q : ℤ) := by rw [hchi, one_mul]
      _ = 1 := by rw [mul_assoc]; exact h1
  have hqz' : ((q : ℤ) : ZMod N) ≠ 0 := by rw [Int.cast_natCast]; exact hqz
  have hres := (legendreSym.eq_one_iff (p := N) hqz').mp h2
  rwa [Int.cast_natCast] at hres

/-- **The sixth-power refinement** (PROVEN 2026-07-26): in `ZMod N` with `N`
prime and `N ≡ 3 (mod 4)`, if `x¹² = Q⁶` with `x ≠ 0`, `Q ≠ 0` and `Q` a
SQUARE, then already `x⁶ = Q³`.

This is the step that converts "the isogeny signature is `6`" into "`ψ²` is a
CUBE root of unity" rather than merely a sixth root, and it is exactly where
the non-inertness of `q` is spent: `Q = q` is a square mod `N` precisely
because `q` is not inert in `ℚ(√−N)`.

Proof, and it needs no `orderOf` reasoning. `x¹² = Q⁶` factors as
`(x⁶ − Q³)(x⁶ + Q³) = 0`, so in the field `ZMod N` either `x⁶ = Q³` — the
conclusion — or `x⁶ = −Q³`. In the second case write `Q = c·c` and put
`m := (N−1)/2`, which is ODD because `N ≡ 3 (mod 4)`. Fermat gives
`x^{N−1} = c^{N−1} = 1`, so `(x⁶)^m = (x^{N−1})³ = 1` and likewise
`(c⁶)^m = 1`; but `(x⁶)^m = (−c⁶)^m = (−1)^m·(c⁶)^m = −1` since `m` is odd.
Hence `1 = −1`, i.e. `N ∣ 2`, contradicting `N ≡ 3 (mod 4)`. -/
theorem mazurIsogeny_sixthPower_of_isSquare {N : ℕ} [Fact N.Prime] (hmod : N % 4 = 3)
    {x Qv : ZMod N} (hx : x ≠ 0) (hQ : Qv ≠ 0) (hsq : IsSquare Qv)
    (h12 : x ^ 12 = Qv ^ 6) : x ^ 6 = Qv ^ 3 := by
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hQ hc
  have hfac : (x ^ 6 - Qv ^ 3) * (x ^ 6 + Qv ^ 3) = 0 := by linear_combination h12
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : x ^ 6 = -(Qv ^ 3) := add_eq_zero_iff_eq_neg.mp h
    have hm : N - 1 = 2 * ((N - 1) / 2) := by omega
    have hmodd : (N - 1) / 2 % 2 = 1 := by omega
    set m := (N - 1) / 2 with hmdef
    have hxf : x ^ (N - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
    have hcf : c ^ (N - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc0
    have e1 : (x ^ 6) ^ m = 1 := by
      rw [← pow_mul, show 6 * m = 2 * m * 3 by ring, ← hm, pow_mul, hxf, one_pow]
    have e2 : (c ^ 6) ^ m = 1 := by
      rw [← pow_mul, show 6 * m = 2 * m * 3 by ring, ← hm, pow_mul, hcf, one_pow]
    have e3 : Qv ^ 3 = c ^ 6 := by rw [hc]; ring
    have e4 : (x ^ 6) ^ m = -(1 : ZMod N) := by
      rw [hneg, e3, neg_pow, Odd.neg_one_pow (Nat.odd_iff.mpr hmodd), e2, mul_one]
    have h11 : (1 : ZMod N) = -1 := e1.symm.trans e4
    have h2 : ((2 : ℤ) : ZMod N) = 0 := by push_cast; linear_combination h11
    have hdvd2 : (N : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 N).mp h2
    have := Int.le_of_dvd (by norm_num) hdvd2
    omega

/-- **The two admissible values of `a²` mod `N`** (PROVEN 2026-07-26): if `x`
is a nonzero root of `X² − aX + q` in `ZMod N` with `x¹² = q⁶`, `q ≢ 0` and
`q` a square, then `a² ≡ q` or `a² ≡ 4q (mod N)`.

Proof. `mazurIsogeny_sixthPower_of_isSquare` upgrades `x¹² = q⁶` to
`x⁶ = q³`, which factors as `(x² − q)(x⁴ + qx² + q²) = 0`. From the
characteristic equation, `ax = x² + q`, so `a²x² = (x² + q)²`. In the first
branch `x² = q` and `(x² + q)² = 4q·x²`; in the second
`(x² + q)² = q·x² + (x⁴ + qx² + q²) = q·x²`. Cancelling `x² ≠ 0` gives
`a² = 4q` and `a² = q` respectively.

Both branches really occur, which is why the conclusion is a disjunction and
why the consumer must refute BOTH: `a² = q` is the case `ψ²(σ_q) ≠ 1` and
`a² = 4q` is the case `ψ²(σ_q) = 1`. -/
theorem mazurIsogeny_traceRelation_of_signature_six {N q : ℕ} [Fact N.Prime]
    (hmod : N % 4 = 3) {x : ZMod N} (hx : x ≠ 0) (hqz : ((q : ℕ) : ZMod N) ≠ 0)
    (h12 : x ^ 12 = ((q : ℕ) : ZMod N) ^ 6) (hsq : IsSquare ((q : ℕ) : ZMod N))
    {a : ℤ} (hchar : x ^ 2 - (a : ZMod N) * x + ((q : ℕ) : ZMod N) = 0) :
    (a : ZMod N) ^ 2 = ((q : ℕ) : ZMod N) ∨
      (a : ZMod N) ^ 2 = 4 * ((q : ℕ) : ZMod N) := by
  set Qv : ZMod N := ((q : ℕ) : ZMod N) with hQdef
  have hkey : x ^ 6 = Qv ^ 3 := mazurIsogeny_sixthPower_of_isSquare hmod hx hqz hsq h12
  have hax : (a : ZMod N) * x = x ^ 2 + Qv := by linear_combination -hchar
  have hx2ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hfac : (x ^ 2 - Qv) * (x ^ 4 + Qv * x ^ 2 + Qv ^ 2) = 0 := by linear_combination hkey
  rcases mul_eq_zero.mp hfac with h | h
  · right
    have hx2 : x ^ 2 = Qv := sub_eq_zero.mp h
    have hmul : ((a : ZMod N) ^ 2 - 4 * Qv) * x ^ 2 = 0 := by
      linear_combination ((a : ZMod N) * x + x ^ 2 + Qv) * hax + (x ^ 2 - Qv) * hx2
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hx2ne
  · left
    have hmul : ((a : ZMod N) ^ 2 - Qv) * x ^ 2 = 0 := by
      linear_combination ((a : ZMod N) * x + x ^ 2 + Qv) * hax + h
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hx2ne

/-- **The Frobenius trace relation at a non-inert prime** (PROVEN 2026-07-26
over the SIBLING leaf `exists_frobeniusTrace_of_potentiallyGoodReduction`,
replacing the sorry this node was introduced with earlier the same day — the
elliptic-curve half of
`mem_classNumberOnePrimes_of_isogenySignature_six`; [Michaud-Jacobs,
Prop. 4.4]): under isogeny signature `6` and `N ≡ 3 (mod 4)`, if `2 < q` is
a prime with `4q < N` which is NOT inert in `ℚ(√−N)` — equivalently `−N` is
a square mod `q` — then there is a RATIONAL integer `a` with `a² ≤ 4q` and
`N ∣ a² − q` or `N ∣ a² − 4q`.

Proof (not formalised). `N ≡ 3 (mod 4)` makes `(N+1)/4` an integer, and
`ψ := λ·χ^{−(N+1)/4}` satisfies `ψ¹² = λ¹²·χ^{−6} = 1` by `hsig` while
`ψ^{N−1} = 1`; since `gcd(12, N−1) = 6` for `N ≡ 3 (mod 4)`, `ψ⁶ = 1`, i.e.
`λ = ψ·χ^{(N+1)/4}` with `ψ` of order dividing `6`. Let `σ_q` be a
Frobenius at `q`. Potential good reduction at `q` — which is `hpg`, i.e.
Mazur's formal-immersion theorem, and is the only reason this leaf carries
it — makes `Tr ρ_{E,N}(σ_q)` the reduction of a rational integer `a` with
`a² ≤ 4q` (Serre–Tate Thm 3, then Hasse–Weil), and `λ(σ_q)` is an
eigenvalue of `ρ_{E,N}(σ_q)`, whose determinant is `χ(σ_q) = q`. So
`a ≡ λ(σ_q) + q·λ(σ_q)^{−1} (mod N)`. If `q` is not inert in `ℚ(√−N)` then
`(−N/q) = 1`, hence by quadratic reciprocity `(q/N) = 1` and
`q^{(N−1)/2} ≡ 1`, so `q^{(N+1)/2} ≡ q (mod N)`. Squaring the expression
for `a` and substituting gives `a² − 2q ≡ q·(ψ²(σ_q) + ψ^{−2}(σ_q))`, and
`ψ²(σ_q)` is a cube root of unity, so the bracket is `2` or `−1`. That is
`a² ≡ 4q` or `a² ≡ q (mod N)`, which is the conclusion.

WHAT IS ACTUALLY FORMALISED BELOW, and it is the whole thing. The only
external input is the sibling leaf
`exists_frobeniusTrace_of_potentiallyGoodReduction`, which already carries
Serre–Tate and Hasse–Weil and already consumes `hpg`; everything else is
`ZMod N` arithmetic over the three PROVEN lemmas above. In particular the
`ψ⁶ = 1` bookkeeping of the classical write-up is replaced by the sharper
and much cheaper `mazurIsogeny_sixthPower_of_isSquare`: one does not need
`ψ` at all, only that `x⁶ = q³` follows from `x¹² = q⁶` once `q` is a
square mod `N`, and the non-inertness hypothesis is exactly what supplies
that square (through `mazurIsogeny_isSquare_of_isSquare_neg`, i.e.
reciprocity). So this node introduces NO new deep input: after this commit
the entire signature-`6` branch rests on `hpg` (the formal-immersion leaf),
the Frobenius-trace leaf, and Baker–Heegner–Stark — nothing else. -/
theorem WeierstrassCurve.exists_frobeniusTraceRelation_of_isogenySignature_six
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN23 : 23 ≤ N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hpg : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ N → 0 ≤ padicValRat q E.j)
    (hsig : ∀ σ : Field.absoluteGaloisGroup ℚ,
      lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ 6)
    (hmod : N % 4 = 3)
    {q : ℕ} (hq : q.Prime) (hq2 : 2 < q) (hq4 : 4 * q < N)
    (hsplit : IsSquare ((-(N : ℤ) : ZMod q))) :
    ∃ a : ℤ, a ^ 2 ≤ 4 * (q : ℤ) ∧
      ((N : ℤ) ∣ a ^ 2 - (q : ℤ) ∨ (N : ℤ) ∣ a ^ 2 - 4 * (q : ℤ)) := by
  haveI : Fact N.Prime := ⟨hN⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hqN : q ≠ N := by omega
  have hq2' : q ≠ 2 := by omega
  -- The sibling leaf: Frobenius at `q` satisfies its characteristic polynomial
  -- `X² − aX + q` mod `N`, with `a` a RATIONAL integer bounded by `2√q`.
  obtain ⟨a, ha, hchar⟩ :=
    E.exists_frobeniusTrace_of_potentiallyGoodReduction g hN hN23 hg lam hlam hpg hq hq2' hqN
  refine ⟨a, ha, ?_⟩
  set σq := GaloisRepresentation.globalFrob hq.toHeightOneSpectrumRingOfIntegersRat with hσq
  -- `χ_N(σ_q) = q` (`cyclotomicCharacterModL_globalFrob`), hence `λ(σ_q)¹² = q⁶`.
  have hcyc : ((@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σq : (ZMod N)ˣ) : ZMod N)
      = ((q : ℕ) : ZMod N) :=
    @GaloisRepresentation.cyclotomicCharacterModL_globalFrob N q ⟨hN⟩ hq hqN
  have h12 : ((lam σq : (ZMod N)ˣ) : ZMod N) ^ 12 = ((q : ℕ) : ZMod N) ^ 6 := by
    have h3 := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) (hsig σq)
    simp only [Units.val_pow_eq_pow_val] at h3
    rw [h3, hcyc]
  have hx : ((lam σq : (ZMod N)ˣ) : ZMod N) ≠ 0 := Units.ne_zero _
  have hqz : ((q : ℕ) : ZMod N) ≠ 0 := ZMod.prime_ne_zero N q (fun hh => hqN hh.symm)
  -- Non-inertness of `q` in `ℚ(√−N)` says `−N` is a square mod `q`; reciprocity
  -- turns that into `q` a square mod `N`, which is what sharpens `x¹² = q⁶` to
  -- `x⁶ = q³` and so pins `a²` to one of two values.
  have hsq : IsSquare ((q : ℕ) : ZMod N) :=
    mazurIsogeny_isSquare_of_isSquare_neg hmod hq2' hqN hsplit
  rcases mazurIsogeny_traceRelation_of_signature_six hmod hx hqz h12 hsq hchar with h | h
  · left
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination h
  · right
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination h

/-- **Square-root witness in natural-number form** (PROVEN 2026-07-26): if
`q ∣ c² + N` for naturals `c, N`, then `−N` is a square mod `q`.

This is the shape in which every concrete non-inertness witness below is
supplied. `q ∣ c * c + N` is a statement about two numerals that `omega`
discharges from a congruence on `N`, and it involves no evaluation of a
`ZMod` numeral at all — which is what keeps the finite check cheap. Note
`c = 0` is allowed and is genuinely useful: it says that a prime `q`
DIVIDING `N` splits (`0` is a square), which is how composite `N` are
excluded below without ever invoking primality. -/
theorem mazurIsogeny_isSquare_neg_of_dvd {q N c : ℕ} (h : q ∣ c * c + N) :
    IsSquare ((-(N : ℤ) : ZMod q)) := by
  refine ⟨(c : ZMod q), ?_⟩
  have h0 : ((c * c + N : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0 ⊢
  linear_combination -h0

/-- **Large prime factors force primality** (PROVEN 2026-07-26): if `1 < n`,
`n < m * m`, and every prime factor of `n` is `≥ m`, then `n` is prime.

Proof. Write `n = p * k` with `p := n.minFac`. If `k = 1` then `n = p` is
prime. Otherwise `k > 1` has a prime factor `r = k.minFac`, which also
divides `n`; both `p ≥ m` and `r ≥ m` by hypothesis, and `r ≤ k`, so
`n = p * k ≥ p * r ≥ m * m`, contradicting `n < m * m`.

This is the sieve half of Rabinowitsch's argument: once every small prime
has been excluded as a divisor, a value below `m²` has no room for two
prime factors and is therefore prime. -/
theorem mazurIsogeny_prime_of_large_factors {n m : ℕ} (h1 : 1 < n) (hlt : n < m * m)
    (hfac : ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p) : n.Prime := by
  have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hk0 : k ≠ 0 := by rintro rfl; omega
  rcases eq_or_lt_of_le (show 1 ≤ k by omega) with hk1 | hk1
  · rw [hk, ← hk1, mul_one]; exact hpp
  · have hr : k.minFac.Prime := Nat.minFac_prime (by omega)
    have hkn : k ∣ n := by rw [hk]; exact dvd_mul_left k n.minFac
    have hrf : k.minFac ∣ n := (Nat.minFac_dvd k).trans hkn
    have h1' : m ≤ n.minFac := hfac _ hpp (Nat.minFac_dvd n)
    have h2' : m ≤ k.minFac := hfac _ hr hrf
    have h3' : k.minFac ≤ k := Nat.minFac_le (by omega)
    have hmm : m * m ≤ n.minFac * k := Nat.mul_le_mul h1' (le_trans h2' h3')
    rw [← hk] at hmm
    exact absurd hlt (not_lt.mpr hmm)

/-- **The Rabinowitsch bridge** (PROVEN 2026-07-26): with `N + 1 = 4 * m` and
`m ≥ 6`, if every odd prime `q` with `4q < N` is inert — `−N` a non-square
mod `q` — then `x² + x + m` is PRIME for every `x ≤ m − 2`.

This is the whole elementary content of the class-number-one hypothesis, and
it removes Legendre symbols from the remaining deep leaf entirely. Three
steps, all elementary.

1. NO SMALL ODD PRIME DIVIDES A VALUE. If `p ∣ x² + x + m` with `p` odd, then
   from the identity `(2x + 1)² + N = 4 * (x² + x + m)` — which is exactly
   `N + 1 = 4m` — we get `(2x + 1)² ≡ −N (mod p)`, so `−N` is a square mod
   `p` and `p` is not inert. Hence every odd prime `p < m` divides no value
   of `x² + x + m` whatsoever. (`p < m` is equivalent to `4p < N`.)

2. `m` IS ODD, hence `N ≡ 3 (mod 8)`. Suppose `m` even. If `m ≡ 2 (mod 4)`
   then `k := m/2` is ODD and `≥ 3`, so `k.minFac` is an odd prime `< m`
   dividing `m = 0² + 0 + m` — contradicting step 1 at `x = 0`. If
   `m ≡ 0 (mod 4)` then `j := m/2 + 1` is ODD and `≥ 5`, so `j.minFac` is an
   odd prime `< m` dividing `m + 2 = 1² + 1 + m` — contradicting step 1 at
   `x = 1`. This is the elementary reason the branch `N ≡ 7 (mod 8)` cannot
   occur, even though `q = 2` is outside the hypothesis: `2` splitting is
   invisible to `hinert`, but it forces a SMALL ODD prime to split as well.

3. THE VALUES ARE PRIME. For `x ≤ m − 2`, `x² + x` is even and `m` is odd, so
   `f := x² + x + m` is odd; every prime factor of `f` is therefore odd, and
   by step 1 is `≥ m`. And `f ≤ (m−2)² + (m−2) + m = m² − 2m + 2 < m²`. So
   `mazurIsogeny_prime_of_large_factors` applies and `f` is prime.

The converse direction (prime-generating implies inert) is classical and is
not needed here. -/
theorem mazurIsogeny_primeGenerating_of_inert {N m : ℕ} (hm6 : 6 ≤ m)
    (hNm : N + 1 = 4 * m)
    (hinert : ∀ q : ℕ, q.Prime → 2 < q → 4 * q < N →
      ¬ IsSquare ((-(N : ℤ) : ZMod q))) :
    ∀ x : ℕ, x + 1 < m → Nat.Prime (x ^ 2 + x + m) := by
  have hkey : ∀ p : ℕ, p.Prime → p ≠ 2 → p < m → ∀ x : ℕ, ¬ p ∣ (x ^ 2 + x + m) := by
    intro p hp hp2 hpm x hdvd
    refine hinert p hp (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) (by omega) ?_
    obtain ⟨k, hk⟩ := hdvd
    refine mazurIsogeny_isSquare_neg_of_dvd (c := 2 * x + 1) ⟨4 * k, ?_⟩
    calc (2 * x + 1) * (2 * x + 1) + N = 4 * x ^ 2 + 4 * x + (N + 1) := by ring
      _ = 4 * x ^ 2 + 4 * x + 4 * m := by rw [hNm]
      _ = 4 * (x ^ 2 + x + m) := by ring
      _ = 4 * (p * k) := by rw [hk]
      _ = p * (4 * k) := by ring
  have hmodd : m % 2 = 1 := by
    by_contra hev
    have he : m % 4 = 0 ∨ m % 4 = 2 := by omega
    rcases he with h4 | h4
    · set j := m / 2 + 1 with hj
      have hjodd : j % 2 = 1 := by omega
      have hp : j.minFac.Prime := Nat.minFac_prime (by omega)
      have hpd : j.minFac ∣ j := Nat.minFac_dvd j
      have hp2 : j.minFac ≠ 2 := by intro hh; rw [hh] at hpd; omega
      have hplt : j.minFac < m := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
      refine hkey j.minFac hp hp2 hplt 1 ?_
      have hval : (1 : ℕ) ^ 2 + 1 + m = m + 2 := by ring
      rw [hval]
      exact hpd.trans ⟨2, by omega⟩
    · set k := m / 2 with hkdef
      have hkodd : k % 2 = 1 := by omega
      have hp : k.minFac.Prime := Nat.minFac_prime (by omega)
      have hpd : k.minFac ∣ k := Nat.minFac_dvd k
      have hp2 : k.minFac ≠ 2 := by intro hh; rw [hh] at hpd; omega
      have hplt : k.minFac < m := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
      refine hkey k.minFac hp hp2 hplt 0 ?_
      have hval : (0 : ℕ) ^ 2 + 0 + m = m := by ring
      rw [hval]
      exact hpd.trans ⟨2, by omega⟩
  intro x hx
  have hodd : (x ^ 2 + x + m) % 2 = 1 := by
    have he : Even (x ^ 2 + x) := by
      have hxx : x ^ 2 + x = x * (x + 1) := by ring
      rw [hxx]; exact Nat.even_mul_succ_self x
    have := Nat.even_iff.mp he
    omega
  have hlt : x ^ 2 + x + m < m * m := by
    obtain ⟨d, hd⟩ : ∃ d, m = x + 2 + d := ⟨m - x - 2, by omega⟩
    rw [hd]; nlinarith
  refine mazurIsogeny_prime_of_large_factors (by omega) hlt ?_
  intro p hp hpd
  by_contra hpm
  exact hkey p hp (by rintro rfl; omega) (by omega) x hpd

/-- **Baker–Heegner–Stark, as a bound on prime-generating polynomials**
(sorry leaf, introduced 2026-07-26, replacing the bare Legendre-symbol form
that stood here — this leaf IS the class-number-one theorem and nothing
else): if `m ≥ 2` and `x² + x + m` is PRIME for every `x ≤ m − 2`, then
`m ≤ 41`.

WHY THIS SHAPE. The previous cut had already removed number fields, ideal
classes and Minkowski bounds; this one additionally removes Legendre
symbols, quadratic reciprocity and the prime `N` itself. What is left is a
single self-contained assertion about a prime-generating quadratic
polynomial — Rabinowitsch's criterion — which is the classical statement of
the class-number-one problem in its most elementary vocabulary. Everything
connecting it back to the isogeny argument is now PROVEN, in
`mazurIsogeny_primeGenerating_of_inert` and in
`mazurIsogeny_classNumberOne_of_inert` below.

The bound is SHARP and the leaf is NOT vacuous: the hypothesis is satisfied
exactly by `m ∈ {2, 3, 5, 11, 17, 41}`, i.e. `4m − 1 ∈ {7, 11, 19, 43, 67,
163}`, the class-number-one discriminants `≡ 3 (mod 4)`. `m = 41` attains
the bound, so no smaller constant is provable.

SHARPNESS RE-VERIFIED AND EXTENDED (2026-07-26, second pass, independently
of the first). The original figure was `m ≤ 1089`, the range in which
`f(m−2)` stays inside a sieve of `1.2 · 10⁶`. Re-run with a deterministic
Miller–Rabin test instead of a sieve, so the range is not capped by the
sieve, and with early exit at the first composite value: over EVERY
`m ≤ 3 · 10⁶` the solution set is still exactly `{2, 3, 5, 11, 17, 41}`.
Cross-checked in PARI/GP from the other side, through the class number
rather than the polynomial: `qfbclassno(-q) = 1` for squarefree
`q ≡ 3 (mod 4)`, `q < 20000`, returns exactly `{3, 7, 11, 19, 43, 67, 163}`.
The two computations agree, which also re-confirms Rabinowitsch's criterion
itself on this range. The check that would refute all of this is a single
`m > 41` for which `x² + x + m` is prime at every `x ≤ m − 2`.

ROUTE AUDIT (2026-07-26; a DATED claim about the pin — re-run the greps
before believing it). Four routes are known, and the pin supports none of
them. What is actually present:

* HEEGNER–STARK, via the Weber modular functions and the resulting quartic
  Diophantine equation. Mathlib has a modular-forms framework
  (`Mathlib/NumberTheory/ModularForms/`, including `DedekindEta.lean` and
  `Delta.lean`), but NO `j`-invariant as a modular function, NO Weber
  functions, and — decisively — NO class field theory of any kind: a grep
  for `Hilbert class field`, `class field theory`, `ArtinMap`, `artinMap`
  over all of mathlib returns nothing. Complex multiplication is what turns
  `h = 1` into a degree bound, so this route has no foundation at all.
* BAKER, via linear forms in logarithms. ABSENT, and not merely
  unformalized here: this pin has no transcendence theory whatever — no
  Baker, no Gelfond–Schneider, no Lindemann–Weierstrass.
* SIEGEL–TATUZAWA or GOLDFELD–GROSS–ZAGIER, via an effective lower bound on
  `L(1, χ)`. This is the route with the most support, and still not enough:
  `Mathlib/NumberTheory/LSeries/` is substantial (`Dirichlet.lean`,
  `Nonvanishing.lean`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`),
  and the analytic class number formula EXISTS as
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
  (`Mathlib/NumberTheory/NumberField/DedekindZeta.lean`). What is missing is
  the only part that bounds anything: an effective lower bound on
  `L(1, χ)`. Siegel's is ineffective by construction, so it could not close
  this leaf even if formalized.
* GAUSS FORM-CLASS-GROUP bookkeeping. Binary quadratic forms are ABSENT
  from mathlib, from `~/cs/FLT` and from this project (no
  `BinaryQuadraticForm`, no Gauss reduction). `NumberField.classNumber` and
  `classNumber_eq_one_iff` exist, and `minkowskiBound` exists, but no class
  number of any imaginary quadratic field is computed anywhere — the only
  worked `IsPrincipalIdealRing (𝓞 K)` instances in mathlib are cyclotomic
  (`Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`). The words
  Heegner, Stark and Rabinowitsch occur in mathlib only in a TODO comment
  in `Mathlib/Analysis/Real/Pi/Chudnovsky.lean`.

WHY THIS LEAF WAS NOT DECOMPOSED FURTHER (2026-07-26, second pass). Every
available cut is a RENAME: restating the hypothesis as `h(1 − 4m) = 1`, or
as "the only reduced form of discriminant `1 − 4m` is `(1, 1, m)`", moves
the leaf to the literature's vocabulary but leaves both halves exactly as
hard — the bridge is elementary and the bound is the whole problem. A cut
along Heegner's argument would split it into a monster (CM plus class field
theory) and a hard-but-finite Diophantine leaf, which is worse than one
honest statement. So the sorry stands.

THE ELEMENTARY CONTENT IS PROVABLY EXHAUSTED, and here is the quantitative
form of that, which is the useful thing to know before attacking this leaf
again. The hypothesis has a much stronger elementary consequence than
`h = 1` is usually given credit for, and even that consequence does not
bound `m`:

1. `4m − 1 = q` is PRIME. Any prime `p ∣ q` satisfies `p ∣ f(x)` for the `x`
   with `2x + 1 ≡ 0 (mod p)`, so by the argument of
   `mazurIsogeny_primeGenerating_of_inert` every prime factor of `q` is
   `≥ m`; and `q < m²`, so `q` has exactly one.
2. `χ(n) = λ(n)` for every `n ≤ m − 1`, where `χ = (1 − 4m | ·)` and `λ` is
   Liouville's function. Indeed every odd prime `p < m` is inert (step 1 of
   the bridge above) and `χ(2) = −1` because `q ≡ 3 (mod 8)`, and every
   prime factor of such an `n` is `≤ n < m`.
3. `Σ_{0 < n < q/4} χ(n) = 0`, unconditionally, for any `q ≡ 3 (mod 8)`.
   Proof: write `T` for the sum over `0 < n < q/2` and `S` for the sum over
   `0 < n < q/4`. The even `n = 2j` in the first range contribute
   `χ(2) S = −S`, so the odd ones contribute `T + S`; and `n ↦ (q − n)/2` is
   a bijection from the odd `n < q/2` onto the integers in `(q/4, q/2)`
   with `χ((q − n)/2) = χ(n)`, so the odd ones also contribute `T − S`.
   Hence `S = 0`.

Combining, the hypothesis forces `Σ_{n=1}^{m−1} λ(n) = 0` — the Liouville
summatory function vanishes at `m − 1`. That is a very sharp sieve: over
`x ≤ 10⁷` it holds at only NINE points, `x ∈ {2, 4, 6, 10, 16, 26, 40, 96,
586}`, and combined with `m` prime (which is `hgen` at `x = 0`) it leaves
`m ∈ {3, 5, 7, 11, 17, 41, 97, 587}` — five true solutions and three
candidates, all three killed by direct evaluation. Every solution `≥ 3` does
satisfy it, as it must (`m = 2` is the one exception, and for the expected
reason: `q = 7 ≡ 7 (mod 8)`, so `χ(2) = +1` and step 3 does not apply).

And yet this does NOT bound `m`, which is precisely the point: `λ` sums to
`0` infinitely often — the Liouville summatory function changes sign
infinitely often (Haselgrove), and it moves by `±1`, so it must hit `0`
infinitely often. So the strongest exact elementary consequence available
still admits infinitely many candidates, and the residue after removing it
is again the class-number-one problem. Any future attempt should be judged
against this: a proposed elementary route that does not go strictly beyond
`Σ_{n<m} λ(n) = 0` cannot work.

FOURTH PASS (2026-07-27). The ROUTE AUDIT above was re-run against the
current pin rather than believed, since an audit is a dated claim. Every
absence it records still holds, ONE of its statements has gone stale in a
way that does not change the verdict, and the analytic route can now be
costed precisely. Each item below names the check that would refute it.

RE-VERIFIED ABSENCES (greps over `.lake/packages/mathlib/Mathlib` and over
`~/cs/FLT/FLT`, this pin):

* `artinMap`, `ArtinMap`, `rayClassGroup`, `RayClassGroup`, `Hilbert class
  field`, `class field theory` — ZERO hits in all of mathlib.
* `Weber`, and any `j`-invariant AS A MODULAR FUNCTION — absent. The only
  `Weber`/`jInvariant` hits under `Mathlib/NumberTheory` and
  `Mathlib/Analysis` are `Analysis/Fourier/AddCircle.lean` and
  `Analysis/Polynomial/CauchyBound.lean`, neither of them this.
* `BinaryQuadraticForm`, `binary quadratic` — the single hit in all of
  mathlib is a prose mention in `LegendreSymbol/Basic.lean`. No Gauss
  reduction theory.
* `~/cs/FLT` — zero hits for any of `jInvariant`, `Weber`, `classNumber`,
  `BinaryQuadratic`, `Heegner` across the whole reference project.

STALE ITEM, AND WHY IT DOES NOT HELP. "NO class field theory of any kind"
remains true of MATHLIB but is now false of THIS PROJECT:
`Fermat/FLT/Modularity/Interface.lean` carries `exists_artinMap_classGroup`,
`exists_artinMap_classGroup_frobenius` and
`exists_artinMap_classGroup_frobeniusIdeal`, and several ray-class/Artin
tasks are in flight. It still founds nothing here, for two independent
reasons:

1. the root of that chain, `exists_artinMap_classGroup_frobeniusIdeal`, is
   itself a `sorry` — the Artin map is STATED, not constructed;
2. more decisively, it is the Artin map of the Hilbert class field of the
   CYCLOTOMIC field `ℚ(μ_p)`, reached through `cyclotomicCharacter`.
   Heegner's argument needs the Hilbert class field of the IMAGINARY
   QUADRATIC field `K = ℚ(√(1 − 4m))` TOGETHER WITH the statement that it is
   generated by `j(𝒪_K)`. That second half is complex multiplication, a
   different theorem from Artin reciprocity, and it has no representative
   anywhere in mathlib, in `~/cs/FLT`, or in this tree.

   Refuting check: if a `j`-invariant ever appears as a modular function
   (with the `q`-expansion and the modular equation `Φ_n`), re-open this —
   that plus the Artin material would be the first real foothold.

THE ANALYTIC ROUTE, COSTED. Mathlib gives MORE than the earlier pass
credited, and the residual gap is smaller to state and no smaller to prove.

* PRESENT, and stronger than "the class number formula exists":
  `NumberField.dedekindZeta_residue` is literally
  `(2 ^ r₁ * (2π) ^ r₂ * R * h) / (w * √|d|)`, and
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT` proves it IS the residue at
  `s = 1`. Specialised to `K = ℚ(√−q)` with `q` prime, `q ≡ 3 (mod 4)`,
  `q > 3`: `r₁ = 0`, `r₂ = 1`, `R = 1`, `w = 2`, `disc K = −q`, so the
  residue is `π h / √q`.
* MISSING PIECE 1, absent rather than hard: the factorisation
  `ζ_K(s) = ζ(s) · L(s, χ_{−q})`. `dedekindZeta` occurs in EXACTLY ONE
  mathlib file (`NumberTheory/NumberField/DedekindZeta.lean`); nothing
  anywhere factors it over a quadratic field. Without it the residue
  formula never becomes a statement about `L(1, χ)` at all.
* MISSING PIECE 2, and this is the whole problem in its sharpest form. With
  the factorisation, `h = 1` reads `L(1, χ_{−q}) = π/√q` EXACTLY. But
  `h ≥ 1` already gives the effective bound `L(1, χ_{−q}) ≥ π/√q`, and
  CLASS NUMBER ONE IS PRECISELY ITS EQUALITY CASE. So the analytic route
  needs an effective bound that STRICTLY BEATS the trivial one; no
  positivity, non-vanishing or Euler-product-positivity argument can
  suffice, and mathlib's `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`
  and `LSeries/Nonvanishing.lean` are purely qualitative (their quantitative
  internals are `private`). The known effective improvements are
  Goldfeld–Gross–Zagier; Siegel's is ineffective by construction.

THE OBSTRUCTION, SHARPENED — this supersedes the `Σλ = 0` discussion as the
reason no elementary route can work, and it is the test to apply first.
`hgen` says exactly that the least prime `p` with `χ_{1−4m}(p) = +1` — the
least SPLIT prime of the discriminant — exceeds `m ≈ q/4`. So this leaf IS
an effective upper bound on the least split prime. Two consequences:

* Burgess-type character-sum bounds ARE effective, but they bound the least
  NON-residue (`χ(p) = −1`) by `q ^ (1/(4√e) + ε)`. They say nothing here:
  the hypothesis makes every small prime a non-residue, which is the
  direction those bounds permit rather than forbid.
* An effective bound on the least SPLIT prime is obstructed exactly by a
  possible Siegel zero of `L(s, χ_{1−4m})`, and `h = 1` at large `q` is
  precisely the Siegel-zero scenario. Every known route — Heegner–Stark,
  Baker, Goldfeld–Gross–Zagier — is a way of excluding that zero for this
  family.

So the rejection test of the previous pass is subsumed by a stronger one:
AN ELEMENTARY ROUTE MUST EXCLUDE A SIEGEL ZERO FOR `χ_{1−4m}`. No argument
that merely manipulates exact character identities can do that, which is
why `Σ_{n<m} λ(n) = 0` — the strongest such identity available — does not
bound `m`.

UNIQUENESS IN THE TREE. Grepping the whole project for `Heegner`, `Stark`,
`class number one` and `Rabinowitsch` finds them, outside this file, in
exactly one unrelated prose line of `ModThree.lean`. This declaration is
therefore the SOLE carrier of the class-number-one input: there is no
sibling leaf to unify with, and no duplicated deep input to reconcile.

FIFTH PASS (2026-07-27). Route chosen DELIBERATELY: the ANALYTIC one. Its
two gaps were re-costed by BUILDING the assembly in throwaway scratch
modules and COMPILING it against this pin, rather than by reading mathlib.
The fourth pass's verdict is unchanged and its two gaps are confirmed —
but their shapes were both wrong, in opposite directions, and the residue
is now exactly ONE arithmetic identity.

BOTH OF THE FOLLOWING COMPILED CLEAN (`lake env lean`, exit 0, first and
second try respectively):

* GAP 1 IS NOT ANALYTIC AT ALL — it is weaker than the fourth pass thought.
  mathlib defines `dedekindZeta K s` as the `LSeries` of
  `n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}` — coefficients, not an
  Euler product. So `ζ_K = ζ · L(χ)` on `re s > 1` follows from the purely
  ARITHMETIC coefficient identity `a_K = 1 ⋆ χ`, i.e.
  `#{I : absNorm I = n} = Σ_{d ∣ n} χ(d)`, by `LSeries_convolution'` and
  `LSeries_one_eq_riemannZeta`. Verified: a single `rw`. No Euler product,
  no analytic continuation, no convergence argument is needed anywhere.

* GAP 2 IS AN EXACT EQUALITY, and that is verified rather than asserted.
  Granted the factorisation and `χ ≠ 1`, the three mathlib facts
  `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `riemannZeta_residue_one` and
  `DirichletCharacter.differentiable_LFunction` combine, in ~25 lines, to
  `L(1, χ) = dedekindZeta_residue K`. For `K = ℚ(√−q)` that is
  `L(1, χ) = π h / √q`. So the analytic route is COMPLETE, from mathlib as
  it stands, down to that equality — and it stops there for exactly the
  reason the fourth pass gave: `h ≥ 1` already yields `L(1,χ) ≥ π/√q` and
  `h = 1` is precisely its equality case. Making the chain machine-checked
  does not move that boundary by one inch; it only locates it exactly.

THE RESIDUE, NAMED, with the check that refutes each item (all three
re-run against THIS pin, all three returning ZERO hits):

  1. `quadraticChar` / `legendreSym` packaged as a `DirichletCharacter` —
     absent from ALL of mathlib. So the factorisation cannot even be
     STATED with a Dirichlet character until this is written. Smallest of
     the three, and the natural first step.
     Refute: `grep -rn "quadraticChar\|legendreSym" Mathlib/ | grep -i dirichlet`.
  2. Multiplicativity of `n ↦ #{I : absNorm I = n}` — no `IsMultiplicative`
     statement about it anywhere under `Mathlib/NumberTheory/NumberField/Ideal/`.
     Refute: `grep -rn IsMultiplicative Mathlib/NumberTheory/NumberField/Ideal/`.
  3. The quadratic splitting law (`p` splits / is inert / ramifies according
     as `χ_d(p) = 1 / −1 / 0`) — absent. `NumberField/Ideal/KummerDedekind.lean`
     is the TOOL such a law would be built from, not the law; it contains no
     quadratic material at all.
     Refute: `grep -rn quadratic Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean`.

WHY NO CODE LANDED HERE, AND WHY THAT IS NOT A FAILURE. Both scratch proofs
are correct and NEITHER CAN BE COMMITTED: while this leaf is open, nothing
in the root cone of `fermat_last_theorem` can consume them, so they would be
free-floating, which this project forbids. That is a general fact about this
leaf, not an accident of this pass — any Gap-1/Gap-2 module is unreachable
from the root until the deep input itself is closed. The material is
reproducible from the three bullets above in minutes; what was worth
establishing is the COST, and it is now exact: the analytic route is ONE
arithmetic identity away from `L(1,χ) = π h/√q`, and still infinitely far
from `m ≤ 41`, because that equality is precisely where Siegel's
ineffectivity lives.

DECOMPOSITION DECLINED, DELIBERATELY, and here is the cut that was declined
so nobody has to rediscover it. The elementary converse
`hgen → every odd prime q < m is inert` is a ten-line Lean proof: if
`1 − 4m ≡ t² (mod q)`, pick `x₀ ∈ [0, q−1]` with `2x₀ + 1 ≡ t`; then
`q ∣ x₀² + x₀ + m` because `4(x² + x + m) = (2x+1)² + (4m−1)`; `x₀ + 1 < m`
holds since `q < m`; and `x₀² + x₀ + m ≥ m > q`, so `hgen`'s prime value is
properly divisible by `q` — contradiction. It would complete an
IFF with `mazurIsogeny_primeGenerating_of_inert`, whose guard `4q < N` is
literally `q < m` under `N = 4m − 1`. It is NOT taken because it moves no
difficulty whatsoever: the residual half is the same statement at the same
strength, which is exactly what the third audit meant by "every available
cut is a rename". Recording it costs nothing; taking it would cost a
verification cycle and buy a sorry in a different costume.

FAITHFULNESS, re-confirmed independently on this pass (deterministic
Miller–Rabin, no sieve cap, no reuse of the earlier PARI run): over
`2 ≤ m ≤ 5·10⁵` the hypothesis `hgen` holds for exactly
`m ∈ {2, 3, 5, 11, 17, 41}`. So the conclusion `m ≤ 41` is true and SHARP.

SIXTH PASS (2026-07-27, flt-lean-175). Nothing new to report, and that is
itself the finding worth recording so the next reader does not re-run this:
the faithfulness sweep was repeated once more, independently, to `2 ≤ m ≤
2·10⁶` (PARI/GP `isprime`, four times the previous range), returning exactly
`{2, 3, 5, 11, 17, 41}` again. The fifth pass's verdict stands unchanged and
no new axis was opened: the leaf is Baker–Heegner–Stark, and the two axes it
recorded as unsearched (Heegner–Stark/CM, Baker's linear forms in logarithms)
still have NO representative in mathlib, in `~/cs/FLT` or in this project, so
neither is a near-term route. Do not dispatch another prover here without
first committing to BUILDING one of those two theories; a search pass will
only reproduce this paragraph.

AXIS SEARCHED, stated so the next reader knows what this pass did NOT look
at: mathlib at this pin, `~/cs/FLT` (zero hits for each of `jInvariant`,
`Weber`, `classNumber`, `BinaryQuadratic`, `Heegner`, `Rabinowitsch`), this
project, and the ANALYTIC axis in full. NOT searched: the
Heegner–Stark/CM axis beyond confirming its prerequisites are absent, and
Baker's linear-forms-in-logarithms axis. Neither has any representative in
any of the three trees, so neither is a near-term route; but "no elementary
and no analytic route exists" is the claim this pass supports, and the
stronger "no route exists" is not.

SEVENTH PASS (2026-07-27, flt-lean-6) — **NO LONGER A SORRY HERE.** This
declaration is now PROVEN, over one deep leaf that lives elsewhere. What was
built, and it is a theory rather than a rename:
`Fermat/FLT/Mathlib/NumberTheory/BinaryQuadraticForm.lean` develops Gauss's
theory of integral binary quadratic forms from scratch (mathlib has none of
it, and neither does `~/cs/FLT`): the `SL₂(ℤ)` action with its composition
law, invariance of the discriminant, proper equivalence with `symm`/`trans`,
positivity of the values of a positive definite form, and — the substantive
piece — **Gauss reduction**, `exists_reduced_equivalent`: every positive
definite form is properly equivalent to one with `|b| ≤ a ≤ c`, by the
classical `T`-translate/`S`-swap descent on `a`. All of that is proven.

On top of it, `a_eq_one_of_primeGenerating` is Rabinowitsch's criterion in
its elementary half — for a reduced form of discriminant `1 − 4m` one has
`b` odd, `|b| = 2x + 1`, and `a·c = x² + x + m`, while `3a² ≤ 4m − 1` forces
`x + 1 < m`, so the hypothesis makes that product prime and `a ≤ c` pins
`a = 1` — and `equivalent_of_primeGenerating` upgrades this, via reduction,
to: EVERY positive definite form of discriminant `1 − 4m` is properly
equivalent to the principal form `⟨1, 1, m⟩`. That is precisely
"`1 − 4m` has one class".

So the residue is now the class number one theorem itself, stated with no
elliptic curve, no prime-generating quadratic and no Legendre symbol in
sight: `neg_163_le_of_classNumberOne`, "a negative discriminant with a
single class of positive definite forms is `≥ −163`". That is verbatim what
Heegner, Stark and Baker prove, and it is where any future CM or
linear-forms-in-logarithms work must attach. Its faithfulness was
machine-checked by enumerating reduced representatives of ALL positive
definite forms (primitive and imprimitive) for every discriminant down to
`−20000`: exactly `{−3, −4, −7, −8, −11, −19, −43, −67, −163}` have one
class, so the bound is true and sharp. The imprimitive forms matter — the
leaf would be FALSE at `m = 7` if the hypothesis were restricted to
primitive forms, since `h(−27) = 1` while `x² + x + 7 = 9` at `x = 1`.

The sixth pass's verdict is therefore unchanged in substance and sharpened
in form: neither Heegner–Stark nor Baker was built, and this pass makes no
claim to have moved that boundary. What it removes is everything AROUND the
boundary. -/
theorem mazurIsogeny_rabinowitsch_bound {m : ℕ} (hm : 2 ≤ m)
    (hgen : ∀ x : ℕ, x + 1 < m → Nat.Prime (x ^ 2 + x + m)) : m ≤ 41 :=
  Fermat.BinaryQuadraticForm.le_41_of_primeGenerating hm hgen

/-- **Class number one, in purely elementary form** (PROVEN 2026-07-26 over
`mazurIsogeny_rabinowitsch_bound`, replacing the bare sorry this node was
introduced with earlier the same day): if `N ≥ 23` is a prime with
`N ≡ 3 (mod 4)` such that every odd prime `q < N/4` is INERT in `ℚ(√−N)` —
equivalently `−N` is a non-square mod `q` — then `N ∈ {43, 67, 163}`.

WHY THIS SHAPE. The old single sorry mixed three different things: the
Hasse–Weil trace estimate, an elementary incompatibility of inequalities,
and the class-number-one theorem. Only the last is deep, and stating it
like this removes elliptic curves, ideal classes, Minkowski bounds and
number fields from it altogether. As of the third pass of 2026-07-26 it no
longer contains the deep input either: the whole of it is now PROVEN over
`mazurIsogeny_rabinowitsch_bound`, in two independent halves.

THE PROOF, and both halves are elementary.

* THE BOUND. `hmod` makes `N + 1 = 4m`, and `mazurIsogeny_primeGenerating_of_inert`
  turns `hinert` into "`x² + x + m` is prime for every `x ≤ m − 2`" —
  Rabinowitsch's criterion. The deep leaf then gives `m ≤ 41`, i.e. `N ≤ 163`.
  This is the classical route back, made formal: instead of speaking of ideals
  of small norm being principal, one observes directly that an odd prime
  dividing a value of `x² + x + m` would split, so the values below `m²` are
  forced to be prime.
* THE FINITE CHECK. Seven congruence conditions, each a single application of
  `hinert` through `mazurIsogeny_isSquare_neg_of_dvd`, cut `[23, 163]` down to
  exactly `{43, 67, 163}`: `q = 3` with `c ∈ {0, 1}` gives `N ≡ 1 (mod 3)`;
  `q = 5` with `c ∈ {0, 1, 2}` gives `N ≡ 2, 3 (mod 5)`; `q = 7, c = 3` kills
  `103`; `q = 11, c = 4` kills `127`. The last two are stated with their
  `4q < N` guards (`28 < N`, `44 < N`) so that `omega` may use them.

FAITHFULNESS AUDIT (2026-07-26, re-run and EXTENDED on the third pass, by
independent sieve; the original PARI/GP figures are reproduced exactly).
Running the inert condition over ALL `N ≥ 1` with no primality and no
congruence filter, the complete list of survivors below `3·10⁵` is

  `{1, ..., 13, 16, 19, 22, 28, 37, 43, 58, 67, 163}`

and restricted to `N ≥ 23` this is `{28, 37, 43, 58, 67, 163}`, as first
reported. `hmod` alone leaves `{3, 7, 11, 19, 43, 67, 163}`, and `hN23` then
leaves the three.

CORRECTION to the earlier attribution, and it matters because the proof below
depends on it: `hN` (primality) is NOT what kills `28` and `58` — `hmod` is,
since `28 ≡ 0` and `58 ≡ 2 (mod 4)`. In fact NO composite at all survives
`hmod` together with `hN23`, so `hN` is REDUNDANT: the proof below never uses
it, and the statement is true without it. It is kept in the signature because
the consumer supplies it anyway and because dropping a hypothesis from a leaf
other agents have already built against buys nothing. The primality of `N` is
of course still doing work upstream, in the sibling leaves.

Note the pleasing symmetry with the sibling branch: `37` is excluded from
the signature-`≠ 6` branch by `hN37` and from THIS branch by `hmod`, which
is why the assembled theorem's exceptional set is `{37, 43, 67, 163}`. -/
theorem mazurIsogeny_classNumberOne_of_inert {N : ℕ} (hN : N.Prime) (hN23 : 23 ≤ N)
    (hmod : N % 4 = 3)
    (hinert : ∀ q : ℕ, q.Prime → 2 < q → 4 * q < N →
      ¬ IsSquare ((-(N : ℤ) : ZMod q))) :
    N ∈ ({43, 67, 163} : Finset ℕ) := by
  have hbound : N ≤ 163 := by
    obtain ⟨m, hNm⟩ : ∃ m, N + 1 = 4 * m := ⟨(N + 1) / 4, by omega⟩
    have hm6 : 6 ≤ m := by omega
    have hm41 := mazurIsogeny_rabinowitsch_bound (by omega : 2 ≤ m)
      (mazurIsogeny_primeGenerating_of_inert hm6 hNm hinert)
    omega
  have step : ∀ q c : ℕ, q.Prime → 2 < q → 4 * q < N → q ∣ c * c + N → False :=
    fun q c hq hq2 hqN hdvd => hinert q hq hq2 hqN (mazurIsogeny_isSquare_neg_of_dvd hdvd)
  have hgoal : N = 43 ∨ N = 67 ∨ N = 163 → N ∈ ({43, 67, 163} : Finset ℕ) := by
    rintro (rfl | rfl | rfl) <;> decide
  refine hgoal ?_
  have c3a : N % 3 ≠ 0 := fun h =>
    step 3 0 (by norm_num) (by norm_num) (by omega) (by omega)
  have c3b : N % 3 ≠ 2 := fun h =>
    step 3 1 (by norm_num) (by norm_num) (by omega) (by omega)
  have c5a : N % 5 ≠ 0 := fun h =>
    step 5 0 (by norm_num) (by norm_num) (by omega) (by omega)
  have c5b : N % 5 ≠ 4 := fun h =>
    step 5 1 (by norm_num) (by norm_num) (by omega) (by omega)
  have c5c : N % 5 ≠ 1 := fun h =>
    step 5 2 (by norm_num) (by norm_num) (by omega) (by omega)
  have c7 : 28 < N → N % 7 ≠ 5 := fun h1 h =>
    step 7 3 (by norm_num) (by norm_num) (by omega) (by omega)
  have c11 : 44 < N → N % 11 ≠ 6 := fun h1 h =>
    step 11 4 (by norm_num) (by norm_num) (by omega) (by omega)
  clear step hinert hgoal hN
  interval_cases N <;> omega

/-- **Signature `6` forces class number one** (PROVEN 2026-07-26 over the
three declarations above, replacing the former bare sorry — the
imaginary-quadratic branch; [Michaud-Jacobs, Prop. 4.4], and then
Baker–Heegner–Stark): if the signature is `6` and `N ≥ 23`, then
`N ∈ {43, 67, 163}`. These three are exactly the CM primes: a
class-number-one curve with CM by the order of discriminant `−N` has a
rational `N`-isogeny, since `N` ramifies.

THE CUT, and after the second pass of 2026-07-26 it leaves exactly ONE new
open leaf. The proof below is the whole of [MJ, Prop. 4.4] over:

* `exists_frobeniusTraceRelation_of_isogenySignature_six` — PROVEN, from the
  pre-existing sibling leaf `exists_frobeniusTrace_of_potentiallyGoodReduction`
  (which already carries Serre–Tate and Hasse–Weil, and is where potential
  good reduction `hpg`, hence Mazur's formal-immersion theorem, is consumed)
  plus reciprocity and `ZMod N` arithmetic;
* `mazurIsogeny_classNumberOne_of_inert` — PROVEN as of the third pass of
  2026-07-26, over the single remaining leaf `mazurIsogeny_rabinowitsch_bound`:
  Baker–Heegner–Stark, now stated with no number field, ideal class,
  Minkowski bound OR Legendre symbol in sight — just "a prime-generating
  quadratic `x² + x + m` forces `m ≤ 41`". The bridge from the inertness
  hypothesis to that criterion is `mazurIsogeny_primeGenerating_of_inert`,
  and the finite check over `[23, 163]` is discharged in-kernel;
* `mazurIsogeny_traceRelation_impossible` — PROVEN: `a² ≤ 4q` and `4q < N`
  force `a² = q` or `a² = 4q`, and a prime is not a square.

So the assembly is: for each odd prime `q < N/4`, a failure of inertness
would produce that impossible relation, so every such `q` IS inert, and the
class-number-one leaf reads off `{43, 67, 163}`.

What this buys over the old single sorry. The class-number-one theorem is a
DIFFERENT deep input from the Eisenstein ideal — it is the one that produces
three of the four exceptional primes — and it is now stated in a vocabulary
(Legendre symbols of a rational prime) that needs no ideal-class machinery
to attack, rather than being welded to a Frobenius-trace argument about
elliptic curves. And the Frobenius-trace half turned out to need no new deep
input at all: it is the sibling leaf plus quadratic reciprocity, so the
signature-`6` branch adds exactly one open problem to this file rather than
the two the first cut suggested. -/
theorem WeierstrassCurve.mem_classNumberOnePrimes_of_isogenySignature_six
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (g : (E⁄(AlgebraicClosure ℚ)).Point) {N : ℕ}
    (hN : N.Prime) (hN23 : 23 ≤ N)
    (hg : addOrderOf g = N)
    (lam : Field.absoluteGaloisGroup ℚ →* (ZMod N)ˣ)
    (hlam : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom g =
        ((lam σ : ZMod N).val) • g)
    (hpg : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ N → 0 ≤ padicValRat q E.j)
    (hsig : ∀ σ : Field.absoluteGaloisGroup ℚ,
      lam σ ^ 12 = (@GaloisRepresentation.cyclotomicCharacterModL N ⟨hN⟩ σ) ^ 6)
    (hmod : N % 4 = 3) :
    N ∈ ({43, 67, 163} : Finset ℕ) :=
  mazurIsogeny_classNumberOne_of_inert hN hN23 hmod fun q hq hq2 hq4 hsplit => by
    obtain ⟨a, ha, hdvd⟩ := E.exists_frobeniusTraceRelation_of_isogenySignature_six g hN
      hN23 hg lam hlam hpg hsig hmod hq hq2 hq4 hsplit
    exact mazurIsogeny_traceRelation_impossible hq hq4 ha hdvd
