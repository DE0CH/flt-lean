/-
Modularity/AbelianSchemeIsogeny.lean — own work for the Fermat project
(not vendored from the FLT project).

# Multiplication by `n` on an abelian scheme, as a morphism, and its surjectivity

This module sits between `Modularity/AbelianScheme.lean` (which gives an
abelian scheme only through its functor of points) and
`Modularity/TateModule.lean` (which consumes divisibility of a geometric
fibre).  It supplies the object that statement is really about — the
MORPHISM `[n] : A ⟶ A` — and reduces

  `exists_nsmul_eq_geomFibrePt` (`A_x̄(F̄)` is `n`-divisible)

to a single statement of the theory of abelian varieties which mentions
no Galois action, no field, and no group of points:

  `flat_locallyOfFinitePresentation_mulByNat` — `[n]` is FLAT and of
  finite presentation, i.e. (with the already-free properness) `[n]` is
  finite locally free.  That is the output of the THEOREM OF THE CUBE.

## Why a separate module

The Yoneda layer below (`RelPoint.self` … `isProper_mulByNat`) previously
lived inside `Modularity/TateModule.lean`, *below* the divisibility leaf
it is needed to prove.  Lean's declaration order therefore made the leaf
unprovable where it stands.  Moving the layer into an upstream module —
rather than reordering a 5000-line file whose other leaves have their own
owners — is the minimal fix, and it also cuts the layer's elaboration out
of that file.  The declarations are moved VERBATIM and keep their names,
so every existing consumer resolves unchanged through the `public import`.

## The reduction, in full

The chain below is PROVEN except at step 3, and step 3 has since been cut
down further — see "The open leaves" at the end of this docstring for the
list the compiler actually reports.  The chain is:

1. **Yoneda.** `mulByNat n : A ⟶ A` is the `n`-fold sum of the
   tautological point `𝟙 A`, and `nsmul_val` says precomposition with it
   computes `n • y` on every relative point.  Hence "`∃ w, n • w = y`" is
   literally "`y.1` factors through `[n]`" (`exists_nsmul_of_exists_comp`).
2. **For free from `ab`.** `[n] ≫ f = f`, so `[n]` is PROPER
   (`isProper_mulByNat`, via `IsProper.of_comp`) and LOCALLY OF FINITE
   TYPE (`locallyOfFiniteType_mulByNat`, via `locallyOfFiniteType_of_comp`).
   Neither uses any abelian-variety input.
3. **The leaf.** `[n]` is flat and locally of finite presentation.
4. **`[n]` is UNIVERSALLY OPEN** (`universallyOpen_mulByNat`), by
   `UniversallyOpen.of_flat`.
5. **`[n]` is SURJECTIVE** (`surjective_mulByNat`).  Its image is open by
   (4) and closed by (2), hence clopen; it meets every fibre of `f`
   because `[n]` fixes the zero section (`zeroSection_comp_mulByNat`); and
   the fibres of `f` are CONNECTED (`ab.connected`).  A clopen set meeting
   a connected set contains it, so the image is everything.  **This is the
   only place `ab.connected` is used, and it is essential**: for a
   disconnected group scheme `[n]` need not be surjective.
6. **`F̄`-points lift** (`exists_comp_eq_of_surjective`).  Base-change `[n]`
   along the point; the pullback is surjective onto `Spec F̄` hence
   nonempty, and locally of finite type over a field, hence a Jacobson
   space; a closed point of it has residue field `F̄` because `F̄` is
   algebraically closed, giving a section.  This is the Nullstellensatz
   step, and it is general scheme theory — no abelian varieties in it.

Step 6 is why the leaf may be stated about the morphism rather than about
points: the passage from "surjective as a map of schemes" to "surjective
on `F̄`-points" is proven here once and for all.

## The open leaves

**Regenerated 2026-07-29 from a comment-stripped `sorry`-token scan of this
file, not merged as prose.**  The scan reports FIVE `sorry` tokens in five
named top-level declarations — no anonymous inner `have … := sorry`, so the
direct count and the `declaration uses 'sorry'` warning count agree at 5.

The whole local-criterion-of-flatness block is now CLOSED.  In particular
`lTensor_subtype_injective_of_pow_le`, `flat_of_rTensor_injective_of_flat_quotientMap`
(Stacks 10.99.10), `flat_quotientMap_pow_of_flat_quotientMap` and
`nonempty_flatNoetherianStage_of_essFinitePresentation` are all PROVEN, as are
`topologicalKrullDim_lt_top_of_isProper` (Noether normalisation),
`height_map_le_of_isFinite` (Cohen–Seidenberg, `@[stacks 00OK]`),
`isIntegrallyClosed_of_isRegularRing`, `exists_isAmpleSheaf_cube_of_isAlgClosed`,
`flat_mulByNat`, `isDominant_of_isFinite_endo` and
`irreducibleSpace_of_smooth_geometricallyConnected`.  Every one of those was
listed here as OPEN until 2026-07-29; the list had gone stale by five bullets,
which is exactly the phantom-dispatch failure mode.  Do not trust this list —
re-run the scan.

What is genuinely open (declaration, and what it is):

* `nonempty_noetherianApproxSystem_of_baseSystem` — the noetherian
  approximation system built from a base system;
* `exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem`
  and `flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem` — the
  two remaining steps of the 10.128.3 two-tower engine
  `exists_flat_index_of_isNoetherianFlatDescentSystem`.  See the section note
  "10.128.3 IS ONE LEMMA APPLIED TWICE";
* `exists_isAmpleSheaf_symmetric_cube` — the two-variable symmetric cube, the
  primitive under BOTH `exists_isAmpleSheaf_cube_of_isAlgClosed` here and
  `exists_cubeModel_of_abelianScheme` in `ModularCurve/X0.lean`;
* `nonempty_modPullback_mulByNat_of_cube` — the theorem-of-the-cube pullback
  identity.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Modularity.AmpleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
-- `IsFinite`, `LocallyQuasiFinite` and `IsFinite.of_isProper_of_locallyQuasiFinite`
-- (Zariski's main theorem), for the shearing reduction below.  These add NOTHING to
-- any downstream cone: the module's only consumer, `Modularity/TateModule.lean`,
-- already `public import`s all three (checked 2026-07-27,
-- `grep -rn "import Fermat.FLT.Modularity.AbelianSchemeIsogeny" Fermat/`).
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- The decomposition of `flat_of_finite_fibres_endo` (miracle flatness) below.
-- `IsFinite` and `LocallyQuasiFinite` occur in the SIGNATURES of its geometric
-- leaves, and `IsRegularLocalRing` / `ringKrullDim` in the signature of its
-- commutative-algebra leaf, so all four are `public import`s and not bare ones.
-- `QuasiFinite` supplies `LocallyQuasiFinite.of_finite_preimage_singleton` and
-- `ZariskisMainTheorem` supplies `IsFinite.of_isProper_of_locallyQuasiFinite`;
-- together they turn the hypothesis "`IsProper u` with finite fibres" into
-- `IsFinite u`, which is the form all three geometric leaves consume.
-- (Those three AlgebraicGeometry modules are already `public import`ed above.)
public import Mathlib.RingTheory.RegularLocalRing.Defs
-- `flat_stalkMap_of_flat_stalkMap_fiberMapOver` and its three-leaf cut.
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
-- `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, the EQUATIONAL CRITERION of
-- flatness, is the entire flatness input of Half A of 10.128.3's colimit leaf
-- (`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem` below):
-- it converts a relation over the colimit into finitely many ring elements and
-- equations that the four `surj`/`sep` fields can descend to a finite stage, which is
-- what makes the "tensor commutes with filtered colimits" detour unnecessary.
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
-- Consumed by the PROOFS of the two leaves below.  `ResidueField.Fiber` supplies
-- `Ideal.Fiber` (the `κ(p) ⊗ S` of `Algebra.QuasiFinite.finite_fiber`) and
-- `TensorProduct.Quotient` the identification of that fibre with `T ⧸ 𝔪T`;
-- `HopkinsLevitzki` / `KrullDimension.Zero` turn "artinian" into
-- `ringKrullDim = 0`; `LocalRing.RingHom.Basic` supplies
-- `IsLocalRing.map_maximalIdeal_lt_top`.  `Regular.RegularSequence` and
-- `RingHom.Flat` (already imported just above) occur in the SIGNATURES of the
-- three sub-leaves of `flat_of_isRegularLocalRing_of_ringKrullDim_eq`, so they
-- are `public`.
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
-- `QuotSMulTop` appears in the `isWeaklyRegular_cons_iff` step of
-- `exists_isWeaklyRegular_span_eq_maximalIdeal_aux`.  It arrives transitively
-- through `Regular.RegularSequence`, but named explicitly so that a proof-body
-- use cannot be broken by a private import upstream.
public import Mathlib.RingTheory.QuotSMulTop
-- `Ideal.Quotient.isNoetherianRing`, the instance that lets the induction of
-- `flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` re-enter itself at
-- `R ⧸ (t) → T ⧸ (φ t)`.  Nothing else in the file needs it.
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
-- The unmixedness cluster (`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero`
-- and the three declarations above it).  `KrullDimension.Regular` supplies the
-- dimension drop `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`,
-- `KrullsHeightTheorem` the bound `ringKrullDim_le_ringKrullDim_quotient_add_encard`,
-- `AssociatedPrime.Basic` + `Regular.IsSMulRegular` the identification of the
-- zerodivisors with the union of the associated primes, and `Depth.Rees` the
-- REES THEOREM, which is what makes the depth descent along a nonzerodivisor a
-- theorem here rather than a leaf.  (See the correction in
-- `isWeaklyRegular_of_ringKrullDim_quotient_eq_zero`'s docstring: mathlib's
-- `RingTheory/Regular/Depth.lean` is a deprecated shim, NOT an empty file, and
-- the depth layer it used to hold now lives in `RingTheory/Depth/Rees.lean`.)
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Depth.Rees
-- Ischebeck (`ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime_aux`)
-- needs exactly three more mathlib modules: `ringKrullDim_quotient`
-- (`Spec (R ⧸ I) ≃o V(I)`) from `KrullDimension/NonZeroDivisors`, Nakayama
-- (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) from `Nakayama`, and the
-- colon ideal `(0 : p)` from `Ideal/Colon`.
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.Colon
-- The going-down half of `ringKrullDim_stalk_eq_of_isFinite_endo` below.
-- `Ideal.GoingDown` supplies `Algebra.HasGoingDown`, which occurs in the
-- SIGNATURE of the leaf `hasGoingDown_stalkMap_of_isFinite_endo`, so it is
-- `public`; `KrullsHeightTheorem` supplies Stacks 00OM/00ON
-- (`Ideal.height_le_height_add_of_liesOver`,
-- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) and `Ideal.Height`
-- the identification `(maximalIdeal R).height = ringKrullDim R`.
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height
-- Krull's going-down theorem for integrally closed domains, `@[stacks 00H8]`,
-- as an INSTANCE — this is what discharges going down on an affine chart in
-- `generalizingMap_of_isFinite_of_isIntegral` below.
public import Mathlib.RingTheory.IntegralClosure.GoingDown
-- The four modules under `isIntegrallyClosed_of_isRegularRing` below (a regular
-- ring is normal).  `LocalProperties.IntegrallyClosed` is the local-to-global
-- step for DOMAINS (`IsIntegrallyClosed.of_localization_maximal`);
-- `DiscreteValuationRing.TFAE` supplies the implication "noetherian local domain
-- with PRINCIPAL maximal ideal ⟹ integrally closed", which is what discharges
-- `A_(x)`; `LocalizationLocalization` identifies a localization of a
-- localization (both the prime correspondence and
-- `IsFractionRing (Localization.AtPrime p) (FractionRing A)`); `Away.Basic`
-- gives `Localization.Away x = A[1/x]`, the other half of `A = A[1/x] ∩ A_(x)`.
-- All four appear only in PROOF bodies, but are `public` for the same reason the
-- rest of this header is: a private import upstream must not be able to break
-- them.
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
-- `Scheme.Hom.app_injective` for a dominant morphism to a REDUCED target, which
-- is the `FaithfulSMul` input of Krull's instance on the chart.
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
-- `isRegularLocalRing_stalk_of_smooth` below is a one-line corollary of
-- `isRegularLocalRing_stalk_of_smooth_over_field`, which was PROVEN in
-- `Modularity/KhareWintenberger.lean` — a module strictly DOWNSTREAM of this
-- one — and was HOISTED into `Modularity/RegularStalks.lean` on 2026-07-27
-- precisely so that it could be consumed here.
public import Fermat.FLT.Modularity.RegularStalks
-- `flat_quotientMap_pow_of_flat_quotientMap` below is the nilpotent half of the
-- one-element local criterion of flatness, and it is PROVEN over the single
-- general statement `Module.Flat.of_flat_quotient_of_pow_eq_bot` — the local
-- criterion for a nilpotent ideal — which lives in the shim tree because it is
-- mathlib-shaped, reusable, and (mathlib having no `Tor` long exact sequence at
-- this pin) needs a theory build that must not happen inside this file.
public import Fermat.FLT.Mathlib.RingTheory.Flat.LocalCriterion
-- The `R_λ` tower of Stacks 10.127.11 (`nonempty_noetherianLocalBaseSystem`).
-- `Adjoin.FG` supplies `is_noetherian_subring_closure`, `Localization.Submodule`
-- supplies `IsLocalization.isNoetherianRing`, and `Localization.AtPrime.Basic`
-- supplies `Ideal.primeCompl` and `IsLocalization.AtPrime.isLocalRing`.  All three
-- are `public` because `Subring`, `IsLocalization` and `Ideal.primeCompl` occur in
-- the SIGNATURES of the construction lemmas in `NoetherianApproxBase` below, not
-- only in their proof bodies.
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
-- `irreducibleSpace_of_connected_of_isDomain_stalk` below is a two-line
-- composition of `irreducibleSpace_of_isOpen_isIrreducible_nhds` and
-- `exists_isOpen_isIrreducible_nhds_of_isDomain_stalk`, which live in the shim tree
-- because the SAME argument had been written three times in this development —
-- here, in `Modularity/MoretBailly.lean` (strictly downstream of this file, so
-- unusable from it) and in `Mathlib/AlgebraicGeometry/CurveExtension.lean`
-- (whose whole `Fermat` cone is two modules, so `MoretBailly` was unusable from
-- it).  A `Mathlib`-only shim is reachable from all three.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.IrreducibleNhds
-- The dimension theory consumed by `topologicalKrullDim_lt_top_of_isProper`
-- below.  `CurveCompactification` already carries the ONE scheme-level bridge
-- that leaf needs — `AlgebraicGeometry.topologicalKrullDim_eq_iSup_coheight`,
-- "the Krull dimension of a scheme is the supremum of the coheights of its
-- points", proven there over `schemeIrreducibleClosedsOrderIso` — so it is
-- imported rather than re-derived.  Its own project cone is exactly one further
-- module (`CurveExtension`) and there is no cycle: neither file imports
-- anything under `Fermat/FLT/Modularity/`.  The three `Mathlib` lines after it
-- are the ring-level inputs (`MvPolynomial.ringKrullDim_of_isNoetherianRing`,
-- `ringKrullDim_eq_zero_of_field`, `Algebra.FiniteType.iff_quotient_mvPolynomial''`);
-- they arrive through `CurveCompactification` as well, but are named here
-- because they occur in the SIGNATURES of the two declarations below.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveCompactification
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.FiniteType

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Fermat

section MulByNat

variable {A S : Scheme.{u}} {f : A ⟶ S}

/-- **The tautological relative point** of `f : A ⟶ S`: the identity of
`A`, read as an `A`-point of `A` over the base point `f` itself. It is
the universal element of the functor of points, and it is what makes
`AbelianSchemeStruct.mulByNat` below constructible without any Yoneda
apparatus. -/
def RelPoint.self (f : A ⟶ S) : RelPoint f f := ⟨𝟙 A, Category.id_comp f⟩

/-- **Every relative point is the tautological one, pulled back along
itself.** This is the Yoneda lemma for `RelPoint`, in the only form
needed here. -/
theorem RelPoint.pre_self {T : Scheme.{u}} {g : T ⟶ S} (y : RelPoint f g) :
    RelPoint.pre y.1 y.2 (RelPoint.self f) = y :=
  Subtype.ext (Category.comp_id _)

/-! ### Relative points of a base change

The functor of points of the base change `A ×_S T ⟶ T` along `g : T ⟶ S`
is the functor of points of `A ⟶ S` restricted to base points that factor
through `g`.  Concretely, for `h : U ⟶ T`,

  `RelPoint (pullback.snd f g) h  ≃  RelPoint f (h ≫ g)`,

by the universal property of the pullback.  That bijection is
`baseChangeDown`/`baseChangeUp` below, and it is what transports the whole
`AbelianSchemeStruct` — group law, naturality and all — from `f` to its
base change.  Nothing here is specific to abelian schemes.
-/

section BaseChangePoints

open _root_.CategoryTheory.Limits

namespace RelPoint

variable {T : Scheme.{u}} (g : T ⟶ S)

/-- **A relative point of the base change, read as a relative point of `f`**:
compose with the projection `A ×_S T ⟶ A`.  The base point moves from
`h : U ⟶ T` to `h ≫ g : U ⟶ S`. -/
noncomputable def baseChangeDown {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) : RelPoint f (h ≫ g) :=
  ⟨x.1 ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

/-- **A relative point of `f` over a base point factoring through `g`, read
as a relative point of the base change**: the universal property of the
pullback.  Inverse to `baseChangeDown`. -/
noncomputable def baseChangeUp {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint f (h ≫ g)) : RelPoint (pullback.snd f g) h :=
  ⟨pullback.lift x.1 h x.2, pullback.lift_snd _ _ _⟩

@[simp] theorem baseChangeDown_val {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) :
    (baseChangeDown g x).1 = x.1 ≫ pullback.fst f g := rfl

@[simp] theorem baseChangeUp_val {U : Scheme.{u}} {h : U ⟶ T} (x : RelPoint f (h ≫ g)) :
    (baseChangeUp g x).1 = pullback.lift x.1 h x.2 := rfl

theorem baseChangeDown_baseChangeUp {U : Scheme.{u}} {h : U ⟶ T} (x : RelPoint f (h ≫ g)) :
    baseChangeDown g (baseChangeUp g x) = x :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem baseChangeUp_baseChangeDown {U : Scheme.{u}} {h : U ⟶ T}
    (x : RelPoint (pullback.snd f g) h) : baseChangeUp g (baseChangeDown g x) = x := by
  refine Subtype.ext ?_
  refine pullback.hom_ext ?_ ?_
  · simpa using pullback.lift_fst (C := Scheme.{u}) (x.1 ≫ pullback.fst f g) h _
  · simpa [x.2] using pullback.lift_snd (C := Scheme.{u}) (x.1 ≫ pullback.fst f g) h _

theorem baseChangeDown_injective {U : Scheme.{u}} {h : U ⟶ T} :
    Function.Injective (baseChangeDown (f := f) g (U := U) (h := h)) :=
  Function.LeftInverse.injective (baseChangeUp_baseChangeDown g)

/-- **`baseChangeDown` is natural**: it commutes with precomposition of
relative points.  Both sides are `h ≫ x.1 ≫ pullback.fst`, associated
differently. -/
theorem baseChangeDown_pre {U' U : Scheme.{u}} (h : U' ⟶ U) {k : U ⟶ T} {k' : U' ⟶ T}
    (hk : h ≫ k = k') (x : RelPoint (pullback.snd f g) k) :
    baseChangeDown g (RelPoint.pre h hk x) =
      RelPoint.pre h (show h ≫ (k ≫ g) = k' ≫ g by rw [← Category.assoc, hk])
        (baseChangeDown g x) :=
  Subtype.ext (Category.assoc _ _ _)

end RelPoint

end BaseChangePoints

/-- **Cancellation for `LocallyOfFinitePresentation`** (PROVEN 2026-07-26):
if `f ≫ g` is locally of finite presentation and `g` is locally of finite
TYPE, then `f` is locally of finite presentation.  Stacks 0562/01TS.

This is general scheme theory with no abelian-variety content, and it is a
gap in mathlib at this pin: `LocallyOfFiniteType` has
`locallyOfFiniteType_of_comp` and `LocallyQuasiFinite` has
`LocallyQuasiFinite.of_comp`, both via `HasRingHomProperty.of_comp`, but
`LocallyOfFinitePresentation` has neither — and it cannot use
`HasRingHomProperty.of_comp` as it stands, because that helper's
hypothesis `Q (g ∘ f) → Q g` admits no side condition, whereas the ring
statement `RingHom.FinitePresentation.of_comp_finiteType` genuinely needs
`f` of finite type.  (It must: `LocallyOfFinitePresentation` is not
cancellable outright.  A closed immersion `Spec (R/I) ⟶ Spec R` with `I`
not finitely generated is not locally of finite presentation, while its
composite with `Spec R ⟶ Spec (R/I)`'s base need not see that.)

So the proof re-runs `HasRingHomProperty.of_comp`'s four-step reduction —
affine target, affine middle, affine source, then the ring statement —
carrying the auxiliary hypothesis through each step.  `LocallyOfFiniteType`
is Zariski-local at source and target, which is exactly what makes the
extra hypothesis survive the restrictions. -/
theorem locallyOfFinitePresentation_of_comp {X Y Z : Scheme.{u}} {p : X ⟶ Y} {q : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (p ≫ q)) (h' : LocallyOfFiniteType q) :
    LocallyOfFinitePresentation p := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (q.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict h' U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (p ⁻¹ᵁ U.1).ι (p ≫ q) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFiniteType U.1.ι q h')
      inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      U.1.ι (p ≫ q) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at h'
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h h'

namespace AbelianSchemeStruct

variable (ab : AbelianSchemeStruct f)

/-- **Pullback of relative points commutes with `n`-fold addition.**
This is `pre_add` and `pre_zero` — the naturality axioms of the group
structure — read at the `ℕ`-action of the resulting `AddCommGroup`. -/
theorem pre_nsmul {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (n : ℕ) (y : RelPoint f g) :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint.pre h hg (n • y) = n • RelPoint.pre h hg y := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  induction n with
  | zero =>
      show RelPoint.pre h hg (0 • y) = 0 • RelPoint.pre h hg y
      rw [zero_nsmul, zero_nsmul]
      exact ab.pre_zero h hg
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      show RelPoint.pre h hg (ab.add (n • y) y)
          = ab.add (n • RelPoint.pre h hg y) (RelPoint.pre h hg y)
      rw [ab.pre_add h hg, ih]

/-- **Multiplication by `n`, as a MORPHISM of schemes `A ⟶ A`**: the
underlying morphism of the `n`-fold sum of the tautological relative
point `RelPoint.self f`.

By `nsmul_val` this really is `[n]`: precomposition with it computes
`n • y` on every relative point, so it is the Yoneda realization of the
endomorphism `y ↦ n • y` of the functor of points. No fibre products
and no chosen pullbacks are needed to write it down. -/
noncomputable def mulByNat (n : ℕ) : A ⟶ A :=
  letI := ab.addCommGroup f
  (n • RelPoint.self f).1

/-- **`n`-fold addition of relative points IS precomposition with
`mulByNat n`.** -/
theorem nsmul_val {T : Scheme.{u}} {g : T ⟶ S} (n : ℕ) (y : RelPoint f g) :
    letI := ab.addCommGroup g
    (n • y).1 = y.1 ≫ ab.mulByNat n := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup f
  conv_lhs => rw [← RelPoint.pre_self y]
  rw [← ab.pre_nsmul y.1 y.2 n (RelPoint.self f)]
  rfl

/-- **The zero section** `S ⟶ A`, i.e. the unit of the group scheme. -/
noncomputable def zeroSection : S ⟶ A := (ab.zero (𝟙 S)).1

/-- **Every zero relative point is the zero section, precomposed.** -/
theorem zero_val {T : Scheme.{u}} (g : T ⟶ S) :
    (ab.zero g).1 = g ≫ ab.zeroSection :=
  congrArg Subtype.val (ab.pre_zero (h := g) (g := 𝟙 S) (g' := g) (Category.comp_id g)).symm

/-- **`mulByNat n` is a morphism over `S`.** -/
theorem mulByNat_comp (n : ℕ) : ab.mulByNat n ≫ f = f :=
  letI := ab.addCommGroup f
  (n • RelPoint.self f).2

/-- **`[1]` is the identity** (PROVEN 2026-07-26).  `1 • self = self`, and
the underlying morphism of the tautological point is `𝟙 A` by definition. -/
theorem mulByNat_one : ab.mulByNat 1 = 𝟙 A := by
  letI := ab.addCommGroup f
  show (1 • RelPoint.self f).1 = 𝟙 A
  rw [one_smul]
  rfl

/-- **`[0]` IS THE CONSTANT MAP THROUGH THE ZERO SECTION**, `[0] = f ≫ e`
(PROVEN 2026-07-30) — `zero_smul` and `zero_val`.

This is the base case `n = 0` of `nonempty_modPullback_mulByNat_of_cube` below,
and it is also exactly why that statement needs its NORMALIZATION hypothesis:
`[0]^* L = f^*(e^* L)` is trivial only once `e^* L ≅ 𝒪_S` is known. -/
theorem mulByNat_zero : ab.mulByNat 0 = f ≫ ab.zeroSection := by
  letI := ab.addCommGroup f
  show (0 • RelPoint.self f).1 = _
  rw [zero_smul]
  exact ab.zero_val f

/-- **`[m·n] = [n] ≫ [m]`** (PROVEN 2026-07-26): `n ↦ [n]` is multiplicative,
i.e. `ℕ ⟶ End(A)` is a monoid map (note the order reversal, since `≫` is
diagrammatic composition and `[m]` is applied last).

This is `nsmul_val` read at the relative point `n • RelPoint.self f`:
`(m • (n • self)).1 = (n • self).1 ≫ [m]`, and `smul_smul` rewrites the
left side to `((m * n) • self).1 = [m * n]`.

**Why it matters.**  It is what reduces flatness of `[n]` to flatness of
`[p]` for `p` PRIME (`flat_mulByNat` below), because flatness of scheme
morphisms is stable under composition.  No route to the leaf avoids it. -/
theorem mulByNat_mul (m n : ℕ) :
    ab.mulByNat (m * n) = ab.mulByNat n ≫ ab.mulByNat m := by
  letI := ab.addCommGroup f
  have h := ab.nsmul_val m (n • RelPoint.self f)
  rw [smul_smul] at h
  exact h

/-- **`mulByNat n` is PROPER**, for free: it commutes with the structure
morphism `f`, which is proper by `ab.proper`, and a morphism whose
composite with a SEPARATED morphism is proper is itself proper
(`IsProper.of_comp`). No abelian-variety input whatsoever. -/
theorem isProper_mulByNat (n : ℕ) : IsProper (ab.mulByNat n) := by
  haveI := ab.proper
  haveI : IsProper (ab.mulByNat n ≫ f) := by rw [ab.mulByNat_comp]; exact ab.proper
  exact IsProper.of_comp _ f

/-! ### The zero section, and finite type — both free -/

/-- **The zero section is a section of `f`** — the second component of
the relative point `ab.zero (𝟙 S)`, read out. -/
theorem zeroSection_comp : ab.zeroSection ≫ f = 𝟙 S := (ab.zero (𝟙 S)).2

/-- **`[n]` fixes the zero section**, `[n] ∘ e = e`.  This is `n • 0 = 0`
in the group of `S`-points, transported through `nsmul_val`.  It is what
makes the image of `[n]` meet every fibre of `f`, which is the
nonemptiness half of the connectedness argument in
`surjective_mulByNat`. -/
theorem zeroSection_comp_mulByNat (n : ℕ) :
    ab.zeroSection ≫ ab.mulByNat n = ab.zeroSection := by
  letI := ab.addCommGroup (𝟙 S)
  have hz : (n • (ab.zero (𝟙 S)) : RelPoint f (𝟙 S)) = ab.zero (𝟙 S) := by
    show (n • (0 : RelPoint f (𝟙 S))) = (0 : RelPoint f (𝟙 S))
    exact smul_zero n
  have h := ab.nsmul_val n (ab.zero (𝟙 S))
  rw [hz] at h
  exact h.symm

/-- **`[n]` is LOCALLY OF FINITE TYPE**, for free, exactly as it is
proper: `[n] ≫ f = f` is locally of finite type because `f` is smooth,
and `locallyOfFiniteType_of_comp` cancels the second factor (no
separatedness hypothesis is needed for this one).

No abelian-variety input.  This is what lets the geometric fibre of `[n]`
be a Jacobson space in `exists_comp_eq_of_surjective`, and it is the
reason the leaf below need not assert finiteness of `[n]`. -/
theorem locallyOfFiniteType_mulByNat (n : ℕ) : LocallyOfFiniteType (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFiniteType (ab.mulByNat n ≫ f) := by
    rw [ab.mulByNat_comp]; infer_instance
  exact locallyOfFiniteType_of_comp (ab.mulByNat n) f

/-- **`[n]` is LOCALLY OF FINITE PRESENTATION**, also for free (PROVEN
2026-07-26).

`[n] ≫ f = f` is locally of finite presentation because `f` is smooth,
and `f` is locally of finite type, so `locallyOfFinitePresentation_of_comp`
above cancels the second factor.

This matters for the leaf below: it is the reason the theorem of the cube
has to supply only FLATNESS.  Mathlib's `UniversallyOpen.of_flat` wants
`Flat` *and* `LocallyOfFinitePresentation`, and the second of the two is
not an abelian-variety fact at all. -/
theorem locallyOfFinitePresentation_mulByNat (n : ℕ) :
    LocallyOfFinitePresentation (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFinitePresentation (ab.mulByNat n ≫ f) := by
    rw [ab.mulByNat_comp]; infer_instance
  exact locallyOfFinitePresentation_of_comp this inferInstance

/-- **The Yoneda translation of divisibility** (PROVEN): a relative point
`y` is `n`-divisible in the group `RelPoint f g` exactly when its
underlying morphism factors through `[n]`.

The factorization automatically lies over `g`: if `w ≫ [n] = y.1` then
`w ≫ f = w ≫ [n] ≫ f = y.1 ≫ f = g`, so no compatibility has to be
supplied by the caller.  That is the whole reason the geometric input can
be a statement about the MORPHISM `[n]` rather than about the group of
points. -/
theorem exists_nsmul_of_exists_comp {T : Scheme.{u}} {g : T ⟶ S} (n : ℕ)
    (y : RelPoint f g) (h : ∃ w : T ⟶ A, w ≫ ab.mulByNat n = y.1) :
    letI := ab.addCommGroup g
    ∃ w : RelPoint f g, n • w = y := by
  letI := ab.addCommGroup g
  obtain ⟨w, hw⟩ := h
  have hwf : w ≫ f = g := by
    have hb : w ≫ (ab.mulByNat n ≫ f) = g := by
      rw [← Category.assoc, hw]; exact y.2
    rwa [ab.mulByNat_comp] at hb
  refine ⟨⟨w, hwf⟩, Subtype.ext ?_⟩
  rw [ab.nsmul_val n ⟨w, hwf⟩]
  exact hw

/-! ### Base change of an abelian scheme

An abelian scheme stays an abelian scheme after any base change `g : T ⟶ S`,
and multiplication by `n` base-changes to multiplication by `n`.  Both are
formal: the group law transports through the bijection of §"Relative points
of a base change", and properness, smoothness and geometric connectedness
are stable under base change in mathlib.

This is what lets the finiteness leaf below be stated over a FIELD: the
fibre `f.fiber s = A ×_S Spec κ(s)` carries an `AbelianSchemeStruct` over
`Spec κ(s)`, i.e. it is an abelian VARIETY, and `[n]` on it is the
restriction of `[n]` on `A`.
-/

section BaseChange

open _root_.CategoryTheory.Limits

/-- **Base change of an abelian scheme structure** along `g : T ⟶ S`.

The group law is transported through the bijection
`RelPoint (pullback.snd f g) h ≃ RelPoint f (h ≫ g)`; properness,
smoothness and geometric connectedness come from mathlib's
`IsStableUnderBaseChange` instances for the three properties. -/
noncomputable def baseChange (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S) :
    AbelianSchemeStruct (pullback.snd f g) where
  add := fun {_} {_} x y =>
    RelPoint.baseChangeUp g (ab.add (RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g y))
  zero := fun {_} h => RelPoint.baseChangeUp g (ab.zero (h ≫ g))
  neg := fun {_} {_} x => RelPoint.baseChangeUp g (ab.neg (RelPoint.baseChangeDown g x))
  add_assoc := by
    intro U h x y z
    rw [RelPoint.baseChangeDown_baseChangeUp, RelPoint.baseChangeDown_baseChangeUp,
      ab.add_assoc]
  add_comm := by
    intro U h x y
    rw [ab.add_comm]
  zero_add := by
    intro U h x
    rw [RelPoint.baseChangeDown_baseChangeUp, ab.zero_add,
      RelPoint.baseChangeUp_baseChangeDown]
  neg_add := by
    intro U h x
    rw [RelPoint.baseChangeDown_baseChangeUp, ab.neg_add]
  pre_add := by
    intro U' U h k k' hk x y
    apply RelPoint.baseChangeDown_injective g
    simp only [RelPoint.baseChangeDown_pre, RelPoint.baseChangeDown_baseChangeUp]
    exact ab.pre_add h _ _ _
  pre_zero := by
    intro U' U h k k' hk
    apply RelPoint.baseChangeDown_injective g
    simp only [RelPoint.baseChangeDown_pre, RelPoint.baseChangeDown_baseChangeUp]
    exact ab.pre_zero h _
  proper := by haveI := ab.proper; infer_instance
  smooth := by haveI := ab.smooth; infer_instance
  connected := by haveI := ab.connected; infer_instance

@[simp] theorem baseChange_add (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (x y : RelPoint (pullback.snd f g) h) :
    (ab.baseChange g).add x y =
      RelPoint.baseChangeUp g
        (ab.add (RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g y)) := rfl

@[simp] theorem baseChange_zero (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} (h : U ⟶ T) :
    (ab.baseChange g).zero h = RelPoint.baseChangeUp g (ab.zero (h ≫ g)) := rfl

/-- **`baseChangeDown` is additive**, hence commutes with the `ℕ`-action. -/
theorem baseChangeDown_nsmul (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    {U : Scheme.{u}} {h : U ⟶ T} (n : ℕ) (x : RelPoint (pullback.snd f g) h) :
    letI := (ab.baseChange g).addCommGroup h
    letI := ab.addCommGroup (h ≫ g)
    RelPoint.baseChangeDown g (n • x) = n • RelPoint.baseChangeDown g x := by
  letI := (ab.baseChange g).addCommGroup h
  letI := ab.addCommGroup (h ≫ g)
  induction n with
  | zero =>
      show RelPoint.baseChangeDown g (0 • x) = 0 • RelPoint.baseChangeDown g x
      rw [zero_nsmul, zero_nsmul]
      show RelPoint.baseChangeDown g ((ab.baseChange g).zero h) = ab.zero (h ≫ g)
      rw [baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul]
      show RelPoint.baseChangeDown g ((ab.baseChange g).add (n • x) x)
          = ab.add (n • RelPoint.baseChangeDown g x) (RelPoint.baseChangeDown g x)
      rw [baseChange_add, RelPoint.baseChangeDown_baseChangeUp, ih]

/-- **`[n]` base-changes to `[n]`**: multiplication by `n` on the base
change `A ×_S T` is the base change of multiplication by `n` on `A`,
expressed as the commuting square with the projection `A ×_S T ⟶ A`.

This is the compatibility that makes the reduction to a field base
legitimate: on the fibre `f.fiber s ⟶ A` the morphism `[n]` of the fibre
is the restriction of `[n]` on `A`, so the two have the same point-set
fibres. -/
theorem baseChange_mulByNat (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S) (n : ℕ) :
    (ab.baseChange g).mulByNat n ≫ pullback.fst f g
      = pullback.fst f g ≫ ab.mulByNat n := by
  letI := (ab.baseChange g).addCommGroup (pullback.snd f g)
  letI := ab.addCommGroup (pullback.snd f g ≫ g)
  letI := ab.addCommGroup f
  have hp : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
  have h1 : RelPoint.baseChangeDown g (n • RelPoint.self (pullback.snd f g))
      = n • RelPoint.baseChangeDown g (RelPoint.self (pullback.snd f g)) :=
    ab.baseChangeDown_nsmul g n _
  have h2 : RelPoint.baseChangeDown g (RelPoint.self (pullback.snd f g))
      = RelPoint.pre (pullback.fst f g) hp (RelPoint.self f) :=
    Subtype.ext (by simp [RelPoint.baseChangeDown, RelPoint.self, RelPoint.pre])
  have h3 : n • RelPoint.pre (pullback.fst f g) hp (RelPoint.self f)
      = RelPoint.pre (pullback.fst f g) hp (n • RelPoint.self f) :=
    (ab.pre_nsmul _ hp n _).symm
  exact congrArg Subtype.val (h1.trans (by rw [h2, h3]))

end BaseChange

end AbelianSchemeStruct

/-! ### The fibrewise reduction, and the theorem of the cube on a fibre

`flat_mulByNat` used to be a single leaf over an ARBITRARY base scheme
`S`, and in that form it is not attackable: the classical proof
("miracle flatness") needs `A` to be REGULAR, which is false over a
general base — `A` is smooth over `S`, so it is only as regular as `S`
is, and `S` is arbitrary here.  The classical argument lives on the
FIBRES, where the base is a field and smoothness does give regularity.

So the leaf is now cut in two along exactly that seam:

* `flat_of_flat_fiberMap` — the **fibrewise criterion of flatness**
  (EGA IV 11.3.10, *critère de platitude par fibres*; Stacks 039E).
  Pure scheme theory: no group scheme, no abelian variety, no `[n]`.
* `flat_fiberMap_mulByNat` — `[p]` is flat **on every fibre**, for `p`
  prime.  This was the abelian-variety half; it is **PROVEN since
  2026-07-27** and is no longer a leaf.

`flat_mulByNat` itself is PROVEN over the two, together with
`mulByNat_mul` (which does the reduction from general `n` to primes).

**The second cut, 2026-07-27 — and where the declarations now live.**
`flat_fiberMap_mulByNat` was closed by carrying the split one step
further, along the seam between the group law and the commutative
algebra.  Over a fibre the base is `Spec κ(s)`, and
`AbelianSchemeStruct.baseChange` — which already existed — makes the
fibre a genuine abelian VARIETY, with `baseChange_mulByNat` identifying
`fiberMapOver [p]` as its own `[p]`.  That reduces the fibre statement to
`flat_mulByNat_of_field`, which in turn splits with NO residue into:

* `finite_preimage_mulByNat_of_field` — the theorem of the cube, and now
  the ONLY leaf in this chain carrying abelian-variety content.  It
  already existed, as the input the torsion CARDINALITY arguments need;
  it is untouched.
* `flat_of_finite_fibres_endo` — **miracle flatness** (Matsumura
  *Commutative Ring Theory* Thm 23.1) in endomorphism form: a proper
  endomorphism with finite fibres of a smooth proper geometrically
  connected scheme over a field is flat.  Pure commutative algebra: no
  group scheme, no abelian variety, no `[n]`.  Declared just below, next
  to `flat_of_flat_fiberMap`, because the two are siblings — both are
  general theorems that would be at home in mathlib.

So the abelian-variety input of the whole divisibility chain is now
concentrated in ONE leaf, where it previously appeared twice.

Declaration ORDER changed to make this possible: `flat_fiberMap_mulByNat`
and `flat_mulByNat` now sit BELOW `finite_preimage_mulByNat`, since they
consume the cube leaf.  They moved down rather than the leaf moving up,
deliberately — that leaf had a live owner, and relocating a declaration
out from under the agent proving it is how merge conflicts get
manufactured here.
-/

/-- **The morphism induced on scheme-theoretic fibres** over a point `s`
of the base by a morphism `u` commuting with the two structure
morphisms.

`Scheme.Hom.fiber p s` is `pullback p (S.fromSpecResidueField s)`, the
fibre over the residue field `κ(s)`, so this is `pullback.map` with the
identity on both the base point and the residue field.  It is the object
the fibrewise criterion of flatness talks about. -/
noncomputable def fiberMapOver {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) : p.fiber s ⟶ q.fiber s :=
  Limits.pullback.map p (S.fromSpecResidueField s) q (S.fromSpecResidueField s)
    u (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id]; exact h.symm)
    (by rw [Category.comp_id, Category.id_comp])

/-! ### The pointwise fibre criterion, cut into ring theory + two transports

`flat_stalkMap_of_flat_stalkMap_fiberMapOver` (Stacks 039C) used to be a
single opaque leaf, and its docstring recorded that it **could not honestly
be restated over abstract local rings** because "essentially of finite
presentation" does not exist in the pin.  That inference is the standard
one this fleet's doctrine warns about — *stating* a notion is not *proving*
anything about it.  The notion is a five-line definition
(`EssFinitePresentation` below), and once it is written the leaf decomposes
with **no residue** into

* `flat_of_flat_of_flat_quotientMap` — the ring-level *critère de platitude
  par fibres*, **Stacks 05UV verbatim**, over abstract local rings.  This is
  where all the missing mathematics now lives (Tor, the local criterion,
  and the limit argument);
* `essFinitePresentation_stalkMap` — the stalk of a morphism locally of
  finite presentation is essentially of finite presentation.  The exact
  analogue of mathlib's `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`
  (`Morphisms/FiniteType.lean:99`), which supplies the OTHER finiteness
  hypothesis (`EssFiniteType`) for free;
* `flat_quotientMap_of_flat_stalkMap_fiberMapOver` — "the stalk of the
  fibre is the base change of the stalk", in the flatness form the criterion
  consumes.

**Why 05UV and not 00MP.**  The Noetherian local engine 00MP cannot be used
here: `S` is an arbitrary scheme, so its stalks are arbitrary local rings.
05UV (= Algebra Lemma 10.128.9) is the non-Noetherian local-ring form, and
its hypotheses were checked against the source on 2026-07-27:

> Let `R`, `S`, `S'` be local rings and let `R → S → S'` be local ring
> homomorphisms.  Let `M` be an `S'`-module and `𝔪` the maximal ideal of
> `R`.  Assume (1) `R → S'` is essentially of finite presentation, (2)
> `R → S` is essentially of finite type, (3) `M` is of finite presentation
> over `S'`, (4) `M` is not zero, (5) `M/𝔪M` is a flat `S/𝔪S`-module, (6)
> `M` is a flat `R`-module.  Then `S` is essentially of finite presentation
> and flat over `R` and `M` is a flat `S`-module.

Note (2) is *finite type*, not presentation — that is exactly why this is
the right form to cut along, since `LocallyOfFiniteType.stalkMap` already
delivers it.

**A CORRECTION about 00R7 (2026-07-27).**  The previous version of this
paragraph ended "Its sibling 00R7 (10.128.8) demands essential finite
presentation on BOTH maps and is therefore the wrong one to reach for."  The
first half is true and the conclusion is backwards: **05UV's own Stacks proof
is an application of 00R7.**  Read verbatim, it writes `S` as `B/J` with
`R → B` essentially of finite presentation, proves `J` finitely generated by
applying **00R7** to `R → B/J' → S'` for finitely generated `J' ⊆ J` and then
**046Y (10.128.4)** to see that any two such `J'` agree, and finishes: "Thus
we may apply Lemma 10.128.8 to `R → S → S'` and we win."

So 00R7 is not a wrong turn — it is the engine, and the extra content of 05UV
over it is exactly the finite-generation argument for `J`.  A prover should
NOT attack 05UV directly.

Instantiating `M = S' = 𝒪_{X,x}`, `S = 𝒪_{Y,y}`, `R = 𝒪_{S,s}` makes (3)
automatic (a ring is finitely presented over itself) and (4) automatic (a
local ring is nontrivial), which is why neither appears below.
-/

/-- **Essentially of finite presentation**, for a ring homomorphism: `φ`
factors as a finitely presented ring map followed by a localization.

This is the exact analogue of mathlib's `Algebra.EssFiniteType` — whose
docstring reads "an `R`-algebra is essentially of finite type if it is the
localization of an algebra of finite type" — with *finite type* replaced by
*finite presentation*, and it is the standard definition (Stacks; EGA IV
1.4).  It is stated for ring homs rather than algebras because that is the
shape the stalk maps come in.

**Why it is not a `Subalgebra`.**  Mathlib's `EssFiniteType` is equivalently
witnessed by a sub*algebra* of the target
(`essFiniteType_iff_exists_subalgebra`), because the image of a finite-type
algebra is again of finite type.  **That equivalence FAILS for finite
presentation** — the image of a finitely presented algebra need not be
finitely presented — so the intermediate ring `T` here genuinely has to be
abstract, and copying the `EssFiniteType` idiom would have produced a
strictly stronger, and hence possibly FALSE, notion.

Belongs in mathlib next to `Algebra.EssFiniteType`; it is declared here only
to avoid a new module.  `grep -rn "EssFinitePresentation"
.lake/packages/mathlib ~/cs/FLT` returned nothing on 2026-07-27. -/
def EssFinitePresentation {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  ∃ (T : Type u) (_ : CommRing T) (g : R →+* T) (v : T →+* S) (M : Submonoid T),
    g.FinitePresentation ∧ v.comp g = φ ∧ @IsLocalization T _ M S _ v.toAlgebra

/-- Ideal bookkeeping: `I·B` lands in the contraction of `I·A` along `B → A`.
This exists only to give the fibre hypothesis of
`flat_of_flat_of_flat_quotientMap` a stable, nameable proof term, so that the
statement below elaborates the same way at every use site. -/
theorem map_le_comap_map_comp {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    (g : R →+* B) (v : B →+* A) (I : Ideal R) :
    I.map g ≤ (I.map (v.comp g)).comap v := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  exact Ideal.le_comap_map

/-!
### CRITÈRE DE PLATITUDE PAR FIBRES, ring level — Stacks 05UV

**SECTION NOTE for the three declarations that follow.**  This block used to
be the docstring of a single sorry leaf `flat_of_flat_of_flat_quotientMap`.
On 2026-07-27 that leaf was CUT along the source's own seam into

* `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation` — **00R7**, the
  engine.  **PROVEN later the same day** over its own two-way cut
  `approximation + 00MP`; see the section note "00R7 CUT" immediately below
  for the filtered-system design decision that produced it, and read that note
  before touching the approximation leaf;
* `essFinitePresentation_of_essFiniteType_of_flat_quotientMap` — the
  **finite-generation of `J`**, 05UV's other conclusion.  **PROVEN
  2026-07-27** by writing out 05UV's own presentation step; the presentation
  bookkeeping — `exists_essFinitePresentation_surjective_of_essFiniteType` and
  `essFinitePresentation_comp_of_fg_ker` — is proven, needing nothing that
  was missing from the pin, and so, later the same day, is
  `fg_ker_of_flat_quotientMap` ("`J` is finitely generated") itself;
* `flat_of_flat_of_flat_quotientMap` — now **PROVEN**, a two-line assembly of
  those two, exactly as 05UV's proof ends.

So the ONE open node of this block is now
`flat_of_flat_of_flat_quotientMap_of_essFinitePresentation` (00R7), i.e. its two
leaves `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation_of_noetherian`
(approximation) and `flat_of_rTensor_injective_of_flat_quotientMap` (the
Noetherian local criterion), and the survey below applies to them.  **The
finite-generation half is closed**: it needed neither Noetherian approximation
nor `Tor` — see the section note "05UV's FINITE-GENERATION ARGUMENT" below,
which records the specific claim of the survey below that is false for it.

Everything below is the route audit that produced that cut, retained verbatim
because each of its claims is paired with the grep that refutes it if it goes
stale.  Read the two leaves' own docstrings for what each now costs.

PURE COMMUTATIVE ALGEBRA, no schemes, no group schemes: **Stacks 05UV** =
Algebra Lemma 10.128.9, the non-Noetherian local-ring form; Noetherian case
Stacks 00MP; Matsumura *Commutative Ring Theory* §23 and EGA IV 11.3.10 for
the classical account.

*Let `R → B → A` be local homomorphisms of local rings, with `R → A`
essentially of finite presentation and `R → B` essentially of finite type.
If `A` is flat over `R` and `A/𝔪_R A` is flat over `B/𝔪_R B`, then `A` is
flat over `B`.*

**FAITHFULNESS — this is 05UV instantiated at `M = S' = A`, with the source
quoted in the section note above.**  Hypotheses (3) `M` of finite
presentation over `S'` and (4) `M ≠ 0` are omitted because at `M = S' = A`
they are theorems, not assumptions: `A` is finitely presented over itself,
and `[IsLocalRing A]` already gives `Nontrivial A`.  The conclusion is
likewise *weaker* than 05UV's, which also asserts that `B` is essentially of
finite presentation and flat over `R`; only `A` flat over `B` is kept,
because only that is consumed.  A weaker conclusion and fewer hypotheses
cannot turn a true statement false, so this leaf is safe in both directions.

**This is where ALL the missing mathematics now is**, and the survey below
is what a prover faces (each claim paired with the grep that refutes it if
it goes stale; all re-run against the pin on 2026-07-27):

* **Tor of modules over a ring is ABSENT.**  `grep -rn "^def Tor" Mathlib/`
  finds only the abstract monoidal `CategoryTheory.Monoidal.Tor` — whose own
  file carries `assert_not_exists ModuleCat.abelian`, i.e. it is
  *deliberately* disconnected from modules — and the group-homology
  `Rep k G` version.  `Mathlib/RingTheory/Flat/CategoryTheory.lean:27`
  carries the literal TODO `- Relate flatness with Tor`.  **`Ext` for
  modules DOES exist** (`HasExt (ModuleCat.{v} R)`), so the asymmetry is
  real and worth knowing: the derived-functor apparatus is present, only the
  `Tor` half is unbuilt.
* **The local criterion of flatness is ABSENT.**  `grep -rin "local
  criterion" Mathlib/` returns nothing.  But note two ingredients that ARE
  present and that a naive survey misses:
  `Module.Flat.iff_rTensor_injective'` (`Flat/Tensor.lean:67`) is exactly
  "`Tor₁(R/I, M) = 0` for every ideal `I`" written without Tor, and
  `Module.free_of_maximalIdeal_rTensor_injective`
  (`LocalRing/Module.lean:248`) is the local criterion itself in the
  finitely-*presented* case: `𝔪 ⊗ M → M` injective plus `FinitePresentation`
  gives `Free`.
  **STILL TRUE OF MATHLIB, NO LONGER TRUE OF THIS FILE (2026-07-27):** the
  Noetherian local criterion `flat_of_rTensor_injective_of_flat_quotientMap`
  (Stacks 10.99.10) is now PROVEN below, over a single homological leaf.  Its
  Noetherian content — Artin–Rees + Krull, which is what the "ideally
  separated" hazard in the next bullet is really about — is written out; see the
  section note "10.99.10 CUT".  A sweep that concludes "the local criterion is
  missing" should say *missing from the pin*, not *missing here*.

**ROUTE AUDIT, 2026-07-27 — a CORRECTION to the sentence that used to end
that bullet.**  It read: "The gap is precisely that a stalk is essentially,
not actually, of finite presentation."  That is **wrong**, and it is wrong in
the direction that sends a prover at a non-existent one-line weakening, so it
is corrected rather than merely qualified.  The check that refutes it is to
read the mathlib statement:

    theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
        (H : Function.Injective ((𝔪).subtype.rTensor M)) : Module.Free R M

Its hypothesis is `Module.FinitePresentation R M` — finite presentation of a
**module**.  What this leaf has is `EssFinitePresentation` of a ring
**homomorphism** `B →+* A`.  Those are not comparable notions and neither
implies the other: a stalk `A` of a smooth morphism of positive relative
dimension is essentially of finite presentation over `B` as an algebra while
being nowhere near finitely generated as a `B`-module.  So the step from
*finitely* to *essentially* finitely presented is **not** the missing step,
and "weaken `FinitePresentation` to `EssFinitePresentation` in
`free_of_maximalIdeal_rTensor_injective`" is not a task that can be
dispatched — it does not typecheck as a task.

**A second hazard on the same route, flagged rather than asserted.**  Before
cutting this leaf along a local criterion at all, check the criterion's
hypotheses in the NON-Noetherian setting: the classical statement (Matsumura
*Commutative Ring Theory* Thm 22.3; Bourbaki) requires the module to be
*ideally separated*, which Noetherianness supplies for free and which this
leaf's setting — `S` an arbitrary scheme, so `R` an arbitrary local ring —
does not.  A sub-leaf of the shape "`𝔫 ⊗_B A → A` injective ⟹ `A` flat over
`B`", stated with no separatedness hypothesis, is exactly the sort of leaf
that can be FALSE, and a false sub-leaf is worse than the open node it
replaces.  Verify against the source before writing one.  That this is a
real distinction and not pedantry is visible in the Stacks project itself:
05UV is stated separately from the Noetherian 00MP precisely because the
Noetherian engine does not reach it.

**THE ACTUAL DEPENDENCY CHAIN, read off the Stacks proofs on 2026-07-27.**
This replaces the guess that the missing pieces are "Tor, the local criterion
and a limit argument", which is right in outline and wrong in the one place
that decides how to attack this:

    05UV (10.128.9)  =  00R7  +  "J is finitely generated"  +  046Y (10.128.4)
    00R7 (10.128.8)  =  Noetherian approximation (10.127.13, 10.128.3)
                        +  00MP (10.99.15)
    046Y (10.128.4)  =  the same approximation  +  10.99.1

Two consequences, both of which change the plan:

* **The local criterion is only ever needed in the NOETHERIAN setting.**
  00MP is 10.99.15 verbatim: *"Let `R`, `S`, `S'` be **Noetherian** local
  rings and `R → S → S'` local homomorphisms, `M` an `S'`-module, `𝔪 ⊂ R` the
  maximal ideal.  Assume (1) `M` finite over `S'`, (2) `M ≠ 0`, (3) `M/𝔪M`
  flat over `S/𝔪S`, (4) `M` flat over `R`.  Then `S` is flat over `R` and `M`
  is a flat `S`-module."*  Note `M` **finite**, not finitely presented, and
  every ring Noetherian.  Its own proof cites only Nakayama (10.20.1) and the
  local-criterion family 10.99.7 / 10.99.10 / 10.39.15.
* **Therefore the "ideally separated" hazard flagged above is real but
  AVOIDABLE.**  The Stacks route never proves a non-Noetherian local
  criterion; it approximates down to the Noetherian case where ideal
  separatedness is free.  So the whole non-Noetherian content of this leaf is
  the **approximation/limit machinery**, not the criterion.  Anyone planning
  to build a non-Noetherian local criterion for this leaf is building
  something the source does not use.

**What a safe cut would therefore need**, in increasing order of cost:
`00MP` (a self-contained Noetherian statement, writable today over
`IsNoetherianRing` and `IsLocalRing` with no new definitions); `10.99.1`
(likewise); and the approximation half — writing an essentially-of-finite-type
local ring map as a filtered colimit of such maps of **Noetherian** local
rings (10.127.13), plus descent of flatness along that colimit (10.128.3).
The last two are the ones that need a design decision about how to state a
filtered system of rings in this development, and getting that wrong
manufactures a useless or false leaf, so they are deliberately NOT cut here.

**AXIS SEARCHED** (so the next reader knows what this audit did NOT look
at): routes that cut this leaf along ring-theoretic machinery — Tor, the
local criterion of flatness, and Noetherian approximation/spreading out.
All three are absent from the pin, by the greps above and below, re-run
2026-07-27.

**THE ONE UNSEARCHED AXIS HAS NOW BEEN SEARCHED, AND IT IS A DEAD END**
(2026-07-27).  The previous version of this paragraph named it as "the first
thing to check before anyone commits to building Tor": whether the CONSUMER
always supplies a Noetherian base, in which case the far cheaper Noetherian
form 00MP would suffice.  **It does not.**  The chain is
`flat_of_flat_of_flat_quotientMap` → `flat_stalkMap_of_flat_stalkMap_fiberMapOver`
→ `flat_of_flat_fiberMap` → `flat_mulByNat` → `AbelianSchemeStruct`, and
`AbelianSchemeStruct f` is declared in `Modularity/AbelianScheme.lean` for an
arbitrary `f : A ⟶ S` with `S : Scheme.{u}` and NO finiteness hypothesis on
`S` whatever — that file contains zero occurrences of the string
"Noetherian".  Every consumer above it quantifies over arbitrary `S` too:
`Modularity/TateModule.lean` (`exists_nsmul_eq_geomFibrePt` and the whole
`TatePt` development), `ModularCurve/X0.lean`, and
`Modularity/KhareWintenberger.lean`.  The refuting check is one line:
`grep -rn "Noetherian" Fermat/FLT/Modularity/AbelianScheme.lean`; a hit means
this note has gone stale.

So 00MP does not reach the consumer either, and replacing this leaf by the
Noetherian form would require adding a Noetherian hypothesis to
`AbelianSchemeStruct` and propagating it through four owned files — a
cut-level restatement, not a simplification of this leaf.  05UV stands.
* **Spreading out / absolute Noetherian approximation is ABSENT.**
  `grep -rni "noetherian approximation" Mathlib/` returns nothing.
  `AffineTransitionLimit.lean` descends *morphisms* along cofiltered limits
  (`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation:1230`) but
  not the *property*, so EGA IV 8.8.2 is not available.
* **Cohen–Macaulay, depth, generic flatness, openness of the flat locus are
  ABSENT.**  `grep -rn CohenMacaulay Mathlib/` is empty,
  `RingTheory/Regular/Depth.lean` is a 10-line stub with zero declarations,
  and `grep -rln "flatLocus\|genericFlat" Mathlib/` is empty.
* `~/cs/FLT` has none of it either.

A hit on any of those greps means this note has gone stale and the leaf is
cheaper than it looks.
-/

/-! ### 00R7 CUT — the filtered-system design decision, TAKEN 2026-07-27

**SECTION NOTE for the six declarations that follow, and for the 00R7 leaf
below them.**  Until 2026-07-27 `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation`
(Stacks **00R7**) was deliberately ATOMIC, and its own docstring said why:

> Stating a filtered system of rings is a design decision, and a wrong one
> manufactures a false or useless sub-leaf; so 00R7 is left ATOMIC rather than
> split into `00MP + approximation`, because the assembly of those two is
> exactly the piece that cannot be written without first making that decision.
> Stating 00MP alone would leave it FREE-FLOATING — no consumer could be
> written — which this development forbids.

The decision has now been taken.  It is: **do NOT state the filtered system;
pass 00MP to the approximation leaf as a HYPOTHESIS.**  That makes the
assembly writable with no new definitions, and 00MP is not free-floating —
its consumer is `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation_of_noetherian`,
which takes it as an argument, and it appears in the proof term of 00R7.

**WHY NOT THE FILTERED SYSTEM — this is a REFUTATION, not a preference.**
The lightweight realisation everyone reaches for first is a directed family of
NOETHERIAN LOCAL SUBRINGS `R_λ ⊆ R`, `B_λ ⊆ B`, `A_λ ⊆ A` with
`⨆ λ, R_λ = ⊤` etc. — cheap to state (`Subring`, `Monotone`, `iSup = ⊤`) and
needing no colimit machinery.  **A leaf stated that way would be FALSE.**  It
is fine for `R` alone: `R` is the directed union of its finitely generated
`ℤ`-subalgebras `C`; each `C_{𝔪 ∩ C}` is essentially of finite type over `ℤ`,
hence Noetherian; and since localisation is exact and `C ↪ R`, the map
`C_{𝔪 ∩ C} → R` is INJECTIVE, so these really are local subrings of `R` whose
union is `R`.  It is false for `B` and `A`.  In the Stacks proof `S_λ` is a
localisation of `R_λ[x₁,…,xₙ]/I_λ` where `I_λ` is a FINITELY GENERATED
approximation to the full ideal `I`, growing with `λ`: the transition maps of
that system are surjections with shrinking kernels, not injections, so
`S_λ → S` is not injective and `S_λ` is not a subring of `S`.  The refuting
check is one line of the source: read the construction of `S_λ` in the proof
of 10.128.8 and ask whether `S_λ → S` is injective.

The correct datum is therefore a genuine filtered colimit — `Ring.DirectLimit`
over a directed order, or a functor from a filtered category — plus a
`DirectedSystem` of the two maps `g` and `v`, plus a descent lemma "a filtered
colimit of flat ring maps is flat over the colimit of the bases".  Three
interlocking pieces of new infrastructure, none of them in the pin
(`grep -rn "Ring.DirectLimit" Fermat/ ~/cs/FLT` finds no use of it anywhere in
this development).  Building them correctly is a task in its own right, and
the wrong version of it is a FALSE leaf, as above.  So the system stays inside
the approximation leaf's PROOF, where a wrong guess costs nothing.

**UPDATE 2026-07-28.**  The refutation above is still exactly right and is why
`NoetherianApproxSystem` (further down) uses `CommRingCat`-valued towers with
their own transition maps and NOT `Subring R`-valued ones: the `Mid` and `Tot`
transitions are not injective.  What has changed is only the last sentence — the
system is now stated, in predicate form, so that the approximation leaf could be
cut; `Ring.DirectLimit` is still not used anywhere, and no ring is constructed.
See "THE CUT OF THE APPROXIMATION LEAF, TAKEN 2026-07-28" below.

**WHAT THE CUT BUYS, concretely.**  00R7 is now PROVEN, and what was one leaf
is two, along the source's own seam `00R7 = approximation + 00MP`:

* `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation_of_noetherian` —
  the APPROXIMATION half.  **PROVEN later the same day**, over the single new
  leaf `nonempty_flatNoetherianStage_of_essFinitePresentation`; the
  filtered-system decision that its owner took, and the reasons, are the
  section note "THE COLIMIT-API DECISION" immediately below.  The short form:
  no filtered colimit is stated anywhere; the interface is a Noetherian stage
  plus a base change followed by a localization (it said `Algebra.IsPushout`
  until 2026-07-27; see the CORRECTION in that note).
* `flat_of_rTensor_injective_of_flat_quotientMap` — **10.99.10**, the local
  criterion of flatness in the Noetherian setting.  **PROVEN 2026-07-27**; it
  was itself cut in two along Matsumura 22.3's own seam, and its HOMOLOGICAL
  half `lTensor_subtype_injective_of_pow_le` — which needs no Noetherian
  hypothesis at all — is **PROVEN 2026-07-27** as well, over the general local
  criterion in `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`.  See
  the section note "10.99.10 CUT" below.

and 00MP itself (`flat_of_flat_of_flat_quotientMap_noetherian`) is PROVEN
here, because its OTHER half is proven outright:

* `rTensor_map_subtype_injective_of_flat` — **PROVEN**.  `A` flat over `R`
  implies `Tor₁^B(B/I·B, A) = 0` for every ideal `I ⊆ R`.  This is the first
  half of 00MP's own proof, it needs neither Noetherian hypotheses nor any
  finiteness, and it is stated over an arbitrary tower `R → B → A`.

**A CORRECTION TO THE SURVEY ABOVE, worth reading before believing it.**  The
route audit in the previous section note says the missing machinery is "Tor,
the local criterion, and Noetherian approximation", and that Tor for modules
is absent from the pin.  Both remain true as stated, and the Tor half of 00MP
turned out **not to need Tor at all**: `Module.Flat.iff_rTensor_injective'`
(`Mathlib/RingTheory/Flat/Tensor.lean:67`) is "`Tor₁(R/I, M) = 0` for every
ideal" written without Tor, and that is enough to prove the whole step.  The
audit itself flags this lemma as "an ingredient a naive survey misses"; it was
right, and the ingredient was sufficient.  What is genuinely missing is only
the local criterion (10.99.10) and the approximation.

**AND A SECOND CORRECTION, 2026-07-27, to the sentence immediately above.**  The
local criterion is no longer missing either: it is PROVEN below, and its own
Noetherian content (Artin–Rees + Krull) is written out.  Its purely homological
half `lTensor_subtype_injective_of_pow_le` — which carries none of the
hypotheses that made this route look expensive: no Noetherian, no finiteness,
no locality — is **PROVEN 2026-07-27** over the general local criterion in
`Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`.  So of the three items
in the original survey — Tor, the local criterion, Noetherian approximation —
only the third remains.

**AXIS SEARCHED.**  Cuts of 00R7 along the Stacks proof's own structure.  Not
searched: whether a *different* proof of 00R7 exists that avoids approximation
entirely.  The direct non-Noetherian route is the one the previous section
note flags as hazardous (Matsumura 22.3 needs ideal separatedness, which an
arbitrary local `R` does not supply), and mathlib's non-Noetherian criterion
`Module.free_of_maximalIdeal_rTensor_injective` needs finite presentation of a
MODULE, which `EssFinitePresentation` of a ring map does not give — so that
axis is documented as closed above rather than merely unexamined.
-/

section FibreCriterionRingLevel

open scoped TensorProduct

/-- The comparison map `I ⊗[R] A → (I·B) ⊗[B] A` of a tower `R → B → A`,
sending `x ⊗ₜ a` to `(g x) ⊗ₜ a`.  It is the map whose SURJECTIVITY carries
the first half of Stacks 00MP's proof ("the surjectivity of
`𝔪 ⊗_R S' → I ⊗_S S'` implies `𝔪 ⊗_R M → I ⊗_S M` is also surjective"), and
it exists only to give `rTensor_map_subtype_injective_of_flat` below a
nameable factorisation. -/
noncomputable def idealMapTensorComparison {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] (I : Ideal R) :
    ↥I ⊗[R] A →ₗ[R] ↥(I.map (algebraMap R B)) ⊗[B] A :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun (x : ↥I) (a : A) =>
      (⟨algebraMap R B x.1, Ideal.mem_map_of_mem _ x.2⟩ :
        ↥(I.map (algebraMap R B))) ⊗ₜ[B] a)
    (fun x y a => by
      rw [show (⟨algebraMap R B (x + y).1, _⟩ : ↥(I.map (algebraMap R B))) =
          ⟨algebraMap R B x.1, Ideal.mem_map_of_mem _ x.2⟩ +
            ⟨algebraMap R B y.1, Ideal.mem_map_of_mem _ y.2⟩ from by ext; simp,
        TensorProduct.add_tmul])
    (fun c x a => by
      rw [show (⟨algebraMap R B (c • x).1, _⟩ : ↥(I.map (algebraMap R B))) =
          c • (⟨algebraMap R B x.1, Ideal.mem_map_of_mem _ x.2⟩ :
            ↥(I.map (algebraMap R B))) from by ext; simp [Algebra.smul_def, map_mul]]
      rfl)
    (fun x a b => TensorProduct.tmul_add _ _ _)
    (fun c x a => by
      rw [show c • a = (algebraMap R B c) • a from (IsScalarTower.algebraMap_smul B c a).symm,
        ← TensorProduct.smul_tmul, IsScalarTower.algebraMap_smul]
      rfl)

@[simp] lemma idealMapTensorComparison_tmul {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    (I : Ideal R) (x : ↥I) (a : A) :
    idealMapTensorComparison (B := B) I (x ⊗ₜ[R] a) =
      (⟨algebraMap R B x.1, Ideal.mem_map_of_mem _ x.2⟩ :
        ↥(I.map (algebraMap R B))) ⊗ₜ[B] a := rfl

/-- `I ⊗[R] A → (I·B) ⊗[B] A` is SURJECTIVE, because `I·B` is generated over
`B` by the image of `I` and `(b · g x) ⊗ₜ a = (g x) ⊗ₜ (b • a)`.  The
`smul` case of the span induction is why the statement is proved for all `a`
simultaneously. -/
lemma idealMapTensorComparison_surjective {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] (I : Ideal R) :
    Function.Surjective (idealMapTensorComparison (R := R) (B := B) (A := A) I) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | tmul y a =>
      obtain ⟨y, hy⟩ := y
      induction hy using Submodule.span_induction generalizing a with
      | mem b hb =>
          obtain ⟨x, hx, rfl⟩ := hb
          exact ⟨(⟨x, hx⟩ : ↥I) ⊗ₜ[R] a, rfl⟩
      | zero =>
          refine ⟨0, ?_⟩
          rw [map_zero, show (⟨0, _⟩ : ↥(I.map (algebraMap R B))) = 0 from rfl,
            TensorProduct.zero_tmul]
      | add b₁ b₂ hb₁ hb₂ ih₁ ih₂ =>
          obtain ⟨w₁, hw₁⟩ := ih₁ a
          obtain ⟨w₂, hw₂⟩ := ih₂ a
          refine ⟨w₁ + w₂, ?_⟩
          rw [map_add, hw₁, hw₂, ← TensorProduct.add_tmul]
          rfl
      | smul c b hb ih =>
          obtain ⟨w, hw⟩ := ih (c • a)
          refine ⟨w, ?_⟩
          rw [hw, show (⟨c • b, _⟩ : ↥(I.map (algebraMap R B))) =
            c • (⟨b, hb⟩ : ↥(I.map (algebraMap R B))) from rfl, TensorProduct.smul_tmul]
  | add z₁ z₂ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁⟩ := ih₁
      obtain ⟨w₂, hw₂⟩ := ih₂
      exact ⟨w₁ + w₂, by rw [map_add, hw₁, hw₂]⟩

/-- The comparison map commutes with the two multiplication maps to `A`:
`(I·B) ⊗[B] A → A` pulled back along it is `I ⊗[R] A → A`.  Both are
`x ⊗ₜ a ↦ x • a`, and `IsScalarTower` identifies the two scalar actions. -/
lemma lid_rTensor_idealMapTensorComparison {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    (I : Ideal R) (z : ↥I ⊗[R] A) :
    (TensorProduct.lid B A)
        (LinearMap.rTensor A (I.map (algebraMap R B)).subtype
          (idealMapTensorComparison (B := B) I z)) =
      (TensorProduct.lid R A) (LinearMap.rTensor A I.subtype z) := by
  induction z with
  | zero => simp
  | tmul x a => simp
  | add z₁ z₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- **PROVEN — the first half of Stacks 00MP's proof, and it needs neither
Noetherian hypotheses nor any finiteness.**

*Let `R → B → A` be a tower of rings with `A` flat over `R`.  Then for every
ideal `I ⊆ R` the map `(I·B) ⊗_B A → B ⊗_B A` is injective, i.e.
`Tor₁^B(B/I·B, A) = 0`.*

This is 00MP's step "the surjectivity of `𝔪 ⊗_R S' → I ⊗_S S'` implies
`𝔪 ⊗_R M → I ⊗_S M` is also surjective; the flatness of `M` over `R` makes the
composition injective, yielding `Tor₁^S(S/I, M) = 0`", at `M = S' = A`.  The
factorisation is `idealMapTensorComparison` (surjective) followed by the map
whose injectivity is wanted; the composite is the `R`-side multiplication map,
injective by `Module.Flat.iff_rTensor_injective'`.

**Note for the survey in the section note above**: this closes the "Tor" item
without Tor.  `Module.Flat.iff_rTensor_injective'` IS the vanishing of `Tor₁`
against every ideal, written as injectivity of `I ⊗ M → M`, so the absence of
`Tor` for modules from the pin does not obstruct this half at all. -/
theorem rTensor_map_subtype_injective_of_flat {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R A] (I : Ideal R) :
    Function.Injective
      (LinearMap.rTensor A (I.map (algebraMap R B)).subtype) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, rfl⟩ := idealMapTensorComparison_surjective (R := R) (B := B) (A := A) I z
  have hw : LinearMap.rTensor A I.subtype w = 0 := by
    have h := lid_rTensor_idealMapTensorComparison (B := B) I w
    rw [hz] at h
    simpa using h.symm
  rw [(Module.Flat.iff_rTensor_injective'.mp inferInstance I).eq_iff' (map_zero _) |>.mp hw]
  exact map_zero _

/-! ### 10.99.10 CUT — the Noetherian half is Artin–Rees + Krull, and it is PROVEN

**SECTION NOTE for the three declarations that follow and for the local criterion
itself** (2026-07-27).  Stacks **10.99.10** — the local criterion of flatness in
the Noetherian setting — was left ATOMIC when 00R7 was cut, with a docstring
saying only that `grep -rin "local criterion"` over the pin is empty and that the
textbook route is "Matsumura 22.3 via the `I`-adic filtration and Artin–Rees".
That is right, and it hides a clean seam that the classical proof itself uses.

**THE SEAM.**  Matsumura 22.3 / Stacks 10.99.6–10.99.7 prove the criterion in two
independent halves:

1. *(Homological, and it needs NO finiteness, NO Noetherian hypothesis and NO
   locality.)*  `Tor₁^B(B/I, A) = 0` together with flatness of `A/IA` over `B/I`
   propagates up the `I`-adic filtration: for every `n`, `Tor₁^B(B/Iⁿ, A) = 0`
   and `A/IⁿA` is flat over `B/Iⁿ`.
2. *(Noetherian, and it is where every hypothesis of the leaf is consumed.)*
   Artin–Rees plus Krull's intersection theorem turn (1) into flatness: for a
   finitely generated ideal `𝔞 ⊆ B`, an element of `ker(A ⊗_B 𝔞 → A)` lies in
   `Iⁿ·(A ⊗_B 𝔞)` for every `n`, and the intersection of those is zero because
   `A ⊗_B 𝔞` is a FINITE `A`-module and `I·A ⊆ 𝔪_A`.

Half (2) is proven below in full; half (1) is
`lTensor_subtype_injective_of_pow_le`, **PROVEN 2026-07-27** over the general
local criterion in `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`.
Both halves are stated with `B`-modules
only — no quotient rings occur in any statement — which is the design decision
recorded in that leaf's docstring.

**WHAT MATHLIB SUPPLIES, checked 2026-07-27.**  `Ideal.exists_pow_inf_eq_pow_smul`
(**Artin–Rees**, `Mathlib/RingTheory/Filtration.lean:387`) and
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (**Krull's intersection theorem** for
a finite module over a Noetherian local ring, same file).  Both arrive in this
file's cone already.  `Module.Finite.base_change`
(`Mathlib/RingTheory/TensorProduct/Finite.lean:82`) supplies
`Module.Finite A (A ⊗[B] ↥𝔞)`, which is what makes Krull applicable — and it is
exactly the "ideally separated" hypothesis of Matsumura 22.3, discharged rather
than assumed.  This is why the section note above is right that
`IsNoetherianRing` must not be dropped: without it neither Artin–Rees nor Krull
is available, and half (2) is FALSE for a general local ring.

**ORIENTATION.**  Everything below is written with `lTensor` (`A ⊗_B N`) rather
than `rTensor` (`N ⊗_B A`), because the `A`-module structure on `A ⊗[B] N` is a
global instance (`TensorProduct.leftModule`) whereas the one on `N ⊗[B] A` is
only available through `Algebra.TensorProduct.rightAlgebra`, which mathlib
declares as a *local* instance.  Krull's theorem is applied over `A`, so the
`A`-module structure has to be the ambient one.  `_htor` is stated with `rTensor`
because that is the shape `rTensor_map_subtype_injective_of_flat` produces; the
two are interchangeable by `LinearMap.lTensor_inj_iff_rTensor_inj`, and the leaf
below takes the `rTensor` form verbatim so that the consumer needs no bridge.
-/

/-- `a ⊗ₜ m` with `m ∈ K • ⊤` lies in `(K·A) • ⊤`.

The `B`-action of an ideal `K` on `M` is absorbed, along `M → A ⊗[B] M`, by the
`A`-action of the extended ideal `K·A` on `A ⊗[B] M`.  This is the step that
converts the Artin–Rees bound (a statement about `B`-ideals) into a statement
about the `A`-submodule filtration on which Krull's intersection theorem is run,
and it is the only place where the scalar tower `B → A → A ⊗[B] M` is used. -/
lemma tmul_mem_map_smul_top {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {M : Type u} [AddCommGroup M] [Module B M] (K : Ideal B) (a : A) (m : M)
    (hm : m ∈ K • (⊤ : Submodule B M)) :
    a ⊗ₜ[B] m ∈ (K.map (algebraMap B A)) • (⊤ : Submodule A (A ⊗[B] M)) := by
  refine Submodule.smul_induction_on (p := fun m => a ⊗ₜ[B] m ∈
    (K.map (algebraMap B A)) • (⊤ : Submodule A (A ⊗[B] M))) hm ?_ ?_
  · intro r hr x _
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul A r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · intro x y hx hy
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- **THE HOMOLOGICAL HALF OF THE LOCAL CRITERION** (**PROVEN 2026-07-27**, cut
out of `flat_of_rTensor_injective_of_flat_quotientMap` earlier the same day;
read the section note above first).

**HOW IT CLOSED.**  Not by the `I`-adic induction prescribed under "WHAT PROVING
IT COSTS" below — that route needs the graded isomorphism
`Iⁿ/Iⁿ⁺¹ ⊗_{B/I} A/IA ≅ IⁿA/Iⁿ⁺¹A`, which is exactly the piece the missing `Tor`
long exact sequence would supply.  It closed instead over the **general,
module-theoretic** local criterion now proven in the shim tree:
`Module.Flat.rTensor_ideal_subtype_injective`
(`Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`), whose dévissage never
leaves the category of modules — see that file's docstring for the four steps.
Everything below the horizontal rule is kept as the record of the classical
route and of why the statement is shaped this way; it is history, not an open
task.

*Let `B → A` be a ring map and `I ⊆ B` an ideal, `J = I·A`.  Assume
`Tor₁^B(B/I, A) = 0` and that `A/J` is flat over `B/I`.  Then for every `n : ℕ`
and every ideal `𝔠 ⊆ B` with `Iⁿ ⊆ 𝔠`, the multiplication map `A ⊗_B 𝔠 → A` is
injective.*

**WHAT THIS SAYS IN CLASSICAL TERMS — it is Stacks 10.99.6 / Matsumura 22.3's
step (2) ⟹ (3), packed into one quantifier.**  The ideals `𝔠 ⊇ Iⁿ` are exactly
the preimages of the ideals of `B/Iⁿ`, so the conclusion is the conjunction of

* `Tor₁^B(B/Iⁿ, A) = 0`  — the case `𝔠 = Iⁿ`; and
* `A/IⁿA` is FLAT over `B/Iⁿ`  — the remaining `𝔠`, via
  `A ⊗_B (𝔠/Iⁿ) ≅ (A/IⁿA) ⊗_{B/Iⁿ} (𝔠/Iⁿ)`.

At `n = 1` it is exactly the two hypotheses again, so the leaf is an induction
starting from its own hypotheses, not a strengthening of them.

**WHY IT IS STATED THIS WAY AND NOT WITH QUOTIENT RINGS.**  The classical form
("`A/IⁿA` is flat over `B/Iⁿ` for every `n`") forces its CONSUMER to cross the
change-of-rings identification `A ⊗_B N ≅ (A/IⁿA) ⊗_{B/Iⁿ} N` for `B/Iⁿ`-modules
`N`, which is a base-change cancellation that mathlib states only through
`TensorProduct.AlgebraTensorModule` and that would have to be carried through the
Artin–Rees argument.  In the `∀ 𝔠 ⊇ Iⁿ` form the identification is part of the
PROOF of this leaf and never appears downstream; the two forms are equivalent by
the diagram chase on `0 → Iⁿ → 𝔠 → 𝔠/Iⁿ → 0` tensored with `A`.  Nothing is
weakened: the equivalence is an equivalence, in both directions.

**NO NOETHERIAN, NO FINITENESS, NO LOCALITY.**  The statement carries none of the
four hypotheses that the consumer needs (`IsNoetherianRing B`, `IsNoetherianRing
A`, `IsLocalRing`, `IsLocalHom`), because half (1) of the classical proof uses
none of them.  A prover who finds a use for them should say so — it would mean
the seam is in the wrong place.

**WHAT PROVING IT COSTS.**  Induction on `n`.

* `n = 0`: `I⁰ = ⊤` forces `𝔠 = ⊤`, and `A ⊗_B B → A` is an isomorphism.
* `n = 1`: the chase above.  From `0 → I → 𝔠 → 𝔠/I → 0` one gets the exact
  `A ⊗ I → A ⊗ 𝔠 → A ⊗ (𝔠/I) → 0`; an `x` killed in `A` dies in `A/IA`, hence in
  `A ⊗ (𝔠/I) ≅ (A/IA) ⊗_{B/I} (𝔠/I)` by `_hquot`, hence comes from `A ⊗ I`,
  hence is `0` by `_htor`.
* `n → n+1`: the graded step of 10.99.6.  The content is that
  `Iⁿ/Iⁿ⁺¹ ⊗_{B/I} A/IA → IⁿA/Iⁿ⁺¹A` is an isomorphism, proved from the `n = 1`
  data by Nakayama; that identification is what upgrades `A/IⁿA` flat over
  `B/Iⁿ` to `A/Iⁿ⁺¹A` flat over `B/Iⁿ⁺¹`.

The only piece of infrastructure that is not already in this file's cone is the
change-of-rings isomorphism `A ⊗_B N ≅ (A/I^nA) ⊗_{B/I^n} N`; mathlib's
`Mathlib.RingTheory.TensorProduct.Quotient` (already imported here) and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` are the intended route.

**READ `section LocalCriterionOfFlatness` FURTHER DOWN THIS FILE BEFORE
STARTING — it is the SAME theorem at a principal ideal, and it already carries a
worked Lean attack.**  `flat_quotientMap_pow_of_flat_quotientMap` there is
precisely this leaf specialised to `I = (t)` with `t` a nonzerodivisor on both
rings (in that case `Tor₁^B(B/(t), A) = 0` is exactly regularity of `φ t` on
`A`, which is why it appears as a hypothesis rather than as a `Tor` statement).
It is **PROVEN** (see the paragraph below); this sentence used to say it was
"open with the same owner-less status", which went stale on 2026-07-27 and was
corrected 2026-07-29.  More usefully,
`mem_baseChange_sup_of_flat_quotientMap_pow`'s docstring works out the
change-of-rings chase in Lean-level detail — the two `TensorProduct.lift`s `F`
and `G`, why a kernel must NOT be computed directly, and the `Module Rₙ Q`
instance hazard.  That plan transfers to a general `I` verbatim.

**These two leaves had ONE owner, and that is how both closed** (2026-07-27):
the general statement `Module.Flat.rTensor_subtype_injective_of_pow_smul_top_le`
in `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean` proves this leaf and
`Module.Flat.of_flat_quotient_of_pow_eq_bot` — hence
`flat_quotientMap_pow_of_flat_quotientMap` — at once, because both are the SAME
dévissage read at `J ^ k • Z ≤ Y` with `Z` the base ring. -/
theorem lTensor_subtype_injective_of_pow_le {B A : Type u}
    [CommRing B] [CommRing A] [Algebra B A] {I : Ideal B}
    (_hIJ : I ≤ (I.map (algebraMap B A)).comap (algebraMap B A))
    (_htor : Function.Injective (LinearMap.rTensor A I.subtype))
    (_hquot : (Ideal.quotientMap (I.map (algebraMap B A)) (algebraMap B A) _hIJ).Flat)
    (n : ℕ) {𝔠 : Ideal B} (_h : I ^ n ≤ 𝔠) :
    Function.Injective (LinearMap.lTensor A 𝔠.subtype) := by
  -- `A ⧸ IA` is flat over `B ⧸ I`, restated as a module rather than a ring map
  have hQflat : Module.Flat (B ⧸ I) (A ⧸ Ideal.map (algebraMap B A) I) := by
    rw [← RingHom.flat_algebraMap_iff]
    exact _hquot
  -- `A ⧸ IA` is `(B ⧸ I) ⊗[B] A`, which is the shape the general criterion wants
  have hker : I • (⊤ : Submodule B A)
      = LinearMap.ker (Ideal.Quotient.mkₐ B (Ideal.map (algebraMap B A) I)).toLinearMap := by
    rw [Ideal.smul_top_eq_map]
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have hflat : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] A) :=
    _root_.Module.Flat.flat_quotTensor_of_flat (J := I)
      (Ideal.Quotient.mkₐ B (Ideal.map (algebraMap B A) I)).toLinearMap
      Ideal.Quotient.mk_surjective hker hQflat
  exact (𝔠.subtype.lTensor_inj_iff_rTensor_inj A).2
    (_root_.Module.Flat.rTensor_ideal_subtype_injective hflat _htor n _h)

/-- **PROVEN** — the form of the leaf above that the Artin–Rees descent actually
consumes: for EVERY ideal `𝔞` (no containment hypothesis), an element of
`ker(A ⊗_B 𝔞 → A)` already comes from `A ⊗_B (𝔞 ∩ Iⁿ)`.

The reduction to the leaf is the second isomorphism theorem.  Write `L = Iⁿ` and
`𝔠 = 𝔞 + L ⊇ L`.  Then

* `x ∈ ker(A ⊗ 𝔞 → A)` pushes to an element of `A ⊗ 𝔠` still killed in `A`, so it
  is `0` there by the leaf at `𝔠`;
* `↥𝔞 ↠ ↥𝔠 / L` is surjective with kernel `𝔞 ∩ L` (mathlib's
  `LinearMap.subToSupQuotient`, surjective by
  `LinearMap.quotientInfEquivSupQuotient_surjective`), so right-exactness of
  `A ⊗_B -` identifies `ker(A ⊗ 𝔞 → A ⊗ (𝔠/L))` with the image of `A ⊗ (𝔞 ∩ L)`;
* and the first bullet says exactly that `x` is in that kernel, because
  `↥𝔞 → ↥𝔠/L` factors through `↥𝔠`.

Note the second isomorphism theorem is used only through its SURJECTIVITY half,
so the `⊤ ⊓ _` shape of `LinearMap.quotientInfEquivSupQuotient`'s domain never
has to be normalised. -/
theorem ker_lTensor_subtype_le_range_lTensor_comap_pow {B A : Type u}
    [CommRing B] [CommRing A] [Algebra B A] {I : Ideal B}
    (hIJ : I ≤ (I.map (algebraMap B A)).comap (algebraMap B A))
    (htor : Function.Injective (LinearMap.rTensor A I.subtype))
    (hquot : (Ideal.quotientMap (I.map (algebraMap B A)) (algebraMap B A) hIJ).Flat)
    (n : ℕ) (𝔞 : Ideal B) :
    LinearMap.ker (LinearMap.lTensor A 𝔞.subtype) ≤
      LinearMap.range (LinearMap.lTensor A
        (Submodule.comap 𝔞.subtype (I ^ n)).subtype) := by
  set L : Ideal B := I ^ n
  set N : Submodule B ↥𝔞 := Submodule.comap 𝔞.subtype L with hNdef
  have hker : LinearMap.ker (LinearMap.subToSupQuotient 𝔞 L) = N := by
    ext y
    simp [LinearMap.subToSupQuotient, hNdef]
  have hex : Function.Exact N.subtype (LinearMap.subToSupQuotient 𝔞 L) := by
    rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
  have hsurj : Function.Surjective (LinearMap.subToSupQuotient 𝔞 L) := by
    intro z
    obtain ⟨w, hw⟩ := LinearMap.quotientInfEquivSupQuotient_surjective 𝔞 L z
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ w
    exact ⟨v, hw⟩
  have hexT := _root_.lTensor_exact A hex hsurj
  intro x hx
  refine (hexT x).mp ?_
  have h1 : LinearMap.lTensor A (Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ L)) x = 0 := by
    refine (injective_iff_map_eq_zero _).mp
      (lTensor_subtype_injective_of_pow_le hIJ htor hquot n (𝔠 := 𝔞 ⊔ L) le_sup_right) _ ?_
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact LinearMap.mem_ker.mp hx
  show LinearMap.lTensor A
    ((Submodule.comap (𝔞 ⊔ L).subtype L).mkQ.comp
      (Submodule.inclusion (le_sup_left : 𝔞 ≤ 𝔞 ⊔ L))) x = 0
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, h1, map_zero]

/-- **THE LOCAL CRITERION OF FLATNESS, Noetherian: Stacks 10.99.10** (**PROVEN
SORRY-FREE**.  Cut out of `flat_of_flat_of_flat_quotientMap_noetherian` on
2026-07-27 over the single leaf `lTensor_subtype_injective_of_pow_le`; that leaf
was itself closed the same day, so nothing under this theorem is open.  The
section note "10.99.10 CUT" above is the design decision that produced it.)

*Let `B → A` be a local homomorphism of NOETHERIAN local rings and `I ⊆ 𝔪_B`
an ideal, `J = I·A`.  If `Tor₁^B(B/I, A) = 0` and `A/J` is flat over `B/I`,
then `A` is flat over `B`.*

This is 10.99.10 with the module `M` taken to be `A` itself — which is the
only instantiation 00MP needs at `M = S' = A`, and which is where the
Noetherian hypotheses earn their keep: `M = A` is a FINITE module over the
Noetherian local ring `S' = A`, so it is ideally separated by Artin–Rees, and
that is exactly what the classical criterion (Matsumura *Commutative Ring
Theory* Thm 22.3; Bourbaki) requires and what a general local ring does not
supply.  **Do not try to drop `IsNoetherianRing` here**: the section note
above records that a separatedness-free version of this statement is precisely
the shape of leaf that can be FALSE, and the Stacks route never proves one —
it approximates down to the Noetherian case instead.

**FAITHFULNESS.**  `_hJ : J = I.map (algebraMap B A)` is load-bearing and not
bookkeeping: without it `J` would be an arbitrary ideal above `I` and the
hypothesis "`A/J` flat over `B/I`" would be a different statement, so the leaf
could be false.  It is carried as an equation rather than substituted into the
type because `J` occurs inside `A ⧸ J`, and the consumer supplies `J` as
`(𝔪_R).map (v.comp g)` while `I.map v` is `((𝔪_R).map g).map v` — equal by
`Ideal.map_map`, but only propositionally, and a dependent rewrite there is
gratuitous friction.

**THE PROOF, now written**, is half (2) of the section note above: Artin–Rees
plus Krull, over the leaf `lTensor_subtype_injective_of_pow_le`.  For a finitely
generated ideal `𝔞 ⊆ B` and `x ∈ ker(A ⊗_B 𝔞 → A)`, fix `n`; Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`) gives `k` with `𝔞 ∩ I^{n+k} ⊆ Iⁿ·𝔞`, the
leaf (through `ker_lTensor_subtype_le_range_lTensor_comap_pow` at `n+k`) puts `x`
in the image of `A ⊗_B (𝔞 ∩ I^{n+k})`, and `tmul_mem_map_smul_top` then places it
in `(I·A)ⁿ · (A ⊗_B 𝔞)`.  As `n` was arbitrary and `A ⊗_B 𝔞` is a finite
`A`-module (`Module.Finite.base_change`, using `IsNoetherianRing B` for
`Module.Finite B ↥𝔞`) with `I·A ≠ ⊤` (using `_hI` and `IsLocalHom`), Krull's
intersection theorem `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` gives `x = 0`.

**WHERE EACH HYPOTHESIS IS CONSUMED**, since the note above warns against
dropping any of them: `IsNoetherianRing B` for Artin–Rees and for finiteness of
`𝔞`; `IsNoetherianRing A` + `IsLocalRing A` for Krull; `_hI` + `IsLocalHom` for
`I·A ≠ ⊤`, which is what makes the Krull filtration separating and is the
formal content of "`A` is `I`-adically ideally separated"; `_htor` and `_hquot`
only through the leaf.  `IsLocalRing B` is used nowhere in this proof — it is
kept because the consumer has it and because dropping it from a leaf's signature
is a restatement, not a simplification.

**WHAT WAS MISSING FROM THE PIN.**  `grep -rin "local criterion"
.lake/packages/mathlib` returns nothing, re-run 2026-07-27, so this is genuinely
new.  Note that mathlib's `Module.free_of_maximalIdeal_rTensor_injective`
(`Mathlib/RingTheory/LocalRing/Module.lean:248`) is the NON-Noetherian
criterion for a finitely presented MODULE, and does not apply: `A` is not a
finite `B`-module here. -/
theorem flat_of_rTensor_injective_of_flat_quotientMap {B A : Type u}
    [CommRing B] [CommRing A] [Algebra B A]
    [IsLocalRing B] [IsLocalRing A]
    [IsNoetherianRing B] [IsNoetherianRing A] [IsLocalHom (algebraMap B A)]
    {I : Ideal B} {J : Ideal A}
    (_hI : I ≤ IsLocalRing.maximalIdeal B)
    (_hJ : J = I.map (algebraMap B A))
    (hIJ : I ≤ J.comap (algebraMap B A))
    (_htor : Function.Injective (LinearMap.rTensor A I.subtype))
    (_hquot : (Ideal.quotientMap J (algebraMap B A) hIJ).Flat) :
    Module.Flat B A := by
  subst _hJ
  have hmapne : I.map (algebraMap B A) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top ?_
    exact (Ideal.map_mono _hI).trans (IsLocalRing.map_maximalIdeal_le (algebraMap B A))
  rw [Module.Flat.iff_lTensor_injective]
  intro 𝔞 h𝔞
  haveI : Module.Finite B ↥𝔞 := Module.Finite.iff_fg.mpr h𝔞
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hKrull : (⨅ i : ℕ, (I.map (algebraMap B A)) ^ i •
      (⊤ : Submodule A (A ⊗[B] ↥𝔞))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ hmapne
  have hx' : x ∈ (⨅ i : ℕ, (I.map (algebraMap B A)) ^ i •
      (⊤ : Submodule A (A ⊗[B] ↥𝔞))) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := B) 𝔞
    have hAR : 𝔞 ⊓ I ^ (n + k) ≤ I ^ n • 𝔞 := by
      have h := hk (n + k) (Nat.le_add_left k n)
      rw [Nat.add_sub_cancel] at h
      have htop : ∀ m : ℕ, (I ^ m) • (⊤ : Submodule B B) = I ^ m := by
        intro m; rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
      rw [htop, htop] at h
      rw [inf_comm, h]
      exact Submodule.smul_mono le_rfl inf_le_right
    obtain ⟨y, hy⟩ := ker_lTensor_subtype_le_range_lTensor_comap_pow hIJ _htor _hquot
      (n + k) 𝔞 (LinearMap.mem_ker.mpr hx)
    rw [← hy]
    clear hy hx
    induction y with
    | zero => simp
    | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
    | tmul a m =>
        rw [LinearMap.lTensor_tmul, ← Ideal.map_pow]
        refine tmul_mem_map_smul_top (I ^ n) a _ ?_
        rw [Submodule.mem_smul_top_iff]
        exact hAR ⟨(m : ↥𝔞).2, m.2⟩
  rw [hKrull] at hx'
  simpa using hx'

/-- **Stacks 00MP** = Algebra Lemma 10.99.15, at `M = S' = A` (**PROVEN**
2026-07-27 over `rTensor_map_subtype_injective_of_flat` and the local
criterion `flat_of_rTensor_injective_of_flat_quotientMap` above).

*Let `R → B → A` be local homomorphisms of NOETHERIAN local rings.  If `A` is
flat over `R` and `A/𝔪_R A` is flat over `B/𝔪_R B`, then `A` is flat over `B`.*

**FAITHFULNESS.**  00MP's hypotheses are (1) `M` finite over `S'`, (2)
`M ≠ 0`, (3) `M/𝔪M` flat over `S/𝔪S`, (4) `M` flat over `R`, with all three
rings Noetherian local.  At `M = S' = A`, (1) and (2) are theorems rather than
assumptions — `A` is finite over itself, and `[IsLocalRing A]` supplies
`Nontrivial A` — exactly as in the leaves below.  00MP also concludes `S` flat
over `R`; only `M` flat over `S` is kept, because only that is consumed.
Fewer hypotheses and a weaker conclusion cannot turn a true statement false.
Note in particular that 00MP asks for NO finite-presentation hypothesis of any
kind: that is the whole reason the approximation half exists.

**THE PROOF** is 00MP's own, in two steps: `I := 𝔪_R B`, so that `B/I` is
`B/𝔪_R B` and `A/I·A` is `A/𝔪_R A` (`Ideal.map_map`), then `Tor₁^B(B/I, A) = 0`
from flatness of `A` over `R`, then the local criterion.  `algebraize` supplies
the three `Algebra` instances and the `IsScalarTower` from the three ring
maps. -/
theorem flat_of_flat_of_flat_quotientMap_noetherian {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    [IsNoetherianRing R] [IsNoetherianRing B] [IsNoetherianRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    v.Flat := by
  algebraize [g, v, v.comp g]
  exact flat_of_rTensor_injective_of_flat_quotientMap
    (I := (IsLocalRing.maximalIdeal R).map g)
    (J := (IsLocalRing.maximalIdeal R).map (v.comp g))
    (IsLocalRing.map_maximalIdeal_le g)
    (Ideal.map_map (f := g) (g := v)).symm
    (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))
    (rTensor_map_subtype_injective_of_flat (R := R) (B := B) (A := A)
      (IsLocalRing.maximalIdeal R))
    hfib

/-! ### THE COLIMIT-API DECISION, TAKEN 2026-07-27 — and it is *no colimit API*

**SECTION NOTE for `FlatNoetherianStage`, the leaf
`nonempty_flatNoetherianStage_of_essFinitePresentation`, and the now-PROVEN
approximation half below them.**  The note "00R7 CUT" above took the *first*
design decision (pass 00MP as a hypothesis rather than state a filtered
system) and explicitly deferred the *second* one to whoever proved the
approximation half:

> The correct datum is therefore a genuine filtered colimit — `Ring.DirectLimit`
> over a directed order, or a functor from a filtered category — plus a
> `DirectedSystem` of the two maps `g` and `v`, plus a descent lemma "a filtered
> colimit of flat ring maps is flat over the colimit of the bases".

That paragraph is a correct description of what 00R7's PROOF does.  It is
**not** what any of 00R7's statements needs, and the decision taken here is
therefore:

**PIN: no filtered colimit appears in the statement of any leaf.  The
interface between the approximation and everything that consumes it is
`(a Noetherian local stage) + (a base change) + (a localization)`.**  It read
`(a Noetherian local stage) + (`Algebra.IsPushout`)` until the CORRECTION
below, which is where the localization comes from.  Concretely that is
the structure `FlatNoetherianStage` below, and the filtered system stays
where the note above put it — inside the leaf's proof, where a wrong guess
costs nothing.

**CORRECTION, 2026-07-27 (by the next owner, from the verbatim source): the
seam is a LOCALIZATION, not a pushout, and the field has been WEAKENED.**

The pin above is kept — no colimit appears in any statement — but the
`isPushout` field it shipped with **asked for strictly more than 00R7's proof
produces**, and the "FAITHFULNESS OF `isPushout`" paragraph below was wrong on
exactly that point.  The evidence is inside 00R7's own proof, one paragraph
above its last sentence, where the properties of the system are listed:

> With these choices, we have for each `λ₃ ≤ λ ≤ μ` that
> `S_λ ⊗_{R_λ} R_μ → S_μ` is **a localization**, `S'_λ ⊗_{S_λ} S_μ → S'_μ` is
> **a localization**, and the map `M_λ ⊗_{S'_λ} S'_μ → M_μ` is an isomorphism.

Only the *module* comparison is an isomorphism, and it is taken over `S'_λ`,
not over `S_λ`.  So the `=` signs in the last sentence ("Then
`S = S_λ ⊗_{R_λ} R` ... and `M = M_λ ⊗_{S_λ} S` ...") are the source's usual
abuse: read literally the first of them contradicts the property list two
lines earlier, since a localization is not an isomorphism.  Passing
`S'_λ ⊗_{S_λ} S_μ → S'_μ` to the colimit over `μ` gives that
`S'_λ ⊗_{S_λ} S → S'` is a localization — and at a FIXED `λ` it genuinely is
not an isomorphism.  Concretely, with `S_λ = R_λ`, `S = R` and
`S'_λ = (R_λ[t])_{(𝔭_λ, t)}`, the ring `S'_λ ⊗_{R_λ} R` is the localization of
`R[t]` at the image of `R_λ[t] ∖ (𝔭_λ, t)`, in which `1 + a t` is not
invertible for `a ∈ R` outside `R_λ`; it is not even local, so it cannot be
`S' = R[t]_{(𝔪, t)}`.

**The field is therefore now `isLocalizationTensor`: `A` is a LOCALIZATION of
`B ⊗_{Mid} Tot`.**  Three things to note about the repair:

* *It is a weakening, so it cannot break anything.*  Any stage satisfying the
  old field satisfies the new one (an isomorphism is the localization at `1`),
  so the leaf below is strictly easier than before and no consumer of the OLD
  field can have been relying on more than the new one delivers.
* *Flatness alone would have been too weak, and this was checked.*  The
  obvious weakest field, "`A` is flat over `B ⊗_{Mid} Tot`", is DEGENERATE:
  the junk stage `Base = Mid = Tot = ℤ_(p)` (or `ℚ`) makes `B ⊗_{Mid} Tot = B`
  and the field becomes "`A` is flat over `B`" — the conclusion itself.  With
  `IsLocalization` that junk stage instead demands "`A` is a localization of
  `B`", which is false in general, so the leaf stays non-degenerate.
* *The consumer is unchanged in substance*: `Tot` flat over `Mid` (00MP at the
  stage) base-changes to `B ⊗_{Mid} Tot` flat over `B`, a localization is flat
  (`IsLocalization.flat`), and `Module.Flat.trans` composes the two.  That is
  one extra step over the old one-line base change.

**WHY, and this is an argument rather than a taste.**

1. *It is the seam the source itself ends on.*  The last sentence of 00R7's
   proof is verbatim "Then `S = S_λ ⊗_{R_λ} R` is flat over `R`, and
   `M = M_λ ⊗_{S_λ} S` is flat over `S` (since the base change of a flat
   module is flat)."  At `M = S' = A`, `S = B` that is a base change followed
   by a localization, and nothing else — see the CORRECTION above for why the
   localization cannot be dropped.
2. *The infrastructure already exists, so nothing has to be invented.*  After
   the correction above the three ingredients are `Module.Flat.baseChange`
   (`Flat R M → Flat S (S ⊗[R] M)`), `IsLocalization.flat`
   (`Mathlib/RingTheory/Flat/Localization.lean:36`) and `Module.Flat.trans`
   (`Mathlib/RingTheory/Flat/Stability.lean:62`), all in the pin.  The
   assembly below is the same instance plumbing plus those three lines.  A
   colimit API would have had to be written, and — per the refutation in the
   note above — written correctly on the first try or it manufactures a false
   leaf.
3. *A colimit API in a statement forces a transport that a stage does not.*
   `Ring.DirectLimit` CONSTRUCTS a ring; `R`, `B`, `A` in this development are
   given rings carrying `IsLocalRing`, `Module.Flat` and `EssFinitePresentation`
   hypotheses.  Stating "R = colim R_λ" as an equality of types is impossible
   and as a `RingEquiv` means transporting every one of those hypotheses across
   it at every use.  The predicate form (a cocone `R_λ → R` plus "every element
   comes from some λ" plus "two elements equal downstairs become equal at some
   μ") avoids the transport, but to be USEFUL it must also carry all six
   properties of 10.127.13 — each of which is a separate opportunity to state
   something false, and none of which the consumer looks at.
4. *The free-floating rule makes the alternative impossible anyway.*  A colimit
   API stated now would be consumed only inside the proof of a still-sorried
   leaf, and a sorried body contributes no dependency edges — so it would be
   free-floating, which this development forbids.  That is the same constraint
   that forced the previous owner's decision, one level down.

**WHAT THIS BUYS THE `046Y` OWNER** (`essFinitePresentation_of_essFiniteType_of_flat_quotientMap`'s
open leaf `fg_ker_of_flat_quotientMap` is where 046Y will be stated).  046Y =
10.128.4 has two conclusions, and the seam serves them differently — this was
checked against the source, not assumed:

* *"`N/u(M)` is flat over `R`"* — the SAME seam works verbatim.  046Y's proof
  ends at a finite λ with `N_λ/u_λ(M_λ)` flat over `R_λ`, and
  `N/u(M)` is a LOCALIZATION of `(N_λ/u_λ(M_λ)) ⊗_{S_λ} S` — not an
  isomorphism; see the CORRECTION above, which applies here verbatim, because
  cokernels commute with base change but the comparison map of the system is a
  localization at every stage.  So base change plus `IsLocalization.flat` plus
  `Module.Flat.trans` closes it with no colimit API, exactly as here.
* *"`u` is injective"* — the seam does **not** serve this, and pretending
  otherwise would be the false step.  `u_λ` injective gives `u = u_λ ⊗ id`
  injective only if `S` were flat over `S_λ`, which is NOT among 10.127.13's
  conclusions.  The real reason is that filtered colimits are EXACT.  So the
  one place 046Y genuinely needs colimit machinery is that exactness — and
  even there nothing has to be invented: mathlib's
  `Module.DirectLimit.of.zero_exact` (`Mathlib/Algebra/Colimit/Module.lean:272`)
  is precisely the ingredient, and `Module.DirectLimit.lift_injective` is the
  packaged form.

So the recorded answer to "what colimit API did you pin" is: **none in any
statement; a base change at a finite Noetherian stage followed by a
localization, for every flatness conclusion, and mathlib's existing
`Module.DirectLimit` inside proofs wherever exactness of the colimit is
genuinely needed.**

**AXIS SEARCHED.**  Ways to state the OUTPUT of Stacks 10.127.13 + 10.128.3 so
that 00R7's endgame can consume it.  NOT searched: whether the approximation
leaf below can be cut further.  A cut into "10.127.13" + "10.128.3" was
considered and rejected for a mechanical reason worth recording — the
assembly of those two is the paragraph of 00R7's proof beginning "Note that
this also implies", which verifies that the FIBRE system
`(S_λ/𝔭_λ S_λ → S'_λ/𝔭_λ S'_λ, M_λ/𝔭_λ M_λ)` is again a system as in
10.127.13.  That verification is itself substantial, so cutting there
produces three leaves of which the "assembly" is not glue, and it is the
first thing to reconsider if the leaf below turns out to be too big to prove
in one go.

**UPDATE 2026-07-28: the approximation leaf HAS now been cut, and the objection
above was right about the wrong split.**  The fibre-system verification is
indeed not glue — so it is not in the assembly; it is inside
`exists_flatFibre_index_of_noetherianApproxSystem`, one of four declarations
that replace the leaf.  The pin "no filtered colimit appears in the statement of
any leaf" is the ONE decision of this note that has been reversed, and only
because the free-floating objection that forced it (reason 4 below) expires
exactly when the assembly is written.  The full argument is the section note
"THE CUT OF THE APPROXIMATION LEAF, TAKEN 2026-07-28" further down; read it
before treating anything in this note as current.
-/

/-- **THE OUTPUT OF STACKS 10.127.13 + 10.128.3, in the only form 00R7's
endgame consumes** — a NOETHERIAN stage under `v : B →+* A` at which both of
00R7's flatness hypotheses already hold, together with the identification of
`A` as a base change from that stage.

Read the section note above for why this, and not a filtered colimit, is what
gets stated.  In Stacks' notation the three carriers are `R_λ`, `S_λ`, `S'_λ`
for one sufficiently large `λ`, and `midToB`, `totToA` are the structure maps
`S_λ → S`, `S'_λ → S'` of the colimit.

**WHY IT IS SAFE — the conclusion is deliberately as WEAK as it can be while
still discharging 00R7.**  Everything the assembly does not use has been left
out, so this datum asks for strictly less than 10.127.13 + 10.128.3 deliver,
and a leaf producing it can only be easier than the source lemma.  In
particular there is deliberately **no** map `Base →+* R`, **no** locality
requirement on `midToB`/`totToA`, **no** localization property of the
transition maps, and **no** directed index set: the assembly needs none of
them.  Conversely, everything that IS here is used — `isNoetherian*`,
`isLocalRing*` and `isLocalHom*` by 00MP, `flatBase` and `flatFibre` as 00MP's
two hypotheses, and `comm` + `isLocalizationTensor` by the base-change step.

**FAITHFULNESS OF `isLocalizationTensor`, and a CORRECTION (2026-07-27).**
This field used to read `Algebra.IsPushout Mid Tot B A`, i.e. `A ≅ Tot ⊗[Mid] B`,
justified as "`M = M_λ ⊗_{S_λ} S`, the last line of 00R7's proof".  **That was
too strong**: the paragraph of 00R7's proof immediately above that sentence
lists `S'_λ ⊗_{S_λ} S_μ → S'_μ` as *a localization*, and only the module
comparison `M_λ ⊗_{S'_λ} S'_μ → M_μ` — taken over `S'_λ`, not `S_λ` — as an
isomorphism.  The `=` in the last sentence is the source's abuse of notation:
read literally it contradicts the property list two lines above it.  So the
field now asks only for what the argument delivers, `A` a LOCALIZATION of
`B ⊗[Mid] Tot`; the full argument, including why plain flatness there would be
degenerate, is the CORRECTION block in the section note above.

The five `letI`s in its type are the algebra structures carried by the four
ring maps of the square, and the two `IsScalarTower`s are forced by `comm`;
they are written inline rather than assumed so that the field cannot be
satisfied by some *other* algebra structure on the same rings, which is the
duplicate-instance trap this development has been bitten by repeatedly.  The
sixth `letI` is the induced algebra structure on `A` over `B ⊗[Mid] Tot`,
built from the two `IsScalarTower`s by `Algebra.TensorProduct.lift`, so that
`IsLocalization` cannot be read against some unrelated map. -/
structure FlatNoetherianStage {B A : Type u} [CommRing B] [CommRing A] (v : B →+* A) where
  /-- `R_λ`, Stacks' Noetherian local base, essentially of finite type over `ℤ`. -/
  Base : Type u
  /-- `S_λ`, the stage of `S = B`. -/
  Mid : Type u
  /-- `S'_λ`, the stage of `S' = M = A`. -/
  Tot : Type u
  [commRingBase : CommRing Base]
  [commRingMid : CommRing Mid]
  [commRingTot : CommRing Tot]
  [isLocalRingBase : IsLocalRing Base]
  [isLocalRingMid : IsLocalRing Mid]
  [isLocalRingTot : IsLocalRing Tot]
  [isNoetherianBase : IsNoetherianRing Base]
  [isNoetherianMid : IsNoetherianRing Mid]
  [isNoetherianTot : IsNoetherianRing Tot]
  /-- `R_λ → S_λ`. -/
  baseToMid : Base →+* Mid
  /-- `S_λ → S'_λ`. -/
  midToTot : Mid →+* Tot
  [isLocalHomBaseToMid : IsLocalHom baseToMid]
  [isLocalHomMidToTot : IsLocalHom midToTot]
  /-- The colimit structure map `S_λ → S`. -/
  midToB : Mid →+* B
  /-- The colimit structure map `S'_λ → S'`. -/
  totToA : Tot →+* A
  /-- The square `R_λ → S_λ → S'_λ → S'` / `S_λ → S → S'` commutes. -/
  comm : totToA.comp midToTot = v.comp midToB
  /-- 00MP's hypothesis (4) at the stage: `M_λ` is flat over `R_λ`.  This is
  the first of the two applications of Stacks 10.128.3. -/
  flatBase : (midToTot.comp baseToMid).Flat
  /-- 00MP's hypothesis (3) at the stage: `M_λ/𝔭_λ M_λ` is flat over
  `S_λ/𝔭_λ S_λ`.  This is the second application of Stacks 10.128.3, to the
  fibre system. -/
  flatFibre : (Ideal.quotientMap
      ((IsLocalRing.maximalIdeal Base).map (midToTot.comp baseToMid)) midToTot
      (map_le_comap_map_comp baseToMid midToTot (IsLocalRing.maximalIdeal Base))).Flat
  /-- `M` is a LOCALIZATION of `M_λ ⊗_{S_λ} S`, which is what 00R7's proof
  delivers — see the CORRECTION in the section note above, and the docstring
  paragraph "FAITHFULNESS OF `isLocalizationTensor`". -/
  isLocalizationTensor :
    letI : Algebra Mid Tot := midToTot.toAlgebra
    letI : Algebra Mid B := midToB.toAlgebra
    letI : Algebra Tot A := totToA.toAlgebra
    letI : Algebra B A := v.toAlgebra
    letI : Algebra Mid A := (v.comp midToB).toAlgebra
    haveI : IsScalarTower Mid B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower Mid Tot A :=
      IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun comm x).symm
    letI : Algebra (B ⊗[Mid] Tot) A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom Mid B A)
        (IsScalarTower.toAlgHom Mid Tot A) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (B ⊗[Mid] Tot), IsLocalization W A

/-! ### THE CUT OF THE APPROXIMATION LEAF, TAKEN 2026-07-28 — the system IS stated

**SECTION NOTE for `NoetherianApproxSystem` and the four declarations under it.**

The section note above pinned "**no filtered colimit appears in the statement of
any leaf**" and, on the strength of it, the previous owner left
`nonempty_flatNoetherianStage_of_essFinitePresentation` as ONE leaf carrying all
of 10.127.11 + 10.127.13 + 10.128.3.  Its own "SURVEY FOR THE NEXT OWNER"
recorded the obstruction in a refutable form, which is why it could be checked:

> every honest cut of it needs the DIRECTED SYSTEM exposed in a statement,
> because 10.128.3's conclusion is "for `λ` big enough", which is not
> expressible about a single stage; a cut that merely hands the next leaf one
> stage is fake, since the second leaf would have to rebuild the system anyway.

**That paragraph is correct, and it is a specification, not a prohibition.**  The
cut below satisfies it literally: the directed system IS exposed, as
`NoetherianApproxSystem` — so 10.128.3's "for `λ` big enough" is stated in the
only honest form it has, `∀ i, ∃ j ≥ i, …`, and nothing is handed one stage.

**WHAT ACTUALLY CHANGED — the objection that used to block this has expired.**
The four reasons the older note gave against putting a colimit in a statement
were re-run one by one, and exactly one of them was load-bearing:

1. *"a colimit API forces a transport"* — true of `Ring.DirectLimit`, which
   CONSTRUCTS a ring, and false of the predicate form.  `NoetherianApproxSystem`
   never asserts `R = colim R_λ` as an equality or a `RingEquiv`; it carries a
   cocone `baseToR` plus the two ordinary filtered-colimit conditions
   (`base_surj`, `base_sep`).  No hypothesis on `R`, `B`, `A` is ever transported.
2. *"to be USEFUL it must carry all six properties of 10.127.13 — each a separate
   opportunity to state something false, and none of which the consumer looks
   at"* — the second clause is what changed.  Under this cut the consumers are
   `exists_flatBase_index_of_noetherianApproxSystem`,
   `exists_flatFibre_index_of_noetherianApproxSystem` and
   `exists_isLocalization_tensor_of_noetherianApproxSystem`, and they look at
   ALL of them: the Noetherian fields and the colimit conditions are what
   10.128.3's Tor argument runs on, and `isLocalizationTotT` is the whole of the
   third.  A field nobody reads is a risk; a field three leaves consume is an
   interface.
3. *"the free-floating rule makes the alternative impossible anyway — a colimit
   API stated now would be consumed only inside the proof of a still-sorried
   leaf, and a sorried body contributes no dependency edges"* — **this was the
   real obstruction, and it dissolves exactly when the assembly is written.**
   The leaf below is no longer sorried: its body is a real term that destructures
   a `NoetherianApproxSystem` and builds a `FlatNoetherianStage` out of one of its
   stages.  So the structure and all four leaves are in the cone of
   `fermat_last_theorem` by the same edges that carried the old single leaf.
   Glue-first is not merely permitted here, it is what makes the cut legal.
4. *the three-way split "10.127.13 / 10.128.3 / assembly" leaves an assembly that
   is not glue*, because 00R7's paragraph beginning "Note that this also implies"
   — the verification that the FIBRE system is again a system as in 10.127.13 —
   is itself substantial.  **Still true, and it is why that split is not the one
   taken.**  Here the fibre-system verification is not in the assembly: it is
   inside `exists_flatFibre_index_of_noetherianApproxSystem`, whose statement is
   about the ring-level system and whose proof owns both the fibre check and the
   second application of 10.128.3.  The assembly that remains is genuinely glue —
   two `obtain`s, one proven lemma, and a structure instance.
   *(Update 2026-07-28: that leaf is now PROVEN, and the two halves it owned have
   been separated — the fibre check is `isNoetherianFlatDescentSystem_fibre`, the
   second application of 10.128.3 is the SHARED engine
   `exists_flat_index_of_isNoetherianFlatDescentSystem` that the base leaf uses too.
   See the section note "10.128.3 IS ONE LEMMA APPLIED TWICE".)*

**WHY THE `∀ i, ∃ j ≥ i` FORM, and why it is not a strengthening.**  10.128.3
states "for some `λ`", but its PROOF fixes `λ` and produces `λ' ≥ λ` (it names
the generators of `Tor_1^{R_λ}(M_λ, R_λ/𝔪_λ)`, which is finite because `S'_λ` is
Noetherian, and pushes them to zero at a large enough `λ'`).  So the cofinal form
is what the argument delivers.  It is also the only form that composes: after
`exists_flatBase_index_of_noetherianApproxSystem` hands back `j₁`, the fibre
application must be able to start AT `j₁`, or the two conclusions land at
unrelated indices and cannot be combined.

**WHAT THE ASSEMBLY HAD TO PROVE, and it is real content.**  Combining the two
still needs base flatness to survive the passage `j₁ ≤ j₂`, and that is
`NoetherianApproxSystem.flat_base_of_le` below, PROVEN: `Tot j₂` is a
localization of `Base j₂ ⊗_{Base j₁} Tot j₁` (`isLocalizationTotBaseT`), the
tensor factor is flat over `Base j₂` by base change, and `Module.Flat.trans`
composes — the same three mathlib ingredients the endgame below uses, run one
level down.  This is why `isLocalizationTotBaseT` is a field even though it is
derivable from `isLocalizationMidT` and `isLocalizationTotT`: it is CONSUMED, by
a proven lemma, in the assembly.

**AXIS SEARCHED.**  Ways to cut `nonempty_flatNoetherianStage_of_essFinitePresentation`
given that the directed system must appear in a statement.  NOT searched: whether
`NoetherianApproxSystem`'s existence (10.127.11 + 10.127.13) can itself be cut —
it can, and the survey in its docstring says where to start.  Also NOT searched:
whether `Mid` can be dropped from the system.  It cannot, because
`isLocalizationTotT` and the fibre leaf are both about `Mid`, but a reader
looking for economy should know nobody tried.

**THE CHECK THAT WOULD REFUTE THIS CUT.**  Exhibit a `NoetherianApproxSystem g v`
— any one, junk included — for which one of the three sorried leaves is false.
The junk stages that the `FlatNoetherianStage` docstring rules out are ruled out
here for the same reason: `Base = Mid = Tot = R = B = A` fails `isNoetherianBase`
unless `R` is Noetherian, and `Base = Mid = Tot = ℤ_(p)` fails `base_surj`.
-/

/-- **THE DIRECTED SYSTEM OF 10.127.13, as a predicate rather than a
construction** — a filtered system of NOETHERIAN local stages
`Base i → Mid i → Tot i` whose colimit is `R → B → A`, with the transition maps
localizations after base change.

In Stacks' notation the three towers are `R_λ`, `S_λ`, `S'_λ` and the module `M`
is absent because 00R7 is applied at `M = S' = A`, where the presentation of `M`
over `S'` may be taken to be `(S')^{⊕0} → (S')^{⊕1} → M → 0`; 10.127.13's
property (6) (`M_λ ⊗_{S_λ} S_μ → M_μ` an isomorphism) is then vacuous and
`M_λ = S'_λ` needs no separate carrier.

**Why `CommRingCat` and not `Type u`.**  Purely to get the `CommRing` instances
for a FAMILY of carriers without a `letI` in front of every field: `Base : Λ →
CommRingCat.{u}` makes `CommRing ↥(Base i)` an instance, where `Base : Λ → Type
u` would force `commRingBase : ∀ i, CommRing (Base i)` and then a `letI` prelude
on all thirty fields below.  No category theory is used — the transition maps are
plain `RingHom`s, not `⟶`s, and no (co)limit of the category is ever mentioned.

**Why a raw relation `le` and not `[Preorder Λ]`.**  `Λ` is a field, so a
`Preorder Λ` instance cannot be an instance-implicit binder of the structure, and
`@IsDirected Λ preorder.toLE.le` is worse to read than the three explicit fields.

**FAITHFULNESS.**  Every field is one of 10.127.11's or 10.127.13's conclusions,
so this datum is no stronger than what those lemmas produce and
`nonempty_noetherianApproxSystem_of_essFinitePresentation` is true if they are:

* `isNoetherian*` — each `R_λ` is essentially of finite type over `ℤ`, each
  `S_λ` over `R_λ`, each `S'_λ` over `S_λ`, hence all three are Noetherian.  Only
  Noetherianity is asked for, not the `ℤ`-finiteness, because only Noetherianity
  is used;
* `isLocalRing*`, `isLocalHom*` — 10.127.11's system is one of LOCAL rings and
  LOCAL homomorphisms, including the structure maps to the colimit;
* `base_surj`/`base_sep` and their two siblings — the ordinary characterisation
  of a filtered colimit, replacing "the colimit of the system is `R → B → A`";
* `isLocalizationMidT` — 10.127.13(5) verbatim, `S_λ ⊗_{R_λ} R_μ → S_μ` a
  localization, weakened from "at a prime ideal" to "at some submonoid" because
  that is all any consumer uses;
* `isLocalizationTotT` — the source's own property list one paragraph above the
  end of 00R7's proof, `S'_λ ⊗_{S_λ} S_μ → S'_μ` a localization.  This is the
  property whose misreading as an ISOMORPHISM produced the `isPushout` field that
  had to be repaired on 2026-07-27; see the CORRECTION block above;
* `isLocalizationTotBaseT` — 10.127.11 applied to `R → S'` rather than to
  `R → S`.  It is DERIVABLE from the previous two (a localization base-changes to
  a localization, and `S'_λ ⊗_{R_λ} R_μ ≅ S'_λ ⊗_{S_λ} (S_λ ⊗_{R_λ} R_μ)`), and
  is a field anyway because `flat_base_of_le` consumes it directly and rederiving
  it there would be strictly more work than proving it once inside
  `nonempty_noetherianApproxSystem_of_essFinitePresentation`.

**NON-DEGENERACY.**  The one-object system `Λ = PUnit`, `Base = Mid = Tot = R =
B = A` satisfies every structural field but demands `IsNoetherianRing R`, `B`,
`A` — exactly the junk stage that `FlatNoetherianStage`'s own check rules out —
and the constant system on a Noetherian subring fails `base_surj`. -/
structure NoetherianApproxSystem {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    (g : R →+* B) (v : B →+* A) where
  /-- The index set `Λ`. -/
  Λ : Type u
  /-- `Λ` is nonempty. -/
  nonemptyΛ : Nonempty Λ
  /-- The order on `Λ`, as a raw relation. -/
  le : Λ → Λ → Prop
  /-- `le` is reflexive. -/
  le_rfl : ∀ i, le i i
  /-- `le` is transitive. -/
  le_trans' : ∀ {i j k}, le i j → le j k → le i k
  /-- `Λ` is directed: this is what "filtered colimit" means here. -/
  directed : ∀ i j, ∃ k, le i k ∧ le j k
  /-- `R_λ`, the Noetherian local base at stage `i`. -/
  Base : Λ → CommRingCat.{u}
  /-- `S_λ`, the stage of `S = B`. -/
  Mid : Λ → CommRingCat.{u}
  /-- `S'_λ`, the stage of `S' = M = A`. -/
  Tot : Λ → CommRingCat.{u}
  /-- Each `R_λ` is local. -/
  isLocalRingBase : ∀ i, IsLocalRing (Base i)
  /-- Each `S_λ` is local. -/
  isLocalRingMid : ∀ i, IsLocalRing (Mid i)
  /-- Each `S'_λ` is local. -/
  isLocalRingTot : ∀ i, IsLocalRing (Tot i)
  /-- Each `R_λ` is Noetherian.  This, not essential finiteness over `ℤ`, is what
  10.128.3's Tor argument and 00MP consume. -/
  isNoetherianBase : ∀ i, IsNoetherianRing (Base i)
  /-- Each `S_λ` is Noetherian. -/
  isNoetherianMid : ∀ i, IsNoetherianRing (Mid i)
  /-- Each `S'_λ` is Noetherian.  This is the field that makes
  `Tor_1^{R_λ}(M_λ, R_λ/𝔪_λ)` finitely generated in 10.128.3. -/
  isNoetherianTot : ∀ i, IsNoetherianRing (Tot i)
  /-- `R_λ → S_λ`. -/
  baseToMid : ∀ i, Base i →+* Mid i
  /-- `S_λ → S'_λ`. -/
  midToTot : ∀ i, Mid i →+* Tot i
  /-- `R_λ → S_λ` is local. -/
  isLocalHomBaseToMid : ∀ i, IsLocalHom (baseToMid i)
  /-- `S_λ → S'_λ` is local. -/
  isLocalHomMidToTot : ∀ i, IsLocalHom (midToTot i)
  /-- The transition map `R_λ → R_μ`. -/
  baseT : ∀ {i j}, le i j → (Base i →+* Base j)
  /-- The transition map `S_λ → S_μ`. -/
  midT : ∀ {i j}, le i j → (Mid i →+* Mid j)
  /-- The transition map `S'_λ → S'_μ`. -/
  totT : ∀ {i j}, le i j → (Tot i →+* Tot j)
  /-- The cocone map `R_λ → R`. -/
  baseToR : ∀ i, Base i →+* R
  /-- The cocone map `S_λ → S`. -/
  midToB : ∀ i, Mid i →+* B
  /-- The cocone map `S'_λ → S'`. -/
  totToA : ∀ i, Tot i →+* A
  /-- The square `R_λ → S_λ → S` / `R_λ → R → S` commutes. -/
  comm_baseMid : ∀ i, (midToB i).comp (baseToMid i) = g.comp (baseToR i)
  /-- The square `S_λ → S'_λ → S'` / `S_λ → S → S'` commutes. -/
  comm_midTot : ∀ i, (totToA i).comp (midToTot i) = v.comp (midToB i)
  /-- The vertical maps are natural in `Λ`, at the `R_λ → S_λ` level. -/
  comm_baseT : ∀ {i j} (h : le i j), (baseToMid j).comp (baseT h) = (midT h).comp (baseToMid i)
  /-- The vertical maps are natural in `Λ`, at the `S_λ → S'_λ` level. -/
  comm_midT : ∀ {i j} (h : le i j), (midToTot j).comp (midT h) = (totT h).comp (midToTot i)
  /-- `baseT` is functorial. -/
  baseT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (baseT h₂).comp (baseT h₁) = baseT (le_trans' h₁ h₂)
  /-- `midT` is functorial. -/
  midT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (midT h₂).comp (midT h₁) = midT (le_trans' h₁ h₂)
  /-- `totT` is functorial. -/
  totT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (totT h₂).comp (totT h₁) = totT (le_trans' h₁ h₂)
  /-- `baseToR` is a cocone. -/
  comm_baseToR : ∀ {i j} (h : le i j), (baseToR j).comp (baseT h) = baseToR i
  /-- `midToB` is a cocone. -/
  comm_midToB : ∀ {i j} (h : le i j), (midToB j).comp (midT h) = midToB i
  /-- `totToA` is a cocone. -/
  comm_totToA : ∀ {i j} (h : le i j), (totToA j).comp (totT h) = totToA i
  /-- The transitions are local. -/
  isLocalHomBaseT : ∀ {i j} (h : le i j), IsLocalHom (baseT h)
  /-- The transitions are local. -/
  isLocalHomMidT : ∀ {i j} (h : le i j), IsLocalHom (midT h)
  /-- The transitions are local. -/
  isLocalHomTotT : ∀ {i j} (h : le i j), IsLocalHom (totT h)
  /-- The cocone maps are local.  This is what makes `𝔪_R` the colimit of the
  `𝔪_{R_λ}`, which the fibre leaf below needs. -/
  isLocalHomBaseToR : ∀ i, IsLocalHom (baseToR i)
  /-- The cocone maps are local. -/
  isLocalHomMidToB : ∀ i, IsLocalHom (midToB i)
  /-- The cocone maps are local. -/
  isLocalHomTotToA : ∀ i, IsLocalHom (totToA i)
  /-- `R` is the colimit, half one: every element comes from some stage. -/
  base_surj : ∀ x : R, ∃ i, ∃ y : Base i, baseToR i y = x
  /-- `B` is the colimit, half one. -/
  mid_surj : ∀ x : B, ∃ i, ∃ y : Mid i, midToB i y = x
  /-- `A` is the colimit, half one. -/
  tot_surj : ∀ x : A, ∃ i, ∃ y : Tot i, totToA i y = x
  /-- `R` is the colimit, half two: elements identified downstairs are identified
  at some later stage. -/
  base_sep : ∀ i (x y : Base i), baseToR i x = baseToR i y →
    ∃ j, ∃ h : le i j, baseT h x = baseT h y
  /-- `B` is the colimit, half two. -/
  mid_sep : ∀ i (x y : Mid i), midToB i x = midToB i y →
    ∃ j, ∃ h : le i j, midT h x = midT h y
  /-- `A` is the colimit, half two. -/
  tot_sep : ∀ i (x y : Tot i), totToA i x = totToA i y →
    ∃ j, ∃ h : le i j, totT h x = totT h y
  /-- **10.127.13(5)**: `S_μ` is a localization of `R_μ ⊗_{R_λ} S_λ`. -/
  isLocalizationMidT : ∀ {i j} (h : le i j),
    letI : Algebra (Base i) (Mid i) := (baseToMid i).toAlgebra
    letI : Algebra (Base i) (Base j) := (baseT h).toAlgebra
    letI : Algebra (Base i) (Mid j) := ((baseToMid j).comp (baseT h)).toAlgebra
    letI : Algebra (Base j) (Mid j) := (baseToMid j).toAlgebra
    letI : Algebra (Mid i) (Mid j) := (midT h).toAlgebra
    haveI : IsScalarTower (Base i) (Base j) (Mid j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (Base i) (Mid i) (Mid j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm_baseT h) x
    letI : Algebra (Base j ⊗[Base i] Mid i) (Mid j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Base i) (Base j) (Mid j))
        (IsScalarTower.toAlgHom (Base i) (Mid i) (Mid j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (Base j ⊗[Base i] Mid i), IsLocalization W (Mid j)
  /-- **The property 00R7's proof lists for the top tower**: `S'_μ` is a
  localization of `S_μ ⊗_{S_λ} S'_λ`.  NOT an isomorphism — see the CORRECTION
  block in the section note "THE COLIMIT-API DECISION". -/
  isLocalizationTotT : ∀ {i j} (h : le i j),
    letI : Algebra (Mid i) (Tot i) := (midToTot i).toAlgebra
    letI : Algebra (Mid i) (Mid j) := (midT h).toAlgebra
    letI : Algebra (Mid i) (Tot j) := ((midToTot j).comp (midT h)).toAlgebra
    letI : Algebra (Mid j) (Tot j) := (midToTot j).toAlgebra
    letI : Algebra (Tot i) (Tot j) := (totT h).toAlgebra
    haveI : IsScalarTower (Mid i) (Mid j) (Tot j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (Mid i) (Tot i) (Tot j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm_midT h) x
    letI : Algebra (Mid j ⊗[Mid i] Tot i) (Tot j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Mid i) (Mid j) (Tot j))
        (IsScalarTower.toAlgHom (Mid i) (Tot i) (Tot j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (Mid j ⊗[Mid i] Tot i), IsLocalization W (Tot j)
  /-- **10.127.11(4) applied to `R → S'`**: `S'_μ` is a localization of
  `R_μ ⊗_{R_λ} S'_λ`.  Derivable from the two fields above; carried because
  `NoetherianApproxSystem.flat_base_of_le` consumes it. -/
  isLocalizationTotBaseT : ∀ {i j} (h : le i j),
    letI : Algebra (Base i) (Tot i) := ((midToTot i).comp (baseToMid i)).toAlgebra
    letI : Algebra (Base i) (Base j) := (baseT h).toAlgebra
    letI : Algebra (Base i) (Tot j) :=
      ((midToTot j).comp ((baseToMid j).comp (baseT h))).toAlgebra
    letI : Algebra (Base j) (Tot j) := ((midToTot j).comp (baseToMid j)).toAlgebra
    letI : Algebra (Tot i) (Tot j) := (totT h).toAlgebra
    haveI : IsScalarTower (Base i) (Base j) (Tot j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (Base i) (Tot i) (Tot j) :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (congrArg (midToTot j) (DFunLike.congr_fun (comm_baseT h) x)).trans
          (DFunLike.congr_fun (comm_midT h) ((baseToMid i) x))
    letI : Algebra (Base j ⊗[Base i] Tot i) (Tot j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Base i) (Base j) (Tot j))
        (IsScalarTower.toAlgHom (Base i) (Tot i) (Tot j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (Base j ⊗[Base i] Tot i), IsLocalization W (Tot j)

/-- **BASE FLATNESS IS STABLE UPWARDS IN THE SYSTEM** (PROVEN).  If `S'_λ` is
flat over `R_λ` and `λ ≤ μ`, then `S'_μ` is flat over `R_μ`.

This is what lets the two cofinal existence leaves below be COMBINED: the first
delivers base flatness at `j₁`, the second delivers fibre flatness at some
`j₂ ≥ j₁`, and without this lemma the two conclusions sit at different indices
and no single stage carries both.

The proof is 00R7's own endgame run one level down, on the three ingredients the
section note above named: `S'_μ` is a localization of `R_μ ⊗_{R_λ} S'_λ`
(`isLocalizationTotBaseT`), that tensor product is flat over `R_μ` by
`Module.Flat.baseChange`, a localization is flat (`IsLocalization.flat`), and
`Module.Flat.trans` composes the two. -/
theorem NoetherianApproxSystem.flat_base_of_le {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A] {g : R →+* B} {v : B →+* A}
    (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j)
    (hi : ((sys.midToTot i).comp (sys.baseToMid i)).Flat) :
    ((sys.midToTot j).comp (sys.baseToMid j)).Flat := by
  letI : Algebra (sys.Base i) (sys.Tot i) :=
    ((sys.midToTot i).comp (sys.baseToMid i)).toAlgebra
  letI : Algebra (sys.Base i) (sys.Base j) := (sys.baseT h).toAlgebra
  letI : Algebra (sys.Base i) (sys.Tot j) :=
    ((sys.midToTot j).comp ((sys.baseToMid j).comp (sys.baseT h))).toAlgebra
  letI : Algebra (sys.Base j) (sys.Tot j) := ((sys.midToTot j).comp (sys.baseToMid j)).toAlgebra
  letI : Algebra (sys.Tot i) (sys.Tot j) := (sys.totT h).toAlgebra
  haveI : IsScalarTower (sys.Base i) (sys.Base j) (sys.Tot j) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (sys.Base i) (sys.Tot i) (sys.Tot j) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (congrArg (sys.midToTot j) (DFunLike.congr_fun (sys.comm_baseT h) x)).trans
        (DFunLike.congr_fun (sys.comm_midT h) ((sys.baseToMid i) x))
  letI : Algebra (sys.Base j ⊗[sys.Base i] sys.Tot i) (sys.Tot j) :=
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (sys.Base i) (sys.Base j) (sys.Tot j))
      (IsScalarTower.toAlgHom (sys.Base i) (sys.Tot i) (sys.Tot j))
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  obtain ⟨W, hW⟩ := sys.isLocalizationTotBaseT h
  haveI : Module.Flat (sys.Base i) (sys.Tot i) := hi
  haveI : Module.Flat (sys.Base j) (sys.Base j ⊗[sys.Base i] sys.Tot i) :=
    Module.Flat.baseChange _ _ _
  haveI : IsScalarTower (sys.Base j) (sys.Base j ⊗[sys.Base i] sys.Tot i) (sys.Tot j) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      show ((sys.midToTot j).comp (sys.baseToMid j)) b = _
      simp [RingHom.algebraMap_toAlgebra]
  haveI : Module.Flat (sys.Base j ⊗[sys.Base i] sys.Tot i) (sys.Tot j) :=
    IsLocalization.flat _ W
  exact Module.Flat.trans (sys.Base j) (sys.Base j ⊗[sys.Base i] sys.Tot i) (sys.Tot j)

/-! ### THE `R_λ` TOWER, CUT OFF AND PROVEN, 2026-07-28

**SECTION NOTE for `NoetherianLocalBaseSystem` and the two declarations under it.**

The previous owner's SURVEY of the approximation leaf ended with:

> this is the one piece that can be landed as a proven lemma; it was not landed
> here only because, with no assembly written, it would be free-floating.

The assembly IS written (it is
`nonempty_flatNoetherianStage_of_essFinitePresentation` below, proven 2026-07-28),
so that objection has expired and the piece is landed here.  `NoetherianApproxSystem`
splits along the obvious seam: its `Base`-tower fields — `Λ` and its order, `Base`,
`isLocalRingBase`, `isNoetherianBase`, `baseT`, `baseToR`, `baseT_comp`,
`comm_baseToR`, `isLocalHomBaseT`, `isLocalHomBaseToR`, `base_surj`, `base_sep` —
mention neither `B` nor `A` nor any localization, so they form a self-contained
datum about `R` alone.  That datum is `NoetherianLocalBaseSystem R`, it is exactly
the OPENING of 10.127.11 ("write the local ring `R` as a filtered colimit of
Noetherian local subrings"), and it is a THEOREM here, not a leaf.

**THE CONSTRUCTION, in one paragraph.**  `Λ = Finset R` ordered by `⊆` — no
`Ring.DirectLimit`, no abstract colimit; the system is concrete and every
transition map is an inclusion of subrings of `R`.  For `s : Finset R` put
`C_s = Subring.closure ↑s` (Noetherian by `is_noetherian_subring_closure`) and

  `R_s = {x : R | ∃ a b ∈ C_s, IsUnit b ∧ x * b = a}`,

the set of fractions `a/b` with `a, b ∈ C_s` and `b` a unit of `R`.  This is a
subring, and — because `R` is LOCAL, so that `b ∈ C_s` is a unit of `R` exactly
when `b ∉ 𝔭_s := 𝔪_R ∩ C_s` — the inclusion `C_s → R_s` is a localization at
`𝔭_s.primeCompl` (`IsLocalization.isLocalization_baseSubring`: `map_units` is
`b⁻¹ = 1/b ∈ R_s`, `surj` is membership itself, and `exists_of_eq` is the
injectivity of `C_s ↪ R`).  Noetherianity is then
`IsLocalization.isNoetherianRing`, locality is `IsLocalization.AtPrime.isLocalRing`,
and `IsLocalHom (R_s → R)` is the computation `x = a/b` invertible in `R` implies
`a` invertible, whence `b/a ∈ R_s` inverts `x` inside `R_s`.  `base_surj` takes
`s = {x}`; `base_sep` is trivial because every `R_s → R` is an inclusion.

**WHY THE HELPER LEMMAS ARE STATED AT `CommRingCat` LEVEL** (`baseStage`,
`baseStageT`, `baseStageToR` and the six facts about them).  Not aesthetics: the
structure instance would not TYPE-CHECK otherwise.  Assembling all eleven fields
in one term makes the kernel re-run the `↥(CommRingCat.of ↥(R_s)) ≡ ↥(R_s)`
conversion once per field, and the total blows the kernel's deterministic-timeout
budget (observed: every field fine in isolation, the assembly `(kernel)
deterministic timeout`).  Paying the conversion once per named lemma, each with
its own budget, leaves the structure instance a syntactic match.  The same trick
is why `baseStageToR_baseStageT` exists rather than a `rfl`: `rfl` for
`↑(Subring.inclusion h x) = ↑x` is also a kernel timeout here, while
`Subring.coe_inclusion` is instant.

**THE CHECK THAT WOULD REFUTE THIS CUT.**  Exhibit a `NoetherianLocalBaseSystem R`
from which no `NoetherianApproxSystem g v` can be built under 00R7's hypotheses.
It cannot be done: `{i | i₀ ≤ i}` is again a base system for every `i₀`, so the
leaf below may always pass to a cofinal restriction before descending `B` and `A`,
which is exactly what 10.127.13 does. -/

/-- **THE `R_λ` TOWER OF STACKS 10.127.11** — a filtered system of NOETHERIAN
LOCAL subrings of `R` whose colimit is `R`, with no reference to `B`, to `A`, or
to any localization.

This is the `Base` half of `NoetherianApproxSystem`, field for field, with `R`
alone as parameter.  Read the section note above for what it is for; its fields
are documented there and in `NoetherianApproxSystem`, whose corresponding fields
they are.

**FAITHFULNESS.**  Every field is one of `NoetherianApproxSystem`'s, so
`nonempty_noetherianLocalBaseSystem` is weaker than the `Base` half of
`nonempty_noetherianApproxSystem_of_essFinitePresentation` and cannot smuggle
anything in.  **NON-DEGENERACY**: the one-object system `Λ = PUnit`,
`Base = R` satisfies every structural field but demands `IsNoetherianRing R`, and
the constant system on a Noetherian subring fails `base_surj`; so the datum is
not free. -/
structure NoetherianLocalBaseSystem (R : Type u) [CommRing R] where
  /-- The index set `Λ`. -/
  Λ : Type u
  /-- `Λ` is nonempty. -/
  nonemptyΛ : Nonempty Λ
  /-- The order on `Λ`, as a raw relation. -/
  le : Λ → Λ → Prop
  /-- `le` is reflexive. -/
  le_rfl : ∀ i, le i i
  /-- `le` is transitive. -/
  le_trans' : ∀ {i j k}, le i j → le j k → le i k
  /-- `Λ` is directed. -/
  directed : ∀ i j, ∃ k, le i k ∧ le j k
  /-- `R_λ`, the Noetherian local base at stage `i`. -/
  Base : Λ → CommRingCat.{u}
  /-- Each `R_λ` is local. -/
  isLocalRingBase : ∀ i, IsLocalRing (Base i)
  /-- Each `R_λ` is Noetherian. -/
  isNoetherianBase : ∀ i, IsNoetherianRing (Base i)
  /-- The transition map `R_λ → R_μ`. -/
  baseT : ∀ {i j}, le i j → (Base i →+* Base j)
  /-- The cocone map `R_λ → R`. -/
  baseToR : ∀ i, Base i →+* R
  /-- `baseT` is functorial. -/
  baseT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (baseT h₂).comp (baseT h₁) = baseT (le_trans' h₁ h₂)
  /-- `baseToR` is a cocone. -/
  comm_baseToR : ∀ {i j} (h : le i j), (baseToR j).comp (baseT h) = baseToR i
  /-- The transitions are local. -/
  isLocalHomBaseT : ∀ {i j} (h : le i j), IsLocalHom (baseT h)
  /-- The cocone maps are local. -/
  isLocalHomBaseToR : ∀ i, IsLocalHom (baseToR i)
  /-- `R` is the colimit, half one. -/
  base_surj : ∀ x : R, ∃ i, ∃ y : Base i, baseToR i y = x
  /-- `R` is the colimit, half two. -/
  base_sep : ∀ i (x y : Base i), baseToR i x = baseToR i y →
    ∃ j, ∃ h : le i j, baseT h x = baseT h y

namespace NoetherianApproxBase

section Construction

-- `[IsLocalRing R]` is deliberately NOT a section variable: locality of `R` is used
-- by exactly the six declarations that carry it explicitly below (everything about
-- `basePrime` and the localization/Noetherian/local facts it feeds), and by nothing
-- else — the subring `baseSubring` and its inclusions make sense over any `CommRing`.
variable {R : Type u} [CommRing R]

/-- `C_s`, the subring of `R` generated by a finite subset — the "coefficients"
of 10.127.11.  Noetherian by `is_noetherian_subring_closure`. -/
abbrev coeffSubring (s : Finset R) : Subring R := Subring.closure (s : Set R)

/-- `R_s`, the localization of `coeffSubring s` at `𝔪_R ∩ coeffSubring s`,
realised inside `R` as the set of fractions `a / b` with `a, b ∈ C_s` and `b` a
unit of `R`.  The subring axioms are the usual fraction arithmetic. -/
def baseSubring (s : Finset R) : Subring R where
  carrier := {x : R | ∃ a ∈ coeffSubring s, ∃ b ∈ coeffSubring s, IsUnit b ∧ x * b = a}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, isUnit_one, one_mul 1⟩
  zero_mem' := ⟨0, zero_mem _, 1, one_mem _, isUnit_one, by ring⟩
  mul_mem' := by
    rintro x y ⟨a, ha, b, hb, hbu, hx⟩ ⟨c, hc, d, hd, hdu, hy⟩
    exact ⟨a * c, mul_mem ha hc, b * d, mul_mem hb hd, hbu.mul hdu, by
      rw [← hx, ← hy]; ring⟩
  add_mem' := by
    rintro x y ⟨a, ha, b, hb, hbu, hx⟩ ⟨c, hc, d, hd, hdu, hy⟩
    refine ⟨a * d + c * b, add_mem (mul_mem ha hd) (mul_mem hc hb), b * d,
      mul_mem hb hd, hbu.mul hdu, ?_⟩
    rw [← hx, ← hy]; ring
  neg_mem' := by
    rintro x ⟨a, ha, b, hb, hbu, hx⟩
    exact ⟨-a, neg_mem ha, b, hb, hbu, by rw [← hx]; ring⟩

/-- `C_s ⊆ R_s`, via `a = a / 1`. -/
theorem coeffSubring_le_baseSubring (s : Finset R) : coeffSubring s ≤ baseSubring s :=
  fun x hx => ⟨x, hx, 1, one_mem _, isUnit_one, mul_one x⟩

/-- `s ↦ R_s` is monotone: this is what makes the system directed. -/
theorem baseSubring_mono {s t : Finset R} (h : s ⊆ t) : baseSubring s ≤ baseSubring t := by
  rintro x ⟨a, ha, b, hb, hbu, hx⟩
  exact ⟨a, Subring.closure_mono (by exact_mod_cast h) ha, b,
    Subring.closure_mono (by exact_mod_cast h) hb, hbu, hx⟩

/-- `𝔭_s = 𝔪_R ∩ C_s`, the contraction of the maximal ideal. -/
def basePrime [IsLocalRing R] (s : Finset R) : Ideal (coeffSubring s) :=
  (IsLocalRing.maximalIdeal R).comap (coeffSubring s).subtype

instance basePrime_isPrime [IsLocalRing R] (s : Finset R) : (basePrime s).IsPrime := by
  unfold basePrime
  infer_instance

/-- Because `R` is LOCAL, `b ∈ C_s` avoids `𝔭_s` exactly when it is a unit of
`R`.  This is the one place locality of `R` is used, and it is what makes the
fraction set above a localization rather than merely a subring. -/
theorem mem_basePrime_primeCompl [IsLocalRing R] {s : Finset R} {b : coeffSubring s} :
    b ∈ (basePrime s).primeCompl ↔ IsUnit (b : R) := by
  simp [Ideal.primeCompl, basePrime]

/-- The inverse of a unit of `C_s` lies in `R_s`: it is `1 / b`. -/
theorem inv_mem_baseSubring {s : Finset R} {b : R} (hb : b ∈ coeffSubring s) (hbu : IsUnit b) :
    (↑hbu.unit⁻¹ : R) ∈ baseSubring s :=
  ⟨1, one_mem _, b, hb, hbu, hbu.val_inv_mul⟩

/-- `R_s` is a `C_s`-algebra, via the inclusion. -/
instance baseAlgebra (s : Finset R) : Algebra (coeffSubring s) (baseSubring s) :=
  (Subring.inclusion (coeffSubring_le_baseSubring s)).toAlgebra

theorem baseAlgebraMap_coe (s : Finset R) (y : coeffSubring s) :
    ((algebraMap (coeffSubring s) (baseSubring s) y : baseSubring s) : R) = (y : R) := rfl

/-- **`R_s` IS THE LOCALIZATION `(C_s)_{𝔭_s}`.**  `map_units` is
`inv_mem_baseSubring`, `surj` is the defining membership of `R_s`, and
`exists_of_eq` is the injectivity of `C_s ↪ R`. -/
instance isLocalization_baseSubring [IsLocalRing R] (s : Finset R) :
    IsLocalization (basePrime s).primeCompl (baseSubring s) := by
  rw [isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hyu : IsUnit ((y : coeffSubring s) : R) := mem_basePrime_primeCompl.mp y.2
    have key : algebraMap (coeffSubring s) (baseSubring s) y *
        (⟨(↑hyu.unit⁻¹ : R), inv_mem_baseSubring (y : coeffSubring s).2 hyu⟩ :
          baseSubring s) = 1 := by
      ext
      show ((y : coeffSubring s) : R) * (↑hyu.unit⁻¹ : R) = 1
      exact hyu.mul_val_inv
    exact IsUnit.of_mul_eq_one _ key
  · obtain ⟨a, ha, b, hb, hbu, hz⟩ := z.2
    refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, mem_basePrime_primeCompl.mpr hbu⟩), ?_⟩
    ext
    exact hz
  · refine ⟨1, ?_⟩
    have hR : ((x : coeffSubring s) : R) = ((y : coeffSubring s) : R) := by
      rw [← baseAlgebraMap_coe s x, ← baseAlgebraMap_coe s y, hxy]
    rw [Subtype.ext hR]

/-- `R_s` is Noetherian: a localization of the Noetherian ring `C_s`. -/
instance isNoetherianRing_baseSubring [IsLocalRing R] (s : Finset R) :
    IsNoetherianRing (baseSubring s) :=
  IsLocalization.isNoetherianRing (basePrime s).primeCompl _
    (is_noetherian_subring_closure _ s.finite_toSet)

/-- `R_s` is local: a localization at a prime. -/
theorem isLocalRing_baseSubring [IsLocalRing R] (s : Finset R) : IsLocalRing (baseSubring s) :=
  IsLocalization.AtPrime.isLocalRing _ (basePrime s)

/-- `R_s → R` is a LOCAL homomorphism: if `x = a / b` is a unit of `R` then so is
`a`, and `b / a ∈ R_s` inverts `x` inside `R_s`. -/
instance isLocalHom_baseSubring_subtype (s : Finset R) :
    IsLocalHom (baseSubring s).subtype := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, hbu, hxb⟩ := x.2
  have hau : IsUnit a := hxb ▸ hx.mul hbu
  have hmem : (b : R) * (↑hau.unit⁻¹ : R) ∈ baseSubring s :=
    ⟨b, hb, a, ha, hau, by rw [mul_assoc, hau.val_inv_mul, mul_one]⟩
  have key : x * (⟨(b : R) * (↑hau.unit⁻¹ : R), hmem⟩ : baseSubring s) = 1 := by
    ext
    show (x : R) * ((b : R) * (↑hau.unit⁻¹ : R)) = 1
    rw [← mul_assoc, hxb, hau.mul_val_inv]
  exact IsUnit.of_mul_eq_one _ key

/-- The transitions `R_s → R_t` are local, since `R_t → R` and `R_s → R` are. -/
instance isLocalHom_baseSubring_inclusion {s t : Finset R} (h : s ⊆ t) :
    IsLocalHom (Subring.inclusion (baseSubring_mono h)) := by
  refine ⟨fun x hx => ?_⟩
  have h1 : IsUnit (((Subring.inclusion (baseSubring_mono h)) x : baseSubring t) : R) :=
    hx.map (baseSubring t).subtype
  rw [Subring.coe_inclusion] at h1
  exact (isLocalHom_baseSubring_subtype s).1 x h1

/-- Every `x : R` already lies in `R_{x}`, which is `base_surj`. -/
theorem mem_baseSubring_singleton (x : R) : x ∈ baseSubring ({x} : Finset R) :=
  coeffSubring_le_baseSubring _ (Subring.subset_closure (by simp))

/-- The stage `R_s` as an object of `CommRingCat`.  See the section note for why
the six facts below are stated at this level and not at `Subring` level. -/
def baseStage (s : Finset R) : CommRingCat.{u} := CommRingCat.of (baseSubring s)

/-- The transition map `R_s → R_t`. -/
def baseStageT {s t : Finset R} (h : s ⊆ t) : baseStage s →+* baseStage t :=
  Subring.inclusion (baseSubring_mono h)

/-- The cocone map `R_s → R`. -/
def baseStageToR (s : Finset R) : baseStage s →+* R := (baseSubring s).subtype

theorem isLocalRing_baseStage [IsLocalRing R] (s : Finset R) : IsLocalRing (baseStage s) :=
  isLocalRing_baseSubring s

theorem isNoetherianRing_baseStage [IsLocalRing R] (s : Finset R) :
    IsNoetherianRing (baseStage s) :=
  isNoetherianRing_baseSubring s

theorem baseStageToR_baseStageT {s t : Finset R} (h : s ⊆ t) (x : baseStage s) :
    baseStageToR t (baseStageT h x) = baseStageToR s x :=
  Subring.coe_inclusion (baseSubring_mono h) x

theorem baseStageToR_injective (s : Finset R) : Function.Injective (baseStageToR s) :=
  fun _ _ h => Subtype.ext h

theorem baseStageT_comp {s t k : Finset R} (h₁ : s ⊆ t) (h₂ : t ⊆ k) :
    (baseStageT h₂).comp (baseStageT h₁) = baseStageT (Finset.Subset.trans h₁ h₂) :=
  RingHom.ext fun x => baseStageToR_injective k (by
    rw [RingHom.comp_apply, baseStageToR_baseStageT, baseStageToR_baseStageT,
      baseStageToR_baseStageT])

theorem comm_baseStageToR {s t : Finset R} (h : s ⊆ t) :
    (baseStageToR t).comp (baseStageT h) = baseStageToR s :=
  RingHom.ext fun x => baseStageToR_baseStageT h x

theorem isLocalHom_baseStageT {s t : Finset R} (h : s ⊆ t) : IsLocalHom (baseStageT h) :=
  isLocalHom_baseSubring_inclusion h

theorem isLocalHom_baseStageToR (s : Finset R) : IsLocalHom (baseStageToR s) :=
  isLocalHom_baseSubring_subtype s

omit [CommRing R] in
theorem baseStage_directed (s t : Finset R) : ∃ k : Finset R, s ⊆ k ∧ t ⊆ k := by
  classical
  exact ⟨s ∪ t, Finset.subset_union_left, Finset.subset_union_right⟩

theorem baseStage_surj (x : R) :
    ∃ s : Finset R, ∃ y : baseStage s, baseStageToR s y = x :=
  ⟨{x}, ⟨x, mem_baseSubring_singleton x⟩, rfl⟩

theorem baseStage_sep (s : Finset R) (x y : baseStage s)
    (hxy : baseStageToR s x = baseStageToR s y) :
    ∃ t : Finset R, ∃ h : s ⊆ t, baseStageT h x = baseStageT h y :=
  ⟨s, Finset.Subset.refl s, congrArg _ (baseStageToR_injective s hxy)⟩

end Construction

end NoetherianApproxBase

/-- **THE `R_λ` TOWER OF 10.127.11 EXISTS** (PROVEN 2026-07-28; read the section
note "THE `R_λ` TOWER, CUT OFF AND PROVEN" above).

*Every local ring is the filtered colimit of a directed system of NOETHERIAN
local subrings, along local inclusions.*

`Λ = Finset R`, `Base s = R_s` the ring of fractions `a / b` with `a, b` in the
subring generated by `s` and `b` a unit of `R`; the transition maps and the
cocone maps are all inclusions of subrings of `R`.  The construction and its six
ingredients are in `NoetherianApproxBase` above.

This is 10.127.11's opening, and it is the half of
`nonempty_noetherianApproxSystem_of_essFinitePresentation` that needs no finite
presentation at all — note that neither `B`, nor `A`, nor either
`EssFinitePresentation` hypothesis appears here. -/
theorem nonempty_noetherianLocalBaseSystem (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (NoetherianLocalBaseSystem R) :=
  ⟨{ Λ := Finset R
     nonemptyΛ := ⟨∅⟩
     le := fun s t => s ⊆ t
     le_rfl := Finset.Subset.refl
     le_trans' := Finset.Subset.trans
     directed := NoetherianApproxBase.baseStage_directed
     Base := NoetherianApproxBase.baseStage
     isLocalRingBase := NoetherianApproxBase.isLocalRing_baseStage
     isNoetherianBase := NoetherianApproxBase.isNoetherianRing_baseStage
     baseT := NoetherianApproxBase.baseStageT
     baseToR := NoetherianApproxBase.baseStageToR
     baseT_comp := NoetherianApproxBase.baseStageT_comp
     comm_baseToR := NoetherianApproxBase.comm_baseStageToR
     isLocalHomBaseT := NoetherianApproxBase.isLocalHom_baseStageT
     isLocalHomBaseToR := NoetherianApproxBase.isLocalHom_baseStageToR
     base_surj := NoetherianApproxBase.baseStage_surj
     base_sep := NoetherianApproxBase.baseStage_sep }⟩

/-! ### 10.127.13 IS 10.127.11 APPLIED TWICE — the one-rung abstraction, 2026-07-28

**SECTION NOTE for `NoetherianLocalExtSystem` and the six declarations under it.**

`nonempty_noetherianApproxSystem_of_baseSystem`'s own docstring says what 10.127.13
is: "10.127.11 applied twice, once to `R → S` and once to `R → S'`, on a common
index set".  Until now that sentence was prose inside a single opaque leaf; the
block below makes it the actual shape of the Lean proof, in exactly the way the
section note "10.128.3 IS ONE LEMMA APPLIED TWICE" below does for the flatness
half.  Nothing here is new mathematics — it is the bookkeeping that lets the ONE
piece of real content be stated once and consumed twice.

**THE ONE RUNG.**  `NoetherianLocalExtSystem bs g` is, field for field, the `Mid`
half of `NoetherianApproxSystem` stated RELATIVE to a given base tower `bs` for
`R`: the tower `S_λ`, its Noetherianity and locality, `R_λ → S_λ` and its
naturality, the cocone `S_λ → S` with the two colimit conditions, and
`isLocalizationMidT`.  The seam is the same one that produced
`NoetherianLocalBaseSystem`, taken one level up.

**WHY IT COMPOSES: `toBaseSystem`.**  The `Mid` tower of a rung is again a base
system — for `B` this time (`NoetherianLocalExtSystem.toBaseSystem`, a pure
renaming: `Base := Mid`, `baseT := midT`, `baseToR := midToB`).  So a second rung
can be built ON TOP of the first, and its `Base` tower is LITERALLY the first
rung's `Mid` tower rather than some other tower for `B` that would then have to be
compared.  That identification is what makes the three-tower assembly below a
matter of naming fields, and it is why the rung is stated relative to a base
system instead of carrying its own index set: two independently-constructed towers
for `B` could not be glued at all.

**WHY THE INDEX SET SHRINKS: `restrict`.**  A rung cannot exist over ALL of `bs`.
A model `S_λ = (R_λ[x]/(f_λ))_{𝔮_λ}` needs `R_λ` to contain the coefficients of a
fixed finite presentation of `B` over `R`, which holds only from some `i₀` on — so
`exists_noetherianLocalExtSystem_of_essFinitePresentation` delivers `i₀` and a rung
over `bs.restrict i₀`, precisely the "take `i₀` large enough, then work over the
RESTRICTED system" step that the leaf's docstring already prescribed.
`NoetherianLocalBaseSystem.restrict` (PROVEN) is that restriction, and
`NoetherianLocalExtSystem.restrict` (PROVEN) carries the FIRST rung down to the
index set the SECOND one lives on, which is the only reindexing the assembly needs.

**THE THIRD LEAF, AND WHY IT IS NOT AVOIDABLE HERE** (**that leaf is now PROVEN**,
2026-07-30).  The second rung is built for `v : B →+* A` over the first rung's
tower, so it needs `EssFinitePresentation v` — and the hypotheses of 00R7 give
`EssFinitePresentation (v.comp g)` and `EssFinitePresentation g` instead.  Deducing
the first from the other two is `essFinitePresentation_of_essFinitePresentation_comp`,
the essential analogue of [Stacks 00F4].  It is a statement about ring maps alone,
with no towers in it.  Rebuilding the second rung from scratch against the composite
hypothesis — the alternative — would duplicate the whole of 10.127.11 and is
strictly more work.

Worth recording, because the cut's own route audit got this wrong: the proof does
**not** go through mathlib's `RingHom.FinitePresentation.of_comp_finiteType`, and
needs only the finite GENERATING set of `T_B`, never its relations.  See that
lemma's docstring for the route that replaced the planned one.

**AXIS SEARCHED.**  Ways to cut the leaf so that the 10.127.11 construction is
written ONCE.  NOT searched: whether the construction itself decomposes further
(it does — the `HasCoeffs` model and the localization at the contracted prime are
visibly separable, and the SURVEY in the construction leaf's docstring says where
to start).  Also NOT searched: whether `restrict` can be avoided by making the rung
carry its own cofinal index map; that is a strictly more general datum and nothing
here would consume the extra generality.

**THE CHECK THAT WOULD REFUTE THIS CUT.**  Exhibit a base system `bs` for `R` and
an essentially-finitely-presented local `g : R →+* B` for which no `i₀` admits a
rung over `bs.restrict i₀`, under 00R7's hypotheses.  That is exactly a
counterexample to 10.127.11, since `bs.restrict i₀` is again a base system and the
rung's fields are 10.127.11's conclusions for `R → S` verbatim. -/

/-- **RESTRICTION OF A BASE TOWER TO A COFINAL PIECE** (PROVEN).  `{i | i₀ ≤ i}`
is again a filtered system of Noetherian local rings with colimit `R`.

This is the step that the approximation leaf's docstring names in as many words —
"take `i₀ : _bs.Λ` large enough … and then work over the RESTRICTED system
`{i | _bs.le i₀ i}`, which is again a base system".  Cofinality is what keeps the
two colimit conditions: `base_surj` composes `bs.base_surj` with one use of
`bs.directed` to push the witness above `i₀`, and `base_sep` needs nothing at all,
because the `j` that `bs.base_sep` returns is automatically `≥ i₀`. -/
def NoetherianLocalBaseSystem.restrict {R : Type u} [CommRing R]
    (bs : NoetherianLocalBaseSystem R) (i₀ : bs.Λ) : NoetherianLocalBaseSystem R where
  Λ := {i : bs.Λ // bs.le i₀ i}
  nonemptyΛ := ⟨⟨i₀, bs.le_rfl i₀⟩⟩
  le := fun i j => bs.le i.1 j.1
  le_rfl := fun i => bs.le_rfl i.1
  le_trans' := fun h₁ h₂ => bs.le_trans' h₁ h₂
  directed := fun i j => by
    obtain ⟨k, hk1, hk2⟩ := bs.directed i.1 j.1
    exact ⟨⟨k, bs.le_trans' i.2 hk1⟩, hk1, hk2⟩
  Base := fun i => bs.Base i.1
  isLocalRingBase := fun i => bs.isLocalRingBase i.1
  isNoetherianBase := fun i => bs.isNoetherianBase i.1
  baseT := fun h => bs.baseT h
  baseToR := fun i => bs.baseToR i.1
  baseT_comp := fun h₁ h₂ => bs.baseT_comp h₁ h₂
  comm_baseToR := fun h => bs.comm_baseToR h
  isLocalHomBaseT := fun h => bs.isLocalHomBaseT h
  isLocalHomBaseToR := fun i => bs.isLocalHomBaseToR i.1
  base_surj := fun x => by
    obtain ⟨i, y, hy⟩ := bs.base_surj x
    obtain ⟨k, hik, hi₀k⟩ := bs.directed i i₀
    exact ⟨⟨k, hi₀k⟩, bs.baseT hik y, by
      rw [← hy]; exact DFunLike.congr_fun (bs.comm_baseToR hik) y⟩
  base_sep := fun i x y hxy => by
    obtain ⟨j, h, hj⟩ := bs.base_sep i.1 x y hxy
    exact ⟨⟨j, bs.le_trans' i.2 h⟩, h, hj⟩

/-- **ONE RUNG OF 10.127.11**: over a GIVEN base tower `bs` for `R`, a tower of
Noetherian local stages for a local `g : R →+* B`, with the transition maps
localizations after base change.

Field for field this is the `Mid` half of `NoetherianApproxSystem` — `Mid`,
`isLocalRingMid`, `isNoetherianMid`, `baseToMid`, `isLocalHomBaseToMid`, `midT`,
`midT_comp`, `comm_baseT`, `midToB`, `comm_baseMid`, `comm_midToB`,
`isLocalHomMidT`, `isLocalHomMidToB`, `mid_surj`, `mid_sep`,
`isLocalizationMidT` — with the `Base` half replaced by the parameter `bs`.  Read
the section note above for what it is for.

**FAITHFULNESS.**  Every field is one of `NoetherianApproxSystem`'s with `Base`
read off `bs`, so a rung is no stronger than what 10.127.11 produces for `R → S`,
and `nonempty_noetherianApproxSystem_of_baseSystem` below is true if 10.127.11 is.
**NON-DEGENERACY**: `Mid = Base` (with `baseToMid = id`, `midToB = g ∘ baseToR`)
satisfies every structural field and fails `mid_surj` as soon as `g` is not
surjective, so the datum is not free; and it cannot be made free by shrinking `Λ`,
since `bs`'s own `Λ` is what indexes it. -/
structure NoetherianLocalExtSystem {R B : Type u} [CommRing R] [CommRing B]
    (bs : NoetherianLocalBaseSystem R) (g : R →+* B) where
  /-- `S_λ`, the stage of `S = B`. -/
  Mid : bs.Λ → CommRingCat.{u}
  /-- Each `S_λ` is local. -/
  isLocalRingMid : ∀ i, IsLocalRing (Mid i)
  /-- Each `S_λ` is Noetherian. -/
  isNoetherianMid : ∀ i, IsNoetherianRing (Mid i)
  /-- `R_λ → S_λ`. -/
  baseToMid : ∀ i, bs.Base i →+* Mid i
  /-- `R_λ → S_λ` is local. -/
  isLocalHomBaseToMid : ∀ i, IsLocalHom (baseToMid i)
  /-- The transition map `S_λ → S_μ`. -/
  midT : ∀ {i j}, bs.le i j → (Mid i →+* Mid j)
  /-- `midT` is functorial. -/
  midT_comp : ∀ {i j k} (h₁ : bs.le i j) (h₂ : bs.le j k),
    (midT h₂).comp (midT h₁) = midT (bs.le_trans' h₁ h₂)
  /-- The vertical maps are natural in `Λ`. -/
  comm_baseT : ∀ {i j} (h : bs.le i j),
    (baseToMid j).comp (bs.baseT h) = (midT h).comp (baseToMid i)
  /-- The cocone map `S_λ → S`. -/
  midToB : ∀ i, Mid i →+* B
  /-- The square `R_λ → S_λ → S` / `R_λ → R → S` commutes. -/
  comm_baseMid : ∀ i, (midToB i).comp (baseToMid i) = g.comp (bs.baseToR i)
  /-- `midToB` is a cocone. -/
  comm_midToB : ∀ {i j} (h : bs.le i j), (midToB j).comp (midT h) = midToB i
  /-- The transitions are local. -/
  isLocalHomMidT : ∀ {i j} (h : bs.le i j), IsLocalHom (midT h)
  /-- The cocone maps are local. -/
  isLocalHomMidToB : ∀ i, IsLocalHom (midToB i)
  /-- `B` is the colimit, half one. -/
  mid_surj : ∀ x : B, ∃ i, ∃ y : Mid i, midToB i y = x
  /-- `B` is the colimit, half two. -/
  mid_sep : ∀ i (x y : Mid i), midToB i x = midToB i y →
    ∃ j, ∃ h : bs.le i j, midT h x = midT h y
  /-- **10.127.13(5)**: `S_μ` is a localization of `R_μ ⊗_{R_λ} S_λ`. -/
  isLocalizationMidT : ∀ {i j} (h : bs.le i j),
    letI : Algebra (bs.Base i) (Mid i) := (baseToMid i).toAlgebra
    letI : Algebra (bs.Base i) (bs.Base j) := (bs.baseT h).toAlgebra
    letI : Algebra (bs.Base i) (Mid j) := ((baseToMid j).comp (bs.baseT h)).toAlgebra
    letI : Algebra (bs.Base j) (Mid j) := (baseToMid j).toAlgebra
    letI : Algebra (Mid i) (Mid j) := (midT h).toAlgebra
    haveI : IsScalarTower (bs.Base i) (bs.Base j) (Mid j) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (bs.Base i) (Mid i) (Mid j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm_baseT h) x
    letI : Algebra (bs.Base j ⊗[bs.Base i] Mid i) (Mid j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (bs.Base i) (bs.Base j) (Mid j))
        (IsScalarTower.toAlgHom (bs.Base i) (Mid i) (Mid j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (bs.Base j ⊗[bs.Base i] Mid i), IsLocalization W (Mid j)

/-- **A RUNG'S `Mid` TOWER IS ITSELF A BASE TOWER, FOR `B`** (PROVEN) — the
declaration that makes "10.127.11 applied twice" composable.

Pure renaming: `Base := Mid`, `baseT := midT`, `baseToR := midToB`, and the nine
remaining fields are the identically-named ones of the rung.  The index set and
its order are `bs`'s unchanged, which is the point: the second rung's stages are
indexed by the SAME `Λ` as the first rung's, so `Mid i → Tot i` is a map at one
index and not a comparison between two unrelated towers. -/
def NoetherianLocalExtSystem.toBaseSystem {R B : Type u} [CommRing R] [CommRing B]
    {bs : NoetherianLocalBaseSystem R} {g : R →+* B} (e : NoetherianLocalExtSystem bs g) :
    NoetherianLocalBaseSystem B where
  Λ := bs.Λ
  nonemptyΛ := bs.nonemptyΛ
  le := bs.le
  le_rfl := bs.le_rfl
  le_trans' := bs.le_trans'
  directed := bs.directed
  Base := e.Mid
  isLocalRingBase := e.isLocalRingMid
  isNoetherianBase := e.isNoetherianMid
  baseT := e.midT
  baseToR := e.midToB
  baseT_comp := e.midT_comp
  comm_baseToR := e.comm_midToB
  isLocalHomBaseT := e.isLocalHomMidT
  isLocalHomBaseToR := e.isLocalHomMidToB
  base_surj := e.mid_surj
  base_sep := e.mid_sep

/-- **A RUNG RESTRICTS ALONG `NoetherianLocalBaseSystem.restrict`** (PROVEN).

The assembly below builds its first rung over `bs.restrict i₀` and its second over
a further restriction above `j₀`; this carries the FIRST rung down to that smaller
index set so that both rungs and the base tower are indexed by one type.  As in
`NoetherianLocalBaseSystem.restrict`, only `mid_surj` does any work (one use of
`bs.directed` to push a witness above `i₀`). -/
def NoetherianLocalExtSystem.restrict {R B : Type u} [CommRing R] [CommRing B]
    {bs : NoetherianLocalBaseSystem R} {g : R →+* B} (e : NoetherianLocalExtSystem bs g)
    (i₀ : bs.Λ) : NoetherianLocalExtSystem (bs.restrict i₀) g where
  Mid := fun i => e.Mid i.1
  isLocalRingMid := fun i => e.isLocalRingMid i.1
  isNoetherianMid := fun i => e.isNoetherianMid i.1
  baseToMid := fun i => e.baseToMid i.1
  isLocalHomBaseToMid := fun i => e.isLocalHomBaseToMid i.1
  midT := fun h => e.midT h
  midT_comp := fun h₁ h₂ => e.midT_comp h₁ h₂
  comm_baseT := fun h => e.comm_baseT h
  midToB := fun i => e.midToB i.1
  comm_baseMid := fun i => e.comm_baseMid i.1
  comm_midToB := fun h => e.comm_midToB h
  isLocalHomMidT := fun h => e.isLocalHomMidT h
  isLocalHomMidToB := fun i => e.isLocalHomMidToB i.1
  mid_surj := fun x => by
    obtain ⟨i, y, hy⟩ := e.mid_surj x
    obtain ⟨k, hik, hi₀k⟩ := bs.directed i i₀
    exact ⟨⟨k, hi₀k⟩, e.midT hik y, by
      rw [← hy]; exact DFunLike.congr_fun (e.comm_midToB hik) y⟩
  mid_sep := fun i x y hxy => by
    obtain ⟨j, h, hj⟩ := e.mid_sep i.1 x y hxy
    exact ⟨⟨j, bs.le_trans' i.2 h⟩, h, hj⟩
  isLocalizationMidT := fun h => e.isLocalizationMidT h

/-! #### THE TWO PRESENTATION-BOOKKEEPING LEMMAS, HOISTED HERE 2026-07-30

Both were written on 2026-07-27 for 05UV's finite-generation half and stood ~3000
lines below.  `essFinitePresentation_of_essFinitePresentation_comp` (immediately
below) turned out to be provable over exactly these two, so they are hoisted to
here — VERBATIM, same names, same signatures, same proofs — and notes are left at
both old sites.  Nothing else moved and no call site changed. -/

/-- **A finitely presented ring map followed by a localization is essentially
of finite presentation.**  This is `EssFinitePresentation` read off its own
definition, with the one piece of friction the definition creates handled
once and for all: the definition demands
`@IsLocalization T _ M S _ v.toAlgebra`, i.e. the localization statement for
the algebra structure *built from* `v`, whereas at a use site the ambient
`Algebra T S` instance is the one in scope.  The two are equal by
`Algebra.algebra_ext` (their `algebraMap`s are literally the same function),
and every construction of an `EssFinitePresentation` below goes through this
lemma rather than repeating that transport. -/
theorem essFinitePresentation_of_isLocalization {R T S : Type u} [CommRing R] [CommRing T]
    [CommRing S] [Algebra T S] (M : Submonoid T) [IsLocalization M S]
    {g : R →+* T} (hg : g.FinitePresentation) :
    EssFinitePresentation ((algebraMap T S).comp g) := by
  refine ⟨T, ‹_›, g, algebraMap T S, M, hg, rfl, ?_⟩
  have h : (algebraMap T S).toAlgebra = ‹Algebra T S› :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  rw [h]
  infer_instance

/-- **A quotient of an essentially-of-finite-presentation map by a FINITELY
GENERATED kernel is again essentially of finite presentation** (PROVEN
2026-07-27).  This is the second half of 05UV's presentation bookkeeping: it
is what converts "`J` is finitely generated" into the conclusion "`S` is
essentially of finite presentation over `R`".

**The proof, and the one step that needs care.**  Write the hypothesis as
`P = M⁻¹T` with `R → T` finitely presented.  A finite generating set of
`ker w` lives in the LOCALIZATION, so its members must have their denominators
cleared: `IsLocalization.surj` writes each generator as `vT a / vT m`, and
because `vT m` is a unit the ideal `J ⊆ T` spanned by the numerators satisfies
`J·P = ker w` exactly.  Then `T ⧸ J` is finitely presented over `R`
(`RingHom.FinitePresentation.comp_surjective`) and `B` is its localization at
the image of `M` — which is precisely mathlib's
`IsLocalization.of_surjective`, applied to the square
`T → P`, `T ⧸ J → B`.

Note this is NOT an instance of a general "`EssFinitePresentation` is stable
under composition" lemma, which is the one closure property this development
deliberately does not prove (see `essFinitePresentation_stalkMap`): the
surjection here is by a finitely generated ideal, which is exactly the
hypothesis that makes the denominators clearable. -/
theorem essFinitePresentation_comp_of_fg_ker {R P B : Type u}
    [CommRing R] [CommRing P] [CommRing B]
    {gP : R →+* P} {w : P →+* B} (hfpP : EssFinitePresentation gP)
    (hw : Function.Surjective w) (hker : (RingHom.ker w).FG) :
    EssFinitePresentation (w.comp gP) := by
  obtain ⟨T, _, gT, vT, M, hgT, hvT, hloc⟩ := hfpP
  letI : Algebra T P := vT.toAlgebra
  haveI : IsLocalization M P := hloc
  have halg : ∀ t : T, algebraMap T P t = vT t := fun _ => rfl
  obtain ⟨s, hs⟩ := hker
  -- clear denominators in the chosen generators of `ker w`
  set num : P → T := fun x => (IsLocalization.surj M x).choose.1 with hnum
  set den : P → M := fun x => (IsLocalization.surj M x).choose.2 with hden
  have hspec : ∀ x : P, x * algebraMap T P (den x) = algebraMap T P (num x) :=
    fun x => (IsLocalization.surj M x).choose_spec
  classical
  set J : Ideal T := Ideal.span (s.image num : Finset T) with hJ
  have hJmap : J.map vT = RingHom.ker w := by
    apply le_antisymm
    · rw [hJ, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ht, rfl⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      have hxk : x ∈ RingHom.ker w := by rw [← hs]; exact Ideal.subset_span hx
      rw [SetLike.mem_coe, ← halg, ← hspec x]
      exact Ideal.mul_mem_right _ _ hxk
    · rw [← hs, Ideal.span_le]
      intro x hx
      have hu : IsUnit (algebraMap T P (den x)) := IsLocalization.map_units P (den x)
      obtain ⟨u, hu'⟩ := hu
      have : x = vT (num x) * (↑u⁻¹ : P) := by
        rw [← halg, ← hspec x, ← hu', mul_assoc]
        simp
      rw [SetLike.mem_coe, this]
      refine Ideal.mul_mem_right _ _ ?_
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨x, hx, rfl⟩))
  -- the quotient presentation
  have hJle : J ≤ RingHom.ker (w.comp vT) := by
    intro t ht
    have : vT t ∈ RingHom.ker w := by rw [← hJmap]; exact Ideal.mem_map_of_mem _ ht
    simpa [RingHom.mem_ker] using this
  set v' : (T ⧸ J) →+* B := Ideal.Quotient.lift J (w.comp vT) (fun a ha => hJle ha) with hv'
  have hv'mk : v'.comp (Ideal.Quotient.mk J) = w.comp vT := by
    ext t; simp [hv']
  letI : Algebra (T ⧸ J) B := v'.toAlgebra
  have halg' : ∀ t : T ⧸ J, algebraMap (T ⧸ J) B t = v' t := fun _ => rfl
  refine ⟨T ⧸ J, inferInstance, (Ideal.Quotient.mk J).comp gT, v',
    M.map (Ideal.Quotient.mk J), ?_, ?_, ?_⟩
  · exact hgT.comp_surjective Ideal.Quotient.mk_surjective ⟨s.image num, by rw [← hJ]; simp [hJ]⟩
  · rw [← RingHom.comp_assoc, hv'mk, RingHom.comp_assoc, hvT]
  · refine IsLocalization.of_surjective M P (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      w hw ?_ ?_
    · ext t; simp [halg, halg', hv']
    · rw [Ideal.mk_ker, ← hJmap]
      exact le_of_eq rfl

/-- **CANCELLATION FOR `EssFinitePresentation`: the essential analogue of
[Stacks 00F4]** (**PROVEN 2026-07-30**; cut 2026-07-28 out of
`nonempty_noetherianApproxSystem_of_baseSystem`).

*If `R → A` is essentially of finite presentation and so is `R → B`, then
`B → A` is essentially of finite presentation.*

**WHY IT IS NEEDED.**  The assembly builds the `S'_λ` tower as a rung over the
`S_λ` tower, i.e. for `v : B →+* A`, and 00R7 hands it `EssFinitePresentation` for
`v.comp g` and for `g` instead.  There is no way round this that does not rebuild
10.127.11 a second time; see the section note above.

**THE NON-ESSENTIAL CASE IS IN THE PIN, AND IS THE ENGINE.**
`RingHom.FinitePresentation.of_comp_finiteType` (in
`Mathlib/RingTheory/FinitePresentation.lean`, verified present 2026-07-28) is
exactly [Stacks 00F4]: `(g.comp f).FinitePresentation → f.FiniteType →
g.FinitePresentation`.  What this leaf adds is the passage through the two
localizations.

**THE ROUTE ACTUALLY TAKEN (2026-07-30), which is NOT the one the cut planned.**
Unfold both hypotheses: `A = M_A⁻¹T_A` with `R →+* T_A` of finite presentation,
and `B = M_B⁻¹T_B` with `R →+* T_B` of finite presentation.  Then put

  `P := B ⊗_R T_A`,   `L := W⁻¹P` for `W` the image of `M_A` in `P`,

and everything is bookkeeping over the two presentation lemmas already in this
file.  `B → P` is of finite presentation by base change
(`Algebra.FinitePresentation.baseChange`), so `B → L` is essentially of finite
presentation by `essFinitePresentation_of_isLocalization` — note that `L` is
introduced as `Localization W`, so *no* "localization commutes with base change"
lemma is needed and `L ≅ B ⊗_R A` is never proved.  Then `L ↠ A` with a
FINITELY GENERATED kernel, and `essFinitePresentation_comp_of_fg_ker` finishes.

The two maps that make the kernel computable are the ones the naive
`B ⊗_R T_A → A` does not have:

* `μ : L →+* A`, from `Algebra.TensorProduct.lift` of `v` and `T_A → A`, then
  `IsLocalization.lift` (the image of `M_A` is already invertible in `A`);
* `τ : A →+* L`, from `IsLocalization.lift` applied to `T_A → P → L` (the image
  of `M_A` is invertible in `L` by construction of `W`).  `τ` is a SECTION of
  `μ`, which is what makes `μ` surjective and drives the kernel computation.

*The kernel.*  With `α b := ι(b ⊗ 1)` and `β b := τ(v b)` — both ring maps
`B → L` — the kernel of `μ` is generated by `{α b - β b : b ∈ B}`, and that set
is generated by the finitely many `b = vB y_k` for `y_1, …, y_n` a finite
`R`-algebra generating set of `T_B`.  Two observations do it:

1. `{b | α b = β b in L/K}` is an `R`-subalgebra of `B` (both `α` and `β` are
   ring maps, and they AGREE on the image of `R` because `g r ⊗ 1` and
   `1 ⊗ gA r` are both `algebraMap R P r`).  It contains `vB(T_B)` by
   `Algebra.adjoin_induction`, and then all of `B`: every `b` satisfies
   `b · vB m = vB t`, and `α (vB m)` is a UNIT, so `α b = β b` by cancellation.
   **This is where `hB` is spent, and it is the only place.**
2. `x ↦ q x` and `x ↦ q (τ (μ x))` are two ring maps `L → L/K`, so
   `IsLocalization.ringHom_ext` reduces their equality to `P`, and
   `Algebra.TensorProduct.ringHom_ext` reduces THAT to the two factors — `B`,
   where it is (1), and `T_A`, where `τ (μ (ι (iR t))) = ι (iR t)` holds on the
   nose.  So `q = q ∘ τ ∘ μ`, and `x ∈ ker μ` gives `q x = q (τ 0) = 0`.

**WHAT THIS AVOIDS, recorded because the cut believed it unavoidable.**  The
route planned at the cut ran through *lifting* `T_B → A` to a localization
`(T_A)_m` — clear the denominators of the images of `y_1, …, y_n`, then kill the
finitely many relations of `T_B` by a further element of `M_A` — and only then
applied `RingHom.FinitePresentation.of_comp_finiteType` (= the non-essential
[Stacks 00F4], in `Mathlib/RingTheory/FinitePresentation.lean`, verified present
2026-07-28) to `R → T_B → (T_A)_m`, followed by base change to `B` and one more
localization.  **That lifting step is the expensive one — it needs the relations
of a finite presentation, not just the generators — and the route above does not
use it, nor `of_comp_finiteType`, at all.**  What replaces both is the pair
`(μ, τ)` above: the section `τ` is what turns "`A` is a quotient of something
finitely presented over `B`" into a statement about an ideal one can generate by
hand.  Only the finite GENERATING set of `T_B` is used, never its relations —
which is why `Algebra.FiniteType` (`RingHom.FiniteType.of_finitePresentation`)
is all that is extracted from `hB`.

**FAITHFULNESS.**  The degenerate corners are TRUE rather than vacuous, so nothing
is hiding in them: `A = 0` is witnessed by `T = B` with `M = B` itself (`0 ∈ M`, and
`M⁻¹B = 0`); `v` bijective by `RingHom.FinitePresentation.of_bijective`; and when
`B` is Noetherian the statement collapses to `EssFiniteType.of_comp` plus
`RingHom.FinitePresentation.of_finiteType`, both in the pin.

**`hB` IS LOAD-BEARING** — the statement is FALSE without it, and the witness is
worth recording because it is the first thing a prover will try to drop.  Take
`R = ℤ`, `B = ℚ[x₁, x₂, x₃, …]` on countably many variables, `A = ℚ`, with
`g : ℤ → B` the structure map and `v : B → ℚ` sending every `xᵢ` to `0`.  Then
`v.comp g : ℤ → ℚ` IS essentially of finite presentation (`ℚ` is the localization
of `ℤ` at `ℤ ∖ {0}`, so take `T = ℤ`), while `ℚ = B ⧸ (x₁, x₂, …)` is a quotient of
`B` by an ideal that is not finitely generated and is a filtered colimit of the
finitely presented `B ⧸ (x₁, …, xₙ)` rather than a localization of any one of them.
`_hB` fails here exactly as it must: `B` is not even of finite type over `ℤ`.
*(This counterexample is asserted, not machine-checked; a prover who needs it
should verify the middle clause before relying on it.  The POSITIVE direction — the
four-step route above — is what this leaf actually asks for.)* -/
theorem essFinitePresentation_of_essFinitePresentation_comp {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A] {g : R →+* B} {v : B →+* A}
    (hA : EssFinitePresentation (v.comp g)) (hB : EssFinitePresentation g) :
    EssFinitePresentation v := by
  classical
  obtain ⟨TA, iTA, gA, vA, MA, hgA, hvA, hlocA⟩ := hA
  obtain ⟨TB, iTB, gB, vB, MB, hgB, hvB, hlocB⟩ := hB
  letI := iTA
  letI := iTB
  letI : Algebra R B := g.toAlgebra
  letI : Algebra R TA := gA.toAlgebra
  letI : Algebra R TB := gB.toAlgebra
  letI : Algebra TA A := vA.toAlgebra
  letI : Algebra TB B := vB.toAlgebra
  haveI : IsLocalization MA A := hlocA
  haveI : IsLocalization MB B := hlocB
  letI : Algebra R A := (v.comp g).toAlgebra
  have hAR : ∀ r : R, algebraMap R A r = v (g r) := fun _ => rfl
  have hBR : ∀ r : R, algebraMap R B r = g r := fun _ => rfl
  have hTBR : ∀ r : R, algebraMap R TB r = gB r := fun _ => rfl
  have hBTB : ∀ t : TB, algebraMap TB B t = vB t := fun _ => rfl
  haveI htowA : IsScalarTower R TA A :=
    IsScalarTower.of_algebraMap_eq fun r => (DFunLike.congr_fun hvA r).symm
  -- ## `P = B ⊗_R T_A`, of finite presentation over `B`
  set iL : B →+* B ⊗[R] TA := Algebra.TensorProduct.includeLeftRingHom with hiL
  set iR : TA →+* B ⊗[R] TA :=
    (Algebra.TensorProduct.includeRight : TA →ₐ[R] B ⊗[R] TA).toRingHom with hiR
  have hiLapp : ∀ b : B, iL b = b ⊗ₜ[R] (1 : TA) := fun _ => rfl
  have hiRapp : ∀ t : TA, iR t = (1 : B) ⊗ₜ[R] t := fun _ => rfl
  haveI : Algebra.FinitePresentation R TA := hgA
  have hfpiL : iL.FinitePresentation := by
    have h : iL.toAlgebra = inferInstanceAs (Algebra B (B ⊗[R] TA)) :=
      Algebra.algebra_ext _ _ (fun _ => rfl)
    show @Algebra.FinitePresentation B (B ⊗[R] TA) _ _ iL.toAlgebra
    rw [h]; infer_instance
  -- ## `L = W⁻¹P`, `W` the image of `M_A`; `B → L` is essentially of finite presentation
  set W : Submonoid (B ⊗[R] TA) := MA.map iR with hW
  set ι : (B ⊗[R] TA) →+* Localization W := algebraMap (B ⊗[R] TA) (Localization W) with hι
  letI : Algebra R (Localization W) := (ι.comp (algebraMap R (B ⊗[R] TA))).toAlgebra
  -- ## `τ : A →+* L`, the section
  have hτunit : ∀ y : MA, IsUnit ((ι.comp iR) y) := by
    intro y
    exact IsLocalization.map_units (M := W) (Localization W) ⟨iR y.1, ⟨y.1, y.2, rfl⟩⟩
  set τ : A →+* Localization W := IsLocalization.lift (M := MA) hτunit with hτ
  have hτeq : ∀ t : TA, τ (algebraMap TA A t) = ι (iR t) :=
    fun t => IsLocalization.lift_eq (M := MA) hτunit t
  -- ## `hh : P →+* A` and `μ : L →+* A`
  set vAlg : B →ₐ[R] A := { v with commutes' := fun _ => rfl } with hvAlg
  set hh : (B ⊗[R] TA) →+* A :=
    (Algebra.TensorProduct.lift vAlg (IsScalarTower.toAlgHom R TA A)
      (fun _ _ => Commute.all _ _)).toRingHom with hhh
  have hhtmul : ∀ (b : B) (t : TA), hh (b ⊗ₜ[R] t) = v b * algebraMap TA A t := by
    intro b t; rfl
  have hhiL : ∀ b : B, hh (iL b) = v b := by
    intro b; rw [hiLapp, hhtmul]; simp
  have hhiR : ∀ t : TA, hh (iR t) = algebraMap TA A t := by
    intro t; rw [hiRapp, hhtmul]; simp
  have hμunit : ∀ y : W, IsUnit (hh y) := by
    rintro ⟨y, m, hm, rfl⟩
    rw [hhiR]
    exact IsLocalization.map_units (M := MA) A ⟨m, hm⟩
  set μ : Localization W →+* A := IsLocalization.lift (M := W) hμunit with hμ
  have hμι : ∀ p : B ⊗[R] TA, μ (ι p) = hh p :=
    fun p => IsLocalization.lift_eq (M := W) hμunit p
  have hμτ : ∀ a : A, μ (τ a) = a := by
    have hcomp : (μ.comp τ) = RingHom.id A := by
      apply IsLocalization.ringHom_ext MA
      ext t
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [hτeq, hμι, hhiR]
    intro a; exact DFunLike.congr_fun hcomp a
  have hμsurj : Function.Surjective μ := fun a => ⟨τ a, hμτ a⟩
  -- ## `K`, generated by `α - β` on a finite `R`-algebra generating set of `T_B`
  haveI : Algebra.FiniteType R TB := RingHom.FiniteType.of_finitePresentation hgB
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType R TB›).out
  set K : Ideal (Localization W) :=
    Ideal.span ((fun t : TB => ι (iL (vB t)) - τ (v (vB t))) '' (s : Set TB)) with hK
  have hKfg : K.FG := Submodule.fg_span (Set.Finite.image _ s.finite_toSet)
  set q : Localization W →+* Localization W ⧸ K := Ideal.Quotient.mk K with hq
  set α : B →+* (Localization W) ⧸ K := q.comp (ι.comp iL) with hα
  set β : B →+* (Localization W) ⧸ K := q.comp (τ.comp v) with hβ
  have hαapp : ∀ b : B, α b = q (ι (iL b)) := fun _ => rfl
  have hβapp : ∀ b : B, β b = q (τ (v b)) := fun _ => rfl
  -- `α` and `β` agree on the image of `R`: `g r ⊗ 1` and `1 ⊗ gA r` are both `algebraMap R P r`
  have hRagree : ∀ r : R, α (g r) = β (g r) := by
    intro r
    have h1 : iL (g r) = algebraMap R (B ⊗[R] TA) r := by
      rw [hiLapp, ← hBR r, Algebra.TensorProduct.algebraMap_apply]
    have h2 : τ (v (g r)) = ι (algebraMap R (B ⊗[R] TA) r) := by
      rw [← hAR r, IsScalarTower.algebraMap_apply R TA A, hτeq, hiRapp,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hαapp, hβapp, h1, h2]
  -- ## `α = β` on `vB (T_B)`, by `adjoin` induction, hence on all of `B`, by unit cancellation
  have hgen : ∀ t : TB, α (vB t) = β (vB t) := by
    intro t
    have ht : t ∈ Algebra.adjoin R (s : Set TB) := hs ▸ Algebra.mem_top
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
        have hmem : ι (iL (vB x)) - τ (v (vB x)) ∈ K := Ideal.subset_span ⟨x, hx, rfl⟩
        rw [hαapp, hβapp, ← sub_eq_zero, ← map_sub]
        exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    | algebraMap r =>
        have h : vB (algebraMap R TB r) = g r := by
          rw [hTBR]; exact DFunLike.congr_fun hvB r
        rw [h]; exact hRagree r
    | add x y _ _ ihx ihy => simp only [map_add, ihx, ihy]
    | mul x y _ _ ihx ihy => simp only [map_mul, ihx, ihy]
  have hall : ∀ b : B, α b = β b := by
    intro b
    obtain ⟨⟨t, m⟩, hbm⟩ := IsLocalization.surj (M := MB) b
    have hbm' : b * vB m.1 = vB t := by rw [← hBTB, ← hBTB]; exact hbm
    have hu : IsUnit (α (vB m.1)) := by
      have hvu : IsUnit (vB m.1) := by
        rw [← hBTB]; exact IsLocalization.map_units (M := MB) B m
      exact hvu.map α
    have h1 : α b * α (vB m.1) = α (vB t) := by rw [← map_mul, hbm']
    have h2 : β b * α (vB m.1) = α (vB t) := by
      rw [hgen m.1, ← map_mul, hbm', hgen t]
    obtain ⟨w, hw⟩ := hu
    have key : α b * (w : (Localization W) ⧸ K) = β b * (w : (Localization W) ⧸ K) := by
      rw [hw]; exact h1.trans h2.symm
    calc α b = α b * (w : (Localization W) ⧸ K) * ((w⁻¹ : ((Localization W) ⧸ K)ˣ) :
                (Localization W) ⧸ K) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
      _ = β b * (w : (Localization W) ⧸ K) * ((w⁻¹ : ((Localization W) ⧸ K)ˣ) :
                (Localization W) ⧸ K) := by rw [key]
      _ = β b := by rw [mul_assoc, Units.mul_inv, mul_one]
  -- ## `q ∘ τ ∘ μ = q`, checked on the two tensor factors
  have hqfix : q.comp (τ.comp μ) = q := by
    apply IsLocalization.ringHom_ext W
    apply Algebra.TensorProduct.ringHom_ext
    · ext b
      simp only [RingHom.comp_apply]
      show q (τ (μ (ι (iL b)))) = q (ι (iL b))
      rw [hμι, hhiL]
      exact (hall b).symm
    · ext t
      simp only [RingHom.comp_apply]
      show q (τ (μ (ι (iR t)))) = q (ι (iR t))
      rw [hμι, hhiR, hτeq]
  -- ## `ker μ = K`, hence finitely generated
  have hker : RingHom.ker μ = K := by
    apply le_antisymm
    · intro x hx
      have hx0 : μ x = 0 := hx
      have hqx : q (τ (μ x)) = q x := DFunLike.congr_fun hqfix x
      rw [hx0, map_zero, map_zero] at hqx
      exact (Ideal.Quotient.eq_zero_iff_mem).1 hqx.symm
    · rw [hK, Ideal.span_le]
      rintro _ ⟨t, _, rfl⟩
      show μ (ι (iL (vB t)) - τ (v (vB t))) = 0
      rw [map_sub, hμι, hhiL, hμτ, sub_self]
  -- ## Assemble
  have hfin : EssFinitePresentation (ι.comp iL) :=
    essFinitePresentation_of_isLocalization W hfpiL
  have hres : EssFinitePresentation (μ.comp (ι.comp iL)) :=
    essFinitePresentation_comp_of_fg_ker hfin hμsurj (hker ▸ hKfg)
  have hvcomp : μ.comp (ι.comp iL) = v := by
    ext b
    simp only [RingHom.comp_apply]
    show μ (ι (iL b)) = v b
    rw [hμι, hhiL]
  rwa [hvcomp] at hres

section IsLocalizationTensorComp

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **TRANSPORT `IsLocalization` ALONG A RING ISOMORPHISM OF THE SOURCE** (PROVEN).

*If `Q` is the localization of `A'` at `V` along `φ`, and `e : A ≃+* A'`, then `Q` is
the localization of `A` at `V.comap e` along `φ.comp e`.*

Stated for BARE ring homomorphisms with `RingHom.toAlgebra` rather than for algebras,
because that is the shape `exists_isLocalization_tensor_comp` below needs: there the
source is replaced by an isomorphic tensor product and no `AlgEquiv` over a common base
ring is available (see step 2 of that proof's docstring).

Nothing deeper than the three `IsLocalization` fields transported one at a time; `e`
being an isomorphism is what makes `surj` and `exists_of_eq` go both ways. -/
theorem isLocalization_comap_of_ringEquiv {A A' Q : Type u} [CommRing A] [CommRing A']
    [CommRing Q] (e : A ≃+* A') (φ : A' →+* Q) (V : Submonoid A')
    (h : letI := φ.toAlgebra; IsLocalization V Q) :
    letI := (φ.comp (e : A →+* A')).toAlgebra
    IsLocalization (V.comap (e : A →+* A')) Q := by
  letI : Algebra A' Q := φ.toAlgebra
  letI : Algebra A Q := (φ.comp (e : A →+* A')).toAlgebra
  have key : ∀ a : A, algebraMap A Q a = algebraMap A' Q (e a) := fun _ => rfl
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · rw [key]
    exact IsLocalization.map_units (M := V) Q ⟨e y.1, y.2⟩
  · obtain ⟨⟨x, v⟩, hx⟩ := IsLocalization.surj (M := V) z
    refine ⟨⟨e.symm x, ⟨e.symm v.1, ?_⟩⟩, ?_⟩
    · simp
    · simpa [key] using hx
  · rw [key, key] at hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := V) hxy
    refine ⟨⟨e.symm c.1, ?_⟩, ?_⟩
    · simp
    · simpa using congrArg e.symm hc

set_option maxHeartbeats 2000000 in
/-- **A LOCALIZATION OF A LOCALIZATION, ACROSS TWO BASE CHANGES** (PROVEN 2026-07-30;
cut 2026-07-28 out of `nonempty_noetherianApproxSystem_of_baseSystem`).

*Given a commuting ladder*
```
  R₀ --a₀--> S₀ --b₀--> T₀
  |          |          |
  f          p          q
  v          v          v
  R₁ --a₁--> S₁ --b₁--> T₁
```
*if `S₁` is a localization of `R₁ ⊗_{R₀} S₀` and `T₁` is a localization of
`S₁ ⊗_{S₀} T₀`, then `T₁` is a localization of `R₁ ⊗_{R₀} T₀`.*

This is `NoetherianApproxSystem`'s `isLocalizationTotBaseT` derived from
`isLocalizationMidT` and `isLocalizationTotT` — the derivation that the structure's
own docstring says is possible ("DERIVABLE from the previous two: a localization
base-changes to a localization, and `S'_λ ⊗_{R_λ} R_μ ≅ S'_λ ⊗_{S_λ} (S_λ ⊗_{R_λ}
R_μ)`") and that had to be carried out somewhere.  Here it is carried out ONCE, at
the level of six bare rings, so the assembly can apply it at every `i ≤ j`.

**THE `letI` BLOCKS ARE NOT DECORATION.**  They are copied verbatim from the three
structure fields, in the same order and built from the same maps, so that the
hypotheses and the conclusion are SYNTACTICALLY the fields at
`R₀ = Base i, R₁ = Base j, S₀ = Mid i, S₁ = Mid j, T₀ = Tot i, T₁ = Tot j` and the
application below needs no transport.  Changing how an `Algebra` instance is
spelled here will break that match even if it stays defeq on paper.

**THE PROOF, IN THREE STEPS.**  Write `P := R₁ ⊗[R₀] S₀`, `A := R₁ ⊗[R₀] T₀`,
`Q := S₁ ⊗[S₀] T₀` and `PT := P ⊗[S₀] T₀`.

1. *Localization commutes with base change.*  This is the only mathematical input, and
   it is one mathlib lemma: `IsLocalization.tensorProduct_tensorProduct`
   (`Mathlib/RingTheory/Localization/BaseChange.lean`) at base `S₀` with `A := P`,
   `B := S₁`, `S := T₀` says `Q` is a localization of `PT` at
   `Algebra.algebraMapSubmonoid PT W₁`.  The lemma takes `Algebra PT Q` as an
   *instance argument* plus a compatibility hypothesis, so the instance is supplied
   here — as `Algebra.TensorProduct.map (IsScalarTower.toAlgHom S₀ P S₁) (AlgHom.id S₀ T₀)`
   — and no diamond can form; the hypothesis is `by ext t; simp`.
   (`IsLocalization.tensor`, which the cut note originally pointed at, is the
   `IsLocalization.Away` special case and is NOT the lemma wanted.)
2. *`A ≃+* PT`.*  Built by hand rather than out of `Algebra.TensorProduct.cancelBaseChange`
   and two `Algebra.TensorProduct.comm`s, because those three equivalences have no common
   base ring here — `cancelBaseChange`'s shape is `X ⊗[S] (S ⊗[R] Y)`, with the base on the
   *inner left*, and `PT` has it on the inner right.  So: the forward map is the
   `R₀`-algebra map `r ⊗ t ↦ (r ⊗ 1) ⊗ t`, the backward map the `S₀`-algebra map
   `(r ⊗ s) ⊗ t ↦ r ⊗ (b₀ s · t)`, and each round trip is one
   `Algebra.TensorProduct.ringHom_ext`.  The only content in the round trips is that `S₀`
   may be slid between the two tensor slots (`hslide`), which is
   `Algebra.TensorProduct.algebraMap_apply` composed with `algebraMap_apply'`.
3. *Transport and compose.*  `isLocalization_comap_of_ringEquiv` above moves step 1 from
   source `PT` to source `A`, and `IsLocalization.localization_localization_isLocalization`
   composes that with `_h₂` at `localizationLocalizationSubmodule`.  The scalar tower
   `A → Q → T₁` it needs is exactly the claim that the goal's own
   `Algebra (R₁ ⊗[R₀] T₀) T₁` instance factors through `Q`, and that is checked on the two
   tensor generators — which is where the "compatibility with the *specific* instance the
   goal names" worry recorded at the cut is discharged.

**THE THREE INSTANCE TRAPS, recorded because each presents as a missing theory and is
not one.**

* The `S₀`-algebra structure on `P` is not global: it is
  `Algebra.TensorProduct.rightAlgebra`, which mathlib deliberately keeps scoped, so the
  whole block sits inside a section under `attribute [local instance]`.
* **Do NOT supply `Algebra P Q` by hand.**  Mathlib's `Algebra.TensorProduct.leftAlgebra`
  already gives it from `Algebra P S₁` and the tower `S₀ → P → S₁`, and its `SMul` *is*
  `TensorProduct.leftHasSMul` — the very instance typeclass search picks for `SMul P Q`.
  A hand-rolled `RingHom.toAlgebra` version has a different, merely extensionally equal,
  `SMul`, and then `IsScalarTower P PT Q` cannot be produced by
  `IsScalarTower.of_algebraMap_eq` at all: the instance arguments do not unify, and the
  error names the SMul instances rather than anything mathematical.
* For the same reason the two towers `IsScalarTower R₀ R₀ PT` and `IsScalarTower S₀ S₀ A`
  that `Algebra.TensorProduct.lift` demands are given as `⟨fun x y z => mul_smul x y z⟩`,
  which adapts to whichever `SMul` search happens to find, rather than through any
  `Algebra`-flavoured constructor.

**FAITHFULNESS.**  The conclusion is one of 10.127.11's own conclusions applied to
`R → S'` and is implied by the two hypotheses, so it cannot be stronger than them;
and it is not vacuous — take every ring equal and every map the identity, and the
witness is `⊤`.  The two commutation hypotheses are load-bearing: without `hsq₁`
the `IsScalarTower R₀ S₀ S₁` needed to form `R₁ ⊗[R₀] S₀ → S₁` does not exist, and
without `hsq₂` the same fails one level up, so neither can be dropped even in
statement. -/
theorem exists_isLocalization_tensor_comp
    {R₀ R₁ S₀ S₁ T₀ T₁ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀] [CommRing S₁]
    [CommRing T₀] [CommRing T₁]
    (f : R₀ →+* R₁) (a₀ : R₀ →+* S₀) (a₁ : R₁ →+* S₁) (p : S₀ →+* S₁)
    (b₀ : S₀ →+* T₀) (b₁ : S₁ →+* T₁) (q : T₀ →+* T₁)
    (hsq₁ : a₁.comp f = p.comp a₀)
    (hsq₂ : b₁.comp p = q.comp b₀)
    (_h₁ :
      letI : Algebra R₀ S₀ := a₀.toAlgebra
      letI : Algebra R₀ R₁ := f.toAlgebra
      letI : Algebra R₀ S₁ := (a₁.comp f).toAlgebra
      letI : Algebra R₁ S₁ := a₁.toAlgebra
      letI : Algebra S₀ S₁ := p.toAlgebra
      haveI : IsScalarTower R₀ R₁ S₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsScalarTower R₀ S₀ S₁ :=
        IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun hsq₁ x
      letI : Algebra (R₁ ⊗[R₀] S₀) S₁ :=
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ R₁ S₁)
          (IsScalarTower.toAlgHom R₀ S₀ S₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
      ∃ W : Submonoid (R₁ ⊗[R₀] S₀), IsLocalization W S₁)
    (_h₂ :
      letI : Algebra S₀ T₀ := b₀.toAlgebra
      letI : Algebra S₀ S₁ := p.toAlgebra
      letI : Algebra S₀ T₁ := (b₁.comp p).toAlgebra
      letI : Algebra S₁ T₁ := b₁.toAlgebra
      letI : Algebra T₀ T₁ := q.toAlgebra
      haveI : IsScalarTower S₀ S₁ T₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsScalarTower S₀ T₀ T₁ :=
        IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun hsq₂ x
      letI : Algebra (S₁ ⊗[S₀] T₀) T₁ :=
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S₀ S₁ T₁)
          (IsScalarTower.toAlgHom S₀ T₀ T₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
      ∃ W : Submonoid (S₁ ⊗[S₀] T₀), IsLocalization W T₁) :
    letI : Algebra R₀ T₀ := (b₀.comp a₀).toAlgebra
    letI : Algebra R₀ R₁ := f.toAlgebra
    letI : Algebra R₀ T₁ := (b₁.comp (a₁.comp f)).toAlgebra
    letI : Algebra R₁ T₁ := (b₁.comp a₁).toAlgebra
    letI : Algebra T₀ T₁ := q.toAlgebra
    haveI : IsScalarTower R₀ R₁ T₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower R₀ T₀ T₁ :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (congrArg b₁ (DFunLike.congr_fun hsq₁ x)).trans (DFunLike.congr_fun hsq₂ (a₀ x))
    letI : Algebra (R₁ ⊗[R₀] T₀) T₁ :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ R₁ T₁)
        (IsScalarTower.toAlgHom R₀ T₀ T₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (R₁ ⊗[R₀] T₀), IsLocalization W T₁ := by
  -- ## The instance blocks, transcribed from the two hypotheses and the conclusion
  letI algR₀S₀ : Algebra R₀ S₀ := a₀.toAlgebra
  letI algR₀R₁ : Algebra R₀ R₁ := f.toAlgebra
  letI algR₀S₁ : Algebra R₀ S₁ := (a₁.comp f).toAlgebra
  letI algR₁S₁ : Algebra R₁ S₁ := a₁.toAlgebra
  letI algS₀S₁ : Algebra S₀ S₁ := p.toAlgebra
  haveI towR₀R₁S₁ : IsScalarTower R₀ R₁ S₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towR₀S₀S₁ : IsScalarTower R₀ S₀ S₁ :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun hsq₁ x
  letI algPS₁ : Algebra (R₁ ⊗[R₀] S₀) S₁ :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ R₁ S₁)
      (IsScalarTower.toAlgHom R₀ S₀ S₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  letI algS₀T₀ : Algebra S₀ T₀ := b₀.toAlgebra
  letI algS₀T₁ : Algebra S₀ T₁ := (b₁.comp p).toAlgebra
  letI algS₁T₁ : Algebra S₁ T₁ := b₁.toAlgebra
  letI algT₀T₁ : Algebra T₀ T₁ := q.toAlgebra
  haveI towS₀S₁T₁ : IsScalarTower S₀ S₁ T₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towS₀T₀T₁ : IsScalarTower S₀ T₀ T₁ :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun hsq₂ x
  letI algQT₁ : Algebra (S₁ ⊗[S₀] T₀) T₁ :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S₀ S₁ T₁)
      (IsScalarTower.toAlgHom S₀ T₀ T₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  letI algR₀T₀ : Algebra R₀ T₀ := (b₀.comp a₀).toAlgebra
  letI algR₀T₁ : Algebra R₀ T₁ := (b₁.comp (a₁.comp f)).toAlgebra
  letI algR₁T₁ : Algebra R₁ T₁ := (b₁.comp a₁).toAlgebra
  haveI towR₀R₁T₁ : IsScalarTower R₀ R₁ T₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI towR₀T₀T₁ : IsScalarTower R₀ T₀ T₁ :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (congrArg b₁ (DFunLike.congr_fun hsq₁ x)).trans (DFunLike.congr_fun hsq₂ (a₀ x))
  letI algAT₁ : Algebra (R₁ ⊗[R₀] T₀) T₁ :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ R₁ T₁)
      (IsScalarTower.toAlgHom R₀ T₀ T₁) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  haveI towR₀S₀T₀ : IsScalarTower R₀ S₀ T₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨W₁, hW₁⟩ := _h₁
  obtain ⟨W₂, hW₂⟩ := _h₂
  haveI : IsLocalization W₁ S₁ := hW₁
  haveI : IsLocalization W₂ T₁ := hW₂
  -- ## `S₀ → R₁ ⊗[R₀] S₀ → S₁` is the structure map `p`
  haveI towS₀PS₁ : IsScalarTower S₀ (R₁ ⊗[R₀] S₀) S₁ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show p x = Algebra.TensorProduct.lift _ _ _ ((1 : R₁) ⊗ₜ[R₀] x)
      simp
      rfl
  -- ## The base-change square `P ⊗[S₀] T₀ → S₁ ⊗[S₀] T₀`
  letI algPTQ : Algebra ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) (S₁ ⊗[S₀] T₀) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S₀ (R₁ ⊗[R₀] S₀) S₁)
      (AlgHom.id S₀ T₀)).toRingHom.toAlgebra
  haveI towPPTQ :
      IsScalarTower (R₁ ⊗[R₀] S₀) ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) (S₁ ⊗[S₀] T₀) := by
    exact @IsScalarTower.of_algebraMap_eq (R₁ ⊗[R₀] S₀) ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀)
      (S₁ ⊗[S₀] T₀) _ _ _ _ _ _
      (fun x => by simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_def])
  -- ## LOCALIZATION COMMUTES WITH BASE CHANGE (the mathematical core)
  haveI hcore : IsLocalization
      (Algebra.algebraMapSubmonoid ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) W₁) (S₁ ⊗[S₀] T₀) :=
    IsLocalization.tensorProduct_tensorProduct S₀ T₀ W₁ S₁
      (by ext t; simp [RingHom.algebraMap_toAlgebra])
  -- ## `R₁ ⊗[R₀] T₀ ≃+* (R₁ ⊗[R₀] S₀) ⊗[S₀] T₀`
  letI algS₀A : Algebra S₀ (R₁ ⊗[R₀] T₀) :=
    ((algebraMap T₀ (R₁ ⊗[R₀] T₀)).comp b₀).toAlgebra
  haveI towR₀R₀PT : IsScalarTower R₀ R₀ ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) :=
    ⟨fun x y z => mul_smul x y z⟩
  haveI towS₀S₀A : IsScalarTower S₀ S₀ (R₁ ⊗[R₀] T₀) := ⟨fun x y z => mul_smul x y z⟩
  -- `S₀` may be pushed from the `T₀` slot of `P ⊗[S₀] T₀` into the `S₀` slot of `P`
  have hslide : ∀ s : S₀, (1 : R₁ ⊗[R₀] S₀) ⊗ₜ[S₀] (b₀ s)
      = ((1 : R₁) ⊗ₜ[R₀] s) ⊗ₜ[S₀] (1 : T₀) := fun s => by
    rw [show ((1 : R₁) ⊗ₜ[R₀] s) = algebraMap S₀ (R₁ ⊗[R₀] S₀) s from rfl,
      show b₀ s = algebraMap S₀ T₀ s from rfl,
      ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply']
  -- the same identity with `(1 : R₁ ⊗[R₀] S₀)` in the form `simp` normalizes it to
  have hslide' : ∀ s : S₀, ((1 : R₁) ⊗ₜ[R₀] (1 : S₀)) ⊗ₜ[S₀] (b₀ s)
      = ((1 : R₁) ⊗ₜ[R₀] s) ⊗ₜ[S₀] (1 : T₀) := fun s => hslide s
  set fwd : (R₁ ⊗[R₀] T₀) →ₐ[R₀] ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) :=
    Algebra.TensorProduct.lift
      { toRingHom := (Algebra.TensorProduct.includeLeftRingHom (R := S₀)
          (A := R₁ ⊗[R₀] S₀) (B := T₀)).comp
          (Algebra.TensorProduct.includeLeftRingHom (R := R₀) (A := R₁) (B := S₀))
        commutes' := by intro r; simp [Algebra.TensorProduct.algebraMap_def] }
      { toRingHom := (Algebra.TensorProduct.includeRight (R := S₀)
          (A := R₁ ⊗[R₀] S₀) (B := T₀)).toRingHom
        commutes' := by
          intro r
          show (1 : R₁ ⊗[R₀] S₀) ⊗ₜ[S₀] (b₀ (a₀ r)) = _
          rw [hslide (a₀ r), Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.algebraMap_apply']
          rfl }
      (fun _ _ => Commute.all _ _) with hfwd
  set bwd : ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) →ₐ[S₀] (R₁ ⊗[R₀] T₀) :=
    Algebra.TensorProduct.lift
      { toRingHom := (Algebra.TensorProduct.map (AlgHom.id R₀ R₁)
          (IsScalarTower.toAlgHom R₀ S₀ T₀)).toRingHom
        commutes' := by intro s; simp [RingHom.algebraMap_toAlgebra] }
      { toRingHom := algebraMap T₀ (R₁ ⊗[R₀] T₀)
        commutes' := fun s => rfl }
      (fun _ _ => Commute.all _ _) with hbwd
  have hbf : bwd.toRingHom.comp fwd.toRingHom = RingHom.id (R₁ ⊗[R₀] T₀) := by
    ext x <;> simp [hfwd, hbwd, RingHom.algebraMap_toAlgebra]
  have hfb : fwd.toRingHom.comp bwd.toRingHom =
      RingHom.id ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) := by
    ext x <;>
      simp [hfwd, hbwd, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.one_def,
        hslide']
  set ε : (R₁ ⊗[R₀] T₀) ≃+* ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) :=
    { fwd.toRingHom with
      invFun := bwd
      left_inv := fun x => DFunLike.congr_fun hbf x
      right_inv := fun x => DFunLike.congr_fun hfb x }
  -- ## Transport the core along `ε`, then compose the two localizations
  letI algAQ : Algebra (R₁ ⊗[R₀] T₀) (S₁ ⊗[S₀] T₀) :=
    ((algebraMap ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) (S₁ ⊗[S₀] T₀)).comp
      (ε : (R₁ ⊗[R₀] T₀) →+* ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀))).toAlgebra
  haveI hQ : IsLocalization
      ((Algebra.algebraMapSubmonoid ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) W₁).comap
        (ε : (R₁ ⊗[R₀] T₀) →+* ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀))) (S₁ ⊗[S₀] T₀) :=
    isLocalization_comap_of_ringEquiv ε
      (algebraMap ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) (S₁ ⊗[S₀] T₀))
      (Algebra.algebraMapSubmonoid ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) W₁) hcore
  have hεapp : ∀ a : R₁ ⊗[R₀] T₀, ε a = fwd a := fun _ => rfl
  haveI towAQT₁ : IsScalarTower (R₁ ⊗[R₀] T₀) (S₁ ⊗[S₀] T₀) T₁ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x <;> simp [hεapp, hfwd, RingHom.algebraMap_toAlgebra]
  exact ⟨_, IsLocalization.localization_localization_isLocalization
    ((Algebra.algebraMapSubmonoid ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀) W₁).comap
      (ε : (R₁ ⊗[R₀] T₀) →+* ((R₁ ⊗[R₀] S₀) ⊗[S₀] T₀))) W₂ T₁⟩

end IsLocalizationTensorComp

/-! ### THE CUT OF 10.127.11 INTO A MODEL HALF AND A LOCALIZATION HALF

(2026-07-30.)  `exists_noetherianLocalExtSystem_of_essFinitePresentation` below used to
be one sorry leaf carrying the whole of 10.127.11.  Its own SURVEY paragraph already
named the seam — finding 1 said the MODEL half is in the pin
(`Algebra.Presentation.HasCoeffs`), finding 2 said "what is NOT supplied is everything
about the LOCALIZATIONS", and those two halves share nothing but a tower of rings — so
the leaf is cut along exactly that line, into three pieces of which the FIRST is proven:

* `exists_isLocalization_atPrime_of_essFinitePresentation` (**PROVEN**) — the local
  normal form.  `EssFinitePresentation g` hands over an arbitrary submonoid `M ⊆ T`; over
  a LOCAL target that submonoid can always be enlarged to the full complement of the
  contracted prime `𝔮 = vT⁻¹(𝔪_B)`, so `B = T_𝔮`.  This is the step every write-up of
  10.127.11 opens with, and it is what lets the rest of the argument work with a single
  prime per stage instead of a submonoid it would have to descend as well.
* `exists_noetherianModelTower_of_finitePresentation` (**LEAF**) — the model half:
  a finitely presented `R`-algebra `T` is, from some stage on, the filtered colimit of
  finitely presented models `T_λ` over `R_λ` that base-change to one another.  No
  localization, no locality, no prime occurs in it.
* `exists_noetherianLocalExtSystem_of_noetherianModelTower` (**LEAF**) — the
  localization half: given such a tower and a prime `𝔮` of `T` with `B = T_𝔮`, take
  `𝔮_λ = ` the contraction of `𝔮` to `T_λ` and `S_λ = (T_λ)_{𝔮_λ}`, and the sixteen
  fields of the rung follow.  No presentation, no polynomial ring and no coefficient
  descent occurs in it.

**WHY THIS SEAM AND NOT ANOTHER.**  The two halves are written in disjoint vocabularies:
the model half is `MvPolynomial`/`Ideal.span`/`Algebra.FinitePresentation` and never
mentions a local ring, while the localization half is `Ideal.comap`/`primeCompl`/
`IsLocalization` and never mentions a presentation.  That is why the tower
`NoetherianModelTower` — which is the interface between them — carries `IsNoetherianRing`
and NOT `Algebra.FinitePresentation`: Noetherianity is all the localization half consumes,
and putting finite presentation in the interface would have strengthened the model leaf
for no consumer's benefit.

**WHAT THE `isPushoutModT` FIELD IS FOR.**  It is the only field of the tower whose sole
consumer is the rung's `isLocalizationMidT`, and it is what `IsLocalizationTensorComp`
above was built to consume: with `T_μ = R_μ ⊗_{R_λ} T_λ`, `R_μ ⊗_{R_λ} (T_λ)_{𝔮_λ}` is
`(T_μ)_W` for `W` the image of `T_λ ∖ 𝔮_λ`, and `(T_μ)_{𝔮_μ}` is a further localization
of that because `W ⊆ T_μ ∖ 𝔮_μ`.  Without it the two towers would be unrelated and
`isLocalizationMidT` would be unprovable — which is the check that would refute dropping
the field.

**THE CHECK THAT WOULD REFUTE THIS CUT.**  Exhibit a finitely presented `R`-algebra `T`
and a base tower for `R` admitting a model tower, and a prime `𝔮` of `T` over `𝔪_R`, for
which no rung exists — i.e. a counterexample to 10.127.11 with its model half already
granted.  Equivalently: find a field of `NoetherianLocalExtSystem` not derivable from the
tower plus `𝔮`.  The one to check first is `isLocalHomBaseToMid`, since it is the only
field that uses locality of anything: it holds because the contraction of `𝔮_λ` to `R_λ`
is the contraction of `𝔪_B` along `R_λ → R → B`, and both of those maps are local
(`bs.isLocalHomBaseToR` and `[IsLocalHom g]`). -/

/-- **THE LOCAL NORMAL FORM OF `EssFinitePresentation`** (PROVEN 2026-07-30): over a LOCAL
target the localizing submonoid may be taken to be the complement of a prime.

*If `g : R →+* B` is essentially of finite presentation and `B` is local, then `g` factors
as `R → T → B` with `T` finitely presented over `R` and `B` the localization of `T` at the
complement of `𝔮 = vT⁻¹(𝔪_B)`.*

`EssFinitePresentation` is stated with an arbitrary submonoid `M ⊆ T` because that is what
makes it composable; but `M` can only consist of elements that become UNITS in `B`, and in
a local ring a unit is exactly an element outside the maximal ideal, so `M ⊆ 𝔮.primeCompl`
and enlarging `M` to `𝔮.primeCompl` costs nothing: `map_units` is
`IsLocalRing.notMem_maximalIdeal`, and `surj` and `exists_of_eq` are inherited from `M`
verbatim along that inclusion.

This is what lets `exists_noetherianLocalExtSystem_of_noetherianModelTower` below work
with one PRIME per stage.  Descending a general submonoid through the tower as well would
be a second, independent colimit argument and is exactly what this lemma removes. -/
theorem exists_isLocalization_atPrime_of_essFinitePresentation
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing B] {g : R →+* B}
    (hfp : EssFinitePresentation g) :
    ∃ (T : Type u) (_ : CommRing T) (gT : R →+* T) (vT : T →+* B),
      gT.FinitePresentation ∧ vT.comp gT = g ∧
      @IsLocalization T _ ((IsLocalRing.maximalIdeal B).comap vT).primeCompl B _
        vT.toAlgebra := by
  obtain ⟨T, hT, gT, vT, M, hfpT, hcomp, hlocM⟩ := hfp
  refine ⟨T, hT, gT, vT, hfpT, hcomp, ?_⟩
  letI : Algebra T B := vT.toAlgebra
  haveI : IsLocalization M B := hlocM
  have hmap : ∀ t : T, algebraMap T B t = vT t := fun _ => rfl
  -- `M` consists of units of `B`, hence of elements outside the contracted prime
  have hMB : ∀ m : T, m ∈ M → m ∈ ((IsLocalRing.maximalIdeal B).comap vT).primeCompl := by
    intro m hm hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr
      (by simpa [hmap] using IsLocalization.map_units (M := M) B ⟨m, hm⟩)) hmem
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalRing.notMem_maximalIdeal.mp hs
  · intro z
    obtain ⟨⟨t, m, hm⟩, hz⟩ := IsLocalization.surj (M := M) z
    exact ⟨⟨t, ⟨m, hMB m hm⟩⟩, hz⟩
  · intro x y hxy
    obtain ⟨⟨c, hc⟩, h⟩ := IsLocalization.exists_of_eq (M := M) hxy
    exact ⟨⟨c, hMB c hc⟩, h⟩

/-- **A TOWER OF NOETHERIAN MODELS OVER A BASE TOWER** — the interface between the two
halves of 10.127.11, and the only object the model leaf below produces.

Over a base tower `bs` for `R` and a ring map `gT : R →+* T`, this is a tower of
Noetherian rings `T_λ` over the `R_λ`, with `T` as filtered colimit and each `T_μ` the
BASE CHANGE `R_μ ⊗_{R_λ} T_λ`.  It is `NoetherianLocalExtSystem` with every locality
condition deleted and `isLocalizationMidT` strengthened to `isPushoutModT`: a model tower
is a tower of honest base changes, and it is the localization half that turns those base
changes into the localizations the rung asks for.

**WHY NOT `Algebra.FinitePresentation` AS A FIELD.**  The models really are finitely
presented — that is how the leaf below builds them, out of a fixed presentation of `T`
over `R` whose coefficients have been descended to `R_{i₀}` — but nothing downstream
consumes more than `IsNoetherianRing`, so the extra strength would only make the model
leaf harder to prove while making the localization leaf no easier.  Weakness belongs in
the statement.

**NON-DEGENERACY.**  `Mod = Base`, `baseToMod = id`, `modToT = gT ∘ baseToR` satisfies
every structural field and `isPushoutModT` (`R_μ ⊗_{R_λ} R_λ ≅ R_μ`), and fails
`mod_surj` as soon as `gT` is not surjective; so the datum is not free.  It is also not
vacuous: `bs` is unconditionally inhabited (`nonempty_noetherianLocalBaseSystem`). -/
structure NoetherianModelTower {R T : Type u} [CommRing R] [CommRing T]
    (bs : NoetherianLocalBaseSystem R) (gT : R →+* T) where
  /-- `T_λ`, the model at stage `λ`. -/
  Mod : bs.Λ → CommRingCat.{u}
  /-- Each `T_λ` is Noetherian. -/
  isNoetherianMod : ∀ i, IsNoetherianRing (Mod i)
  /-- `R_λ → T_λ`. -/
  baseToMod : ∀ i, bs.Base i →+* Mod i
  /-- The transition map `T_λ → T_μ`. -/
  modT : ∀ {i j}, bs.le i j → (Mod i →+* Mod j)
  /-- `modT` is functorial. -/
  modT_comp : ∀ {i j k} (h₁ : bs.le i j) (h₂ : bs.le j k),
    (modT h₂).comp (modT h₁) = modT (bs.le_trans' h₁ h₂)
  /-- The vertical maps are natural in `Λ`. -/
  comm_baseT : ∀ {i j} (h : bs.le i j),
    (baseToMod j).comp (bs.baseT h) = (modT h).comp (baseToMod i)
  /-- The cocone map `T_λ → T`. -/
  modToT : ∀ i, Mod i →+* T
  /-- The square `R_λ → T_λ → T` / `R_λ → R → T` commutes. -/
  comm_baseMod : ∀ i, (modToT i).comp (baseToMod i) = gT.comp (bs.baseToR i)
  /-- `modToT` is a cocone. -/
  comm_modToT : ∀ {i j} (h : bs.le i j), (modToT j).comp (modT h) = modToT i
  /-- `T` is the colimit, half one. -/
  mod_surj : ∀ x : T, ∃ i, ∃ y : Mod i, modToT i y = x
  /-- `T` is the colimit, half two. -/
  mod_sep : ∀ i (x y : Mod i), modToT i x = modToT i y →
    ∃ j, ∃ h : bs.le i j, modT h x = modT h y
  /-- **The models base-change**: `T_μ = R_μ ⊗_{R_λ} T_λ`.  This is the field that
  `isLocalizationMidT` is derived from, through `IsLocalizationTensorComp` above. -/
  isPushoutModT : ∀ {i j} (h : bs.le i j),
    letI : Algebra (bs.Base i) (Mod i) := (baseToMod i).toAlgebra
    letI : Algebra (bs.Base i) (bs.Base j) := (bs.baseT h).toAlgebra
    letI : Algebra (bs.Base i) (Mod j) := ((baseToMod j).comp (bs.baseT h)).toAlgebra
    letI : Algebra (bs.Base j) (Mod j) := (baseToMod j).toAlgebra
    letI : Algebra (Mod i) (Mod j) := (modT h).toAlgebra
    haveI : IsScalarTower (bs.Base i) (bs.Base j) (Mod j) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (bs.Base i) (Mod i) (Mod j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm_baseT h) x
    Function.Bijective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (bs.Base i) (bs.Base j) (Mod j))
      (IsScalarTower.toAlgHom (bs.Base i) (Mod i) (Mod j))
      fun _ _ => Commute.all _ _)

/-- **THE MODEL HALF OF 10.127.11** (sorry leaf, cut 2026-07-30 out of
`exists_noetherianLocalExtSystem_of_essFinitePresentation` below; read the section note
"THE CUT OF 10.127.11 INTO A MODEL HALF AND A LOCALIZATION HALF" above first).

*A finitely presented `R`-algebra is, from some stage of a base tower for `R` on, the
filtered colimit of a base-changing tower of Noetherian models over the `R_λ`.*

**THE PROOF.**  Fix a finite presentation `T = R[x_1,…,x_n]/(f_1,…,f_m)` (`_hfp`).  The
`f_k` have finitely many coefficients between them, so `bs.base_surj` and `bs.directed`,
applied finitely many times, give `i₀` and lifts `F_k ∈ R_{i₀}[x]` with
`map (baseToR i₀) F_k = f_k`.  For `λ ≥ i₀` put `F_k^λ := map (baseT) F_k` and

    T_λ := R_λ[x_1,…,x_n] ⧸ (F_1^λ, …, F_m^λ).

Everything then follows from that ONE choice of lift, which is why the lifts must be
transported along `baseT` rather than chosen afresh at each `λ` — independent choices
would not be compatible and `isPushoutModT` would fail:

* `isNoetherianMod` is Hilbert's basis theorem plus `Ideal.Quotient`;
* `modT`, `modToT` and their functoriality are `MvPolynomial.map`, which carries
  generators to generators, so the ideals are respected with no computation;
* `mod_surj` descends the finitely many coefficients of one representing polynomial;
* `mod_sep` is where finite PRESENTATION (as opposed to finite type) is spent: a
  polynomial over `R_λ` dying in `T` is `∑ h_k f_k` for FINITELY many `h_k ∈ R[x]`, whose
  coefficients descend to some `μ`, after which `bs.base_sep` on the finitely many
  coefficients of the difference gives a `ν` at which it dies already;
* `isPushoutModT` is base change of a quotient of a polynomial ring:
  `R_μ ⊗_{R_λ} R_λ[x]/(F^λ) ≅ R_μ[x]/(F^μ)`.

**WHAT IS IN THE PIN.**  `Mathlib/RingTheory/Extension/Presentation/Core.lean` supplies
the coefficient-lifting step directly — `Algebra.Presentation.HasCoeffs R₀` asks exactly
`coeffs ⊆ Set.range (algebraMap R₀ R)`, `relationOfHasCoeffs` is the lift, and
`ModelOfHasCoeffs R₀` with `tensorModelOfHasCoeffsEquiv` is `T = R ⊗_{R₀} T_{i₀}` for the
BOTTOM stage.  It does NOT give the tower, because `relationOfHasCoeffs` is a `choose` and
so gives unrelated lifts at different stages; take the lift ONCE at `i₀` and push it up
with `baseT`.  `Mathlib/RingTheory/Smooth/NoetherianDescent.lean` is a worked example of
the same idiom and is worth reading first.

**FAITHFULNESS.**  This is 10.127.11's construction with every localization deleted, so it
is true if 10.127.11 is; and it is strictly weaker than the leaf it was cut from, since
`NoetherianModelTower` has no locality conditions.  Note there is no `[IsLocalRing R]` and
no `IsLocalHom` anywhere in the statement, deliberately: nothing in the argument uses
either, and adding them would hide that fact.  **NOT vacuous**: `bs` is unconditionally
inhabited, and the conclusion is not satisfiable by a constant tower (see the structure's
NON-DEGENERACY note). -/
theorem exists_noetherianModelTower_of_finitePresentation {R T : Type u}
    [CommRing R] [CommRing T]
    (bs : NoetherianLocalBaseSystem R) (gT : R →+* T) (_hfp : gT.FinitePresentation) :
    ∃ i₀ : bs.Λ, Nonempty (NoetherianModelTower (bs.restrict i₀) gT) :=
  sorry

/-- **THE LOCALIZATION HALF OF 10.127.11** (sorry leaf, cut 2026-07-30 out of
`exists_noetherianLocalExtSystem_of_essFinitePresentation` below; read the section note
"THE CUT OF 10.127.11 INTO A MODEL HALF AND A LOCALIZATION HALF" above first).

*Given a model tower for `T` over a base tower for `R`, and a prime `𝔮` of `T` with
`B = T_𝔮`, the localizations `S_λ = (T_λ)_{𝔮_λ}` at the contractions `𝔮_λ` of `𝔮` form a
rung over that base tower.*

**THE PROOF, FIELD BY FIELD.**  Put `𝔮_λ := (modToT λ)⁻¹(𝔮)`, prime, and
`S_λ := (T_λ)_{𝔮_λ}`.

* `isNoetherianMid`, `isLocalRingMid`: a localization of a Noetherian ring at a prime.
* `midT h` exists because `𝔮_λ = (modT h)⁻¹(𝔮_μ)` — both sides being `(modToT)⁻¹(𝔮)`
  through `comm_modToT` — so `T_λ ∖ 𝔮_λ` lands in `T_μ ∖ 𝔮_μ`.  `midToB` exists for the
  same reason with `𝔮` in place of `𝔮_μ`, and both are automatically local.
* `isLocalHomBaseToMid` is the ONLY field that uses locality of anything.  The contraction
  of `𝔮_λ` to `R_λ` is the contraction of `𝔪_B` along `R_λ → R → B` (by `comm_baseMod`
  and `_hcomp`), and both of those maps are local (`bs.isLocalHomBaseToR`, `[IsLocalHom g]`),
  so that contraction is `𝔪_{R_λ}`.
* `mid_surj`: an element of `B` is `t/s` with `s ∉ 𝔮` (`_hloc`); `mod_surj` and
  `bs.directed` put both at one stage, and `s_λ ∉ 𝔮_λ` because its image is `s`.
* `mid_sep`: two fractions over `T_λ` agreeing in `B` differ by a factor `u ∉ 𝔮`
  (`IsLocalization.exists_of_eq` for `_hloc`); descend `u` and the resulting equation with
  `mod_surj`/`mod_sep`, and at that stage `u` is a unit of `S`, so the fractions agree.
* `isLocalizationMidT` is `isPushoutModT` fed to `IsLocalizationTensorComp` above:
  `R_μ ⊗_{R_λ} S_λ = R_μ ⊗_{R_λ} (T_λ)_{𝔮_λ}` is `(T_μ)_W` for `W` the image of
  `T_λ ∖ 𝔮_λ`, and `S_μ = (T_μ)_{𝔮_μ}` is a further localization of it because
  `W ⊆ T_μ ∖ 𝔮_μ` (`IsLocalization.localization_localization_isLocalization`).

**FAITHFULNESS.**  Every conclusion is a field of `NoetherianLocalExtSystem`, so this is
no stronger than 10.127.11's conclusion for `R → S`.  The hypothesis `_hloc` is the LOCAL
NORMAL FORM produced by `exists_isLocalization_atPrime_of_essFinitePresentation` above and
not an extra assumption smuggled in: `EssFinitePresentation g` plus `IsLocalRing B`
implies it.  **NOT vacuous**, and in particular not satisfiable by `Mid = Base`, which
fails `mid_surj` whenever `g` is not surjective.

**THE CHECK THAT WOULD REFUTE IT.**  A model tower and a prime `𝔮` over `𝔪_R` for which
some contraction `𝔮_λ` fails to be prime, or for which `R_λ → S_λ` fails to be local.  The
first cannot happen (contractions of primes are prime); the second is the bullet above and
is where `[IsLocalHom g]` is spent — dropping that hypothesis DOES make the leaf false,
since a non-local `g` can put `𝔪_{R_λ}` outside the contraction of `𝔮_λ`. -/
theorem exists_noetherianLocalExtSystem_of_noetherianModelTower {R B T : Type u}
    [CommRing R] [CommRing B] [CommRing T] [IsLocalRing R] [IsLocalRing B]
    {bs : NoetherianLocalBaseSystem R} {g : R →+* B} [IsLocalHom g]
    {gT : R →+* T} {vT : T →+* B} (_hcomp : vT.comp gT = g)
    (_mt : NoetherianModelTower bs gT)
    (_hloc : @IsLocalization T _ ((IsLocalRing.maximalIdeal B).comap vT).primeCompl B _
      vT.toAlgebra) :
    Nonempty (NoetherianLocalExtSystem bs g) :=
  sorry

/-- **THE CONSTRUCTION OF 10.127.11, ONCE: a rung over a given base tower**
(PROVEN 2026-07-30 over the two leaves above; cut 2026-07-28 out of
`nonempty_noetherianApproxSystem_of_baseSystem`, and it was that leaf's remaining
mathematical content).

*Over a directed system of Noetherian local subrings with colimit `R`, a local
`g : R →+* B` essentially of finite presentation is, from some index `i₀` on, the
filtered colimit of a tower of Noetherian local stages `S_λ` with `S_μ` a
localization of `R_μ ⊗_{R_λ} S_λ`.*

**WHAT THE `∃ i₀` IS.**  A model `S_λ = (R_λ[x]/(f_λ))_{𝔮_λ}` exists only once
`R_λ` contains the coefficients of a fixed finite presentation of `B` over `R`,
which happens from some stage on by `bs.base_surj` and `bs.directed` applied
finitely many times.  Below that stage there is no rung and the statement does not
claim one — that is exactly the "work over the RESTRICTED system" step of the
previous docstring, and `NoetherianLocalBaseSystem.restrict` (PROVEN above) is what
makes `bs.restrict i₀` again a legitimate base tower to state the rung over.

**WHAT THE BODY DOES** (2026-07-30).  Nothing but assemble the three declarations
above: the local normal form replaces the localizing submonoid of
`EssFinitePresentation` by the complement of a prime; the model leaf produces the
`i₀` and the tower of models; the localization leaf localizes that tower at the
contractions of the prime.  The SURVEY below is what generated that cut, and its
findings 1 and 2 are now the model leaf and the localization leaf respectively.

**SURVEY — three findings, each greppable, RE-VERIFIED 2026-07-28.**

1. **The model half is already in the pin**, in a place a grep for "Noetherian
   approximation" misses: `Mathlib/RingTheory/Extension/Presentation/Core.lean`
   defines, for a `Presentation R S ι σ` with `ι`, `σ` finite, `P.coeffs`, the
   class `P.HasCoeffs R₀`, `P.ModelOfHasCoeffs R₀` — carrying an instance
   `Algebra.FinitePresentation R₀ (P.ModelOfHasCoeffs R₀)` — and
   `P.tensorModelOfHasCoeffsEquiv R₀ : R ⊗[R₀] P.ModelOfHasCoeffs R₀ ≃ₐ[R] S`.
   That is "descend a finitely presented algebra to a subring containing the
   coefficients and recover it by base change", i.e. the `S_λ = R_λ[x]/(f_λ)` half
   with the base-change property supplied.  `R₀` need not inject into `R`; the
   class only asks `coeffs ⊆ Set.range (algebraMap R₀ R)`.
   **`Mathlib/RingTheory/Smooth/NoetherianDescent.lean` is a WORKED EXAMPLE of this
   exact idiom** (`Algebra.Smooth.exists_subalgebra_fg`,
   `Algebra.Etale.exists_subalgebra_fg`): it is smooth/étale-specific and does NOT
   supply 10.127.13, but it is the closest thing in the pin to the argument wanted
   here and should be read before writing.  `Mathlib/RingTheory/Smooth/Flat.lean`
   runs the same "choose a model over a finitely generated `ℤ`-subalgebra" pattern
   through `Algebra.exists_finiteType ℤ R A`.

2. **What is NOT supplied is everything about the LOCALIZATIONS**: the primes
   `𝔮_λ`, the locality of `S_λ` and of `S_λ → S`, and `isLocalizationMidT`.  Those
   are this leaf's real work, and they are why the rung is stated for LOCAL rings
   and LOCAL homomorphisms throughout.

3. **Do not look for `Ring.DirectLimit`.**  With essential finite PRESENTATION the
   ideals do not grow with `λ` (fixed generators suffice), so the only thing a
   transition map does is enlarge the base: the system is concrete and no abstract
   colimit is constructed.  `grep -rn "Ring.DirectLimit" Fermat/ ~/cs/FLT` found no
   use anywhere in this development on 2026-07-28; a hit means this note is stale.

**FAITHFULNESS.**  The conclusion is 10.127.11's conclusion for `R → S` with
"essentially of finite type over `ℤ`" weakened to "Noetherian" and "localization at
a prime" to "localization at a submonoid", so it is true if 10.127.11 is.  It is
not vacuous: `bs` is unconditionally inhabited (`nonempty_noetherianLocalBaseSystem`)
and `bs.restrict i₀` is inhabited for every `i₀`.  Nor is it trivially satisfiable:
`Mid = Base` fails `mid_surj` whenever `g` is not surjective, and a constant tower
on a Noetherian subring of `B` fails it too. -/
theorem exists_noetherianLocalExtSystem_of_essFinitePresentation {R B : Type u}
    [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    (bs : NoetherianLocalBaseSystem R) (g : R →+* B) [IsLocalHom g]
    (hfp : EssFinitePresentation g) :
    ∃ i₀ : bs.Λ, Nonempty (NoetherianLocalExtSystem (bs.restrict i₀) g) := by
  obtain ⟨T, hT, gT, vT, hfpT, hcomp, hloc⟩ :=
    exists_isLocalization_atPrime_of_essFinitePresentation hfp
  obtain ⟨i₀, ⟨mt⟩⟩ := exists_noetherianModelTower_of_finitePresentation bs gT hfpT
  exact ⟨i₀, exists_noetherianLocalExtSystem_of_noetherianModelTower hcomp mt hloc⟩

/-- **NOETHERIAN APPROXIMATION, THE `S_λ` AND `S'_λ` TOWERS: Stacks 10.127.13
OVER A GIVEN `R_λ` TOWER** (PROVEN 2026-07-28 over the three leaves above; cut
2026-07-28 out of
`nonempty_flatNoetherianStage_of_essFinitePresentation` below, then cut again the
same day against `nonempty_noetherianLocalBaseSystem`.  Read the section notes
"THE CUT OF THE APPROXIMATION LEAF" and "THE `R_λ` TOWER, CUT OFF AND PROVEN"
above first).

*Given a directed system of Noetherian local subrings with colimit `R`, a local
`R → B → A` with both `R → B` and `R → A` essentially of finite presentation is
the filtered colimit of a directed system of NOETHERIAN local stages, with the
transition maps localizations after base change.*

This is 10.127.13 (which is 10.127.11 applied twice, once to `R → S` and once to
`R → S'`, on a common index set) with the module dropped, because 00R7 is applied
at `M = S' = A`.  It contains no flatness whatsoever: every flatness statement of
00R7's proof is in the two leaves below.

**WHAT `_bs` IS FOR, AND WHY IT IS NOT DECORATION.**  `_bs` is the whole of
10.127.11's opening — the index set, the tower `R_λ`, its Noetherianity and
locality, the local transition and cocone maps, and the two colimit conditions —
proven unconditionally above.  A prover of this leaf is expected to CONSUME it,
in the shape 10.127.13 uses: fix finite presentations of `B` over `R` and of `A`
over `B`, take `i₀ : _bs.Λ` large enough (`base_surj` plus `directed`, finitely
many times) that `_bs.Base i₀` contains every coefficient of both, and then work
over the RESTRICTED system `{i | _bs.le i₀ i}`, which is again a base system —
that restriction is why the leaf is stated with `_bs` as an ordinary input and no
compatibility clause: the produced system's base tower is a cofinal piece of
`_bs`'s, but saying so in the type would cost an equality of `CommRingCat`
objects for no consumer's benefit.  Rebuilding the `R_λ` tower here instead of
using `_bs` is permitted by the type and is strictly more work.

**WHAT THE BODY DOES, AND WHAT IS LEFT** (2026-07-28 — read the section note
"10.127.13 IS 10.127.11 APPLIED TWICE" above).  The body is now real code: it
builds the first rung over `_bs.restrict i₀`, reads its `Mid` tower as a base
tower for `B` (`NoetherianLocalExtSystem.toBaseSystem`), builds the second rung
over a further restriction of THAT above `j₀`, carries the first rung down to the
same index set (`NoetherianLocalExtSystem.restrict`), and names the fifty fields of
`NoetherianApproxSystem` off the three objects.  The `Mid` and `Tot` towers are
therefore indexed by ONE type and `midToTot` is the second rung's `baseToMid`, not
a comparison map that would have to be built.

So the whole of the "eight commutation and functoriality fields", the four colimit
conditions and the two `isLocalization` fields that this leaf used to owe are
DISCHARGED here; of the three named leaves it was cut over, **exactly ONE is still
open** (`exists_isLocalization_tensor_comp` was PROVEN on 2026-07-30 and
`essFinitePresentation_of_essFinitePresentation_comp` later the same day):

* `exists_noetherianLocalExtSystem_of_essFinitePresentation` — the construction of
  10.127.11 itself, i.e. the models `S_λ = (R_λ[x]/(f_λ))_{𝔮_λ}` and their
  localizations at the contracted primes.  **This is the mathematics, and it is now
  the whole of what this leaf's subtree still owes**, and the three-finding SURVEY
  that used to sit in this docstring has moved into its own, where it belongs —
  including the addition (2026-07-28) that
  `Mathlib/RingTheory/Smooth/NoetherianDescent.lean` is a worked example of the
  `HasCoeffs` descent idiom;
* `essFinitePresentation_of_essFinitePresentation_comp` — [Stacks 00F4] for
  essentially finite presentation, needed because the second rung is built for
  `v : B →+* A` while 00R7 gives the hypothesis on `v.comp g`.  **PROVEN
  2026-07-30** — and NOT by the route the cut planned: it goes through
  `B ⊗_R T_A`, its localization at the image of `M_A`, and a SECTION `A →+* L` of
  the evaluation map, so the pin's `RingHom.FinitePresentation.of_comp_finiteType`
  is never used and only the generators of `T_B` are needed.  The two presentation
  lemmas it consumes (`essFinitePresentation_of_isLocalization` and
  `essFinitePresentation_comp_of_fg_ker`) were HOISTED ~3000 lines up to sit above
  it; notes were left at both old sites.

`exists_isLocalization_tensor_comp` — `isLocalizationTotBaseT` derived from the other two
localization fields — is **PROVEN** (2026-07-30), over
`IsLocalization.tensorProduct_tensorProduct` and
`IsLocalization.localization_localization_isLocalization`, with a hand-built
`R₁ ⊗[R₀] T₀ ≃+* (R₁ ⊗[R₀] S₀) ⊗[S₀] T₀` in between; the three instance traps that made
it look like missing theory are recorded in its docstring.  Neither
`Algebra.TensorProduct.cancelBaseChange` nor `IsLocalization.tensor` is used — the cut
note named both and both were wrong turns.

**FAITHFULNESS.**  The hypotheses are 00R7's plus one that is unconditionally
satisfiable (`_bs`, by `nonempty_noetherianLocalBaseSystem`), and the conclusion
is a strict subset of 10.127.13's conclusions (the module is dropped, "essentially
of finite type over `ℤ`" is weakened to "Noetherian", and "localization at a
prime" to "localization at a submonoid"), so this is true if 10.127.13 is.
Adding `_bs` therefore cannot weaken the statement: it is implied by the version
without it, and it implies that version, since `_bs` can always be supplied.
Non-degeneracy is discussed in `NoetherianApproxSystem`'s docstring: `base_surj`
is what rules out a constant system on a Noetherian subring. -/
theorem nonempty_noetherianApproxSystem_of_baseSystem
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (bs : NoetherianLocalBaseSystem R)
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g) :
    Nonempty (NoetherianApproxSystem g v) := by
  obtain ⟨i₀, ⟨e₁⟩⟩ := exists_noetherianLocalExtSystem_of_essFinitePresentation bs g hfpB
  obtain ⟨j₀, ⟨e₂⟩⟩ := exists_noetherianLocalExtSystem_of_essFinitePresentation
    e₁.toBaseSystem v (essFinitePresentation_of_essFinitePresentation_comp hfpA hfpB)
  -- `bsF` is the base tower restricted twice; `e₁'` is the first rung carried down
  -- to that index set, so that `bsF`, `e₁'` and `e₂` are all indexed by one type.
  set bsF := (bs.restrict i₀).restrict j₀ with _hbsF
  set e₁' := e₁.restrict j₀ with _he₁'
  exact ⟨{ Λ := bsF.Λ
           nonemptyΛ := bsF.nonemptyΛ
           le := bsF.le
           le_rfl := bsF.le_rfl
           le_trans' := bsF.le_trans'
           directed := bsF.directed
           Base := bsF.Base
           Mid := e₁'.Mid
           Tot := e₂.Mid
           isLocalRingBase := bsF.isLocalRingBase
           isLocalRingMid := e₁'.isLocalRingMid
           isLocalRingTot := e₂.isLocalRingMid
           isNoetherianBase := bsF.isNoetherianBase
           isNoetherianMid := e₁'.isNoetherianMid
           isNoetherianTot := e₂.isNoetherianMid
           baseToMid := e₁'.baseToMid
           midToTot := e₂.baseToMid
           isLocalHomBaseToMid := e₁'.isLocalHomBaseToMid
           isLocalHomMidToTot := e₂.isLocalHomBaseToMid
           baseT := bsF.baseT
           midT := e₁'.midT
           totT := e₂.midT
           baseToR := bsF.baseToR
           midToB := e₁'.midToB
           totToA := e₂.midToB
           comm_baseMid := e₁'.comm_baseMid
           comm_midTot := e₂.comm_baseMid
           comm_baseT := e₁'.comm_baseT
           comm_midT := e₂.comm_baseT
           baseT_comp := bsF.baseT_comp
           midT_comp := e₁'.midT_comp
           totT_comp := e₂.midT_comp
           comm_baseToR := bsF.comm_baseToR
           comm_midToB := e₁'.comm_midToB
           comm_totToA := e₂.comm_midToB
           isLocalHomBaseT := bsF.isLocalHomBaseT
           isLocalHomMidT := e₁'.isLocalHomMidT
           isLocalHomTotT := e₂.isLocalHomMidT
           isLocalHomBaseToR := bsF.isLocalHomBaseToR
           isLocalHomMidToB := e₁'.isLocalHomMidToB
           isLocalHomTotToA := e₂.isLocalHomMidToB
           base_surj := bsF.base_surj
           mid_surj := e₁'.mid_surj
           tot_surj := e₂.mid_surj
           base_sep := bsF.base_sep
           mid_sep := e₁'.mid_sep
           tot_sep := e₂.mid_sep
           isLocalizationMidT := e₁'.isLocalizationMidT
           isLocalizationTotT := e₂.isLocalizationMidT
           isLocalizationTotBaseT := fun {i j} h =>
             exists_isLocalization_tensor_comp (bsF.baseT h) (e₁'.baseToMid i) (e₁'.baseToMid j)
               (e₁'.midT h) (e₂.baseToMid i) (e₂.baseToMid j) (e₂.midT h)
               (e₁'.comm_baseT h) (e₂.comm_baseT h)
               (e₁'.isLocalizationMidT h) (e₂.isLocalizationMidT h) }⟩

/-- **NOETHERIAN APPROXIMATION: Stacks 10.127.11 + 10.127.13** (PROVEN 2026-07-28
over the two declarations above, cut 2026-07-28 out of
`nonempty_flatNoetherianStage_of_essFinitePresentation` below).

*A local `R → B → A` with both `R → B` and `R → A` essentially of finite
presentation is the filtered colimit of a directed system of NOETHERIAN local
stages, with the transition maps localizations after base change.*

The body is glue: the `R_λ` tower exists unconditionally
(`nonempty_noetherianLocalBaseSystem`, PROVEN — it is 10.127.11's opening and
needs neither `B`, nor `A`, nor either finite-presentation hypothesis), and
`nonempty_noetherianApproxSystem_of_baseSystem` descends `B` and `A` over it.
The docstring of that leaf is the specification of everything that remains; the
SURVEY above says where to start on it. -/
theorem nonempty_noetherianApproxSystem_of_essFinitePresentation
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g) :
    Nonempty (NoetherianApproxSystem g v) := by
  obtain ⟨bs⟩ := nonempty_noetherianLocalBaseSystem R
  exact nonempty_noetherianApproxSystem_of_baseSystem bs hfpA hfpB
/-! ### 10.128.3 IS ONE LEMMA APPLIED TWICE — the two-tower abstraction, 2026-07-28

**SECTION NOTE for `IsNoetherianFlatDescentSystem` and the six declarations under it.**

The two leaves of the cut above,
`exists_flatBase_index_of_noetherianApproxSystem` and
`exists_flatFibre_index_of_noetherianApproxSystem`, are the SAME source lemma —
Stacks 10.128.3 ([Stacks 00R6]) — applied to two different systems.  00R7's proof
says so in as many words: step 2 applies it to `(R_λ → S'_λ, M_λ)` and step 3
checks that the fibre datum `(S_λ/𝔭_λ S_λ → S'_λ/𝔭_λ S'_λ, M_λ/𝔭_λ M_λ)` is again
a system as in 10.127.13 and applies it AGAIN.  Proving the two leaves separately
would therefore build 10.128.3 twice, so the machinery is stated ONCE here, as a
predicate on an abstract two-tower system, and both leaves are `exact` applications
of it.  That is the whole design of this block; the mathematics that is NOT shared —
the fibre-system verification — is the three leaves under
`isNoetherianFlatDescentSystem_fibre`.

**WHY TWO TOWERS AND NOT THREE.**  10.128.3's data is a ring map `R → S` together
with an `S`-module `M`; here `M = M_λ = S'_λ` throughout (the presentation of `M`
over `S'` may be taken to be `(S')^{⊕0} → (S')^{⊕1} → M → 0`, which is why
`NoetherianApproxSystem` has three towers and no module), so "module" and "top ring"
coincide and the datum collapses to a tower `C_λ → D_λ` with `M_λ = D_λ`.  The two
applications differ only in what `C` and `D` are:

* **first application**: `C = Base`, `D = Tot`.  In Stacks' notation the pair is
  `(R_λ → S'_λ, M_λ = S'_λ)`, i.e. the source's `S` is our `Tot` and NOT our `Mid`;
* **second application**: `C i = Mid i ⧸ 𝔭_i`, `D i = Tot i ⧸ 𝔭_i`, the fibre system.

**WHY `isLocalizationDT` IS THE SHAPE IT IS.**  10.128.3 ends by invoking the
relative local criterion [Stacks 00MO] (Lemma 10.99.14), whose hypothesis (1) is
"`S'` is a localization of `S ⊗_R R'`" for the square `R → R'`, `S → S'`.  At
`λ ≤ μ` that square is `C_λ → C_μ`, `D_λ → D_μ`, so the hypothesis reads "`D_μ` is a
localization of `C_μ ⊗_{C_λ} D_λ`" — which is exactly the field below, and exactly
why `NoetherianApproxSystem.isLocalizationTotBaseT` exists as a field: the first
application discharges it VERBATIM (`isLocalizationDT h := sys.isLocalizationTotBaseT h`,
no transport).  For the fibre system it is the quotient of `isLocalizationTotT`, which
is the leaf `exists_isLocalization_fibre`.

**WHY THE CORE IS STILL A SORRY — CORRECTED 2026-07-28, AND THE GATE IS FAR SMALLER
THAN THIS PARAGRAPH USED TO CLAIM.**  The previous version of this paragraph said
10.128.3 is blocked until someone builds `Tor_1` and its six-term long exact
sequence, and named `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean` as this
leaf's natural prerequisite ("one prover closes both").  **That was wrong when it was
written, and the refuting check is one grep in this very file.**  00MO's proof
invokes **Lemma 10.99.10**, and 10.99.10 is ALREADY PROVEN here as
`flat_of_rTensor_injective_of_flat_quotientMap`, roughly 1400 lines above — and as of
the 2026-07-29 release it is proven **sorry-free**, because its former leaf
`lTensor_subtype_injective_of_pow_le` has since been closed too.  (10.99.10's own
docstring used to say only "PROVEN over the single leaf
`lTensor_subtype_injective_of_pow_le`", which read as though that leaf were still
open; corrected 2026-07-29 to say **PROVEN SORRY-FREE**.)

Reading 00MO's proof line by line against that, the ONLY content it needs beyond
10.99.10 is:

* `M'/I'M'` is flat over `R'/I'` — base change of the flat `M/IM` along
  `R/I → R'/I'`, followed by a localization.  **No `Tor` appears anywhere in this
  step**; and
* surjectivity of `Tor_1^R(M, R/I) ⊗_R R' → Tor_1^{R'}(M', R'/I')`, which is
  10.99.13 (`Tor_1^R(M, R'/I') ↠ Tor_1^{R'}(M ⊗_R R', R'/I')`) composed with 10.99.12
  at `R → R/I → R'/I'`, then localized.

Throughout, `Tor_1(−, R/I) = ker(I ⊗ − → −)` (Remark 10.75.9), so **not one of these
steps needs a derived functor, a projective resolution, or a long exact sequence** —
they are all statements about kernels of explicit `TensorProduct.lift`s.  10.128.3 is
therefore cut below into exactly TWO leaves over the already-proven 10.99.10,
`exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem` and
`flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem`; read their
docstrings, which are the specifications.

**STATUS 2026-07-29/30: the SECOND of those two leaves is now PROVEN**, over the three
general ring-level lemmas in the block immediately below this section note
(`flat_quotMap_tensorProduct_of_isMaximal`, `flat_quotMap_of_isLocalization`,
`flat_quotMap_map_of_isLocalization_tensorProduct`) — exactly the first bullet above, and
exactly as predicted, with no `Tor`, no Noetherian hypothesis and no colimit.  So the
heading of this paragraph now overstates the gate: **the only open leaf of 10.128.3 is the
colimit half** `exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem`,
i.e. the second bullet above.  Do not dispatch anyone at the fibre half.

**The `LocalCriterion.lean` coupling is WITHDRAWN.**
`Module.Flat.of_flat_quotient_of_pow_eq_bot` there is a genuinely different statement
— a NILPOTENT ideal and no Noetherian hypothesis, which is exactly the case
10.99.10's Artin–Rees/Krull proof does not cover and does not need — so it is not a
prerequisite for this leaf and this leaf is not a prerequisite for it.  Neither
closes the other.

**FAITHFULNESS OF THE PREDICATE.**  Every field is one of 10.127.13's conclusions or
one of 10.99.14's hypotheses, so `IsNoetherianFlatDescentSystem` is no stronger than
what the source has in hand when it applies 10.128.3, and both instances below are
PROVEN (the `baseTot` one outright, the fibre one over three named leaves).  Nothing
is asked for that no application can supply — which is the check a hypothesis-side
datum has to pass, and the reason the fields were chosen by walking 00R6's and 00MO's
proofs rather than by copying `NoetherianApproxSystem`.

**AXIS SEARCHED.**  Whether the two 10.128.3 applications share a statement.  NOT
searched: whether the module `M` can be reinstated as a fourth carrier so that this
predicate covers 10.128.3 in full generality rather than at `M = S'` — it can, and it
is what a mathlib-facing version should do, but nothing in this development needs it.

**THE CHECK THAT WOULD REFUTE THIS CUT.**  Exhibit an
`IsNoetherianFlatDescentSystem` with `w` flat for which no `j ≥ i` has `cd j` flat.
By 10.128.3 that is a refutation of the source, so the real risk is the opposite one:
a field that no application can supply.  Both applications below are written out, so
that risk is discharged by the compiler rather than by argument.

[Stacks 00R6]: https://stacks.math.columbia.edu/tag/00R6
[Stacks 00MO]: https://stacks.math.columbia.edu/tag/00MO
[Stacks 00ML]: https://stacks.math.columbia.edu/tag/00ML
-/

/-- **THE DATUM 10.128.3 RUNS ON, as a predicate over explicitly given data** — a
filtered system of NOETHERIAN LOCAL rings `C i → D i` whose colimit is `w : Cbot →+* Dbot`,
with `D` a localization of `C`-base-change along the transitions.

Read the section note above for why this exists and why it has two towers rather than
three.  In Stacks' notation `C i = R_λ`, `D i = S'_λ = M_λ`, `Cbot = R`, `Dbot = S' = M`.

**WHY A PREDICATE OVER GIVEN DATA and not a bundled structure.**  Both consumers must
land their conclusion ON THE NOSE — leaf 2's goal is an `Ideal.quotientMap`, written out
— and a bundled structure would force a transport of `RingHom.Flat` along an
isomorphism of carriers.  Here the carriers ARE the quotients, so `cd j` is
syntactically the map the leaf asks about.

**FAITHFULNESS, field by field.**  Each is either a conclusion of 10.127.13 (hence
available in any `NoetherianApproxSystem`, which is what the first application uses) or
a hypothesis of [Stacks 00MO], which is what 10.128.3's endgame invokes:

* `le_rfl`, `le_trans'`, `directed` — `Λ` is a filtered index set;
* `isLocalRingC`, `isLocalRingD`, `isNoetherianC`, `isNoetherianD`, `isLocalHomCD` —
  00MO asks for local homomorphisms of local NOETHERIAN rings.  `isNoetherianD` is
  additionally what makes `ker(𝔪_λ ⊗_{C_λ} D_λ → D_λ)` finitely generated, which is the
  first line of 00R6's proof;
* `cT_comp`, `dT_comp`, `comm_T`, `comm_cocone`, `comm_cToC`, `comm_dToD` — functoriality
  and the cocone, i.e. "the colimit of the system is `w`";
* `isLocalHomCT`, `isLocalHomDT`, `isLocalHomCToC`, `isLocalHomDToD` — 10.127.11's system
  is one of local rings and local homomorphisms, structure maps included;
* `c_surj`, `d_surj`, `c_sep`, `d_sep` — the ordinary characterisation of a filtered
  colimit, and what 00R6's "tensor products commute with colimits" step consumes;
* `isLocalizationDT` — hypothesis (1) of [Stacks 00MO]; see the section note.

**NON-DEGENERACY.**  The one-object system `Λ = PUnit`, `C = D = Cbot = Dbot` satisfies
every structural field but demands `IsNoetherianRing Cbot`, which is exactly the junk
stage 00R7 is trying to avoid; and a constant system on a Noetherian subring fails
`c_surj`. -/
structure IsNoetherianFlatDescentSystem {Λ : Type u} (le : Λ → Λ → Prop)
    (C D : Λ → Type u) [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    (cd : ∀ i, C i →+* D i)
    (cT : ∀ {i j : Λ}, le i j → (C i →+* C j))
    (dT : ∀ {i j : Λ}, le i j → (D i →+* D j))
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] (w : Cbot →+* Dbot)
    (cToC : ∀ i, C i →+* Cbot) (dToD : ∀ i, D i →+* Dbot) : Prop where
  /-- `le` is reflexive. -/
  le_rfl : ∀ i, le i i
  /-- `le` is transitive. -/
  le_trans' : ∀ {i j k}, le i j → le j k → le i k
  /-- `Λ` is directed. -/
  directed : ∀ i j, ∃ k, le i k ∧ le j k
  /-- Each `R_λ` is local. -/
  isLocalRingC : ∀ i, IsLocalRing (C i)
  /-- Each `S'_λ` is local. -/
  isLocalRingD : ∀ i, IsLocalRing (D i)
  /-- Each `R_λ` is Noetherian. -/
  isNoetherianC : ∀ i, IsNoetherianRing (C i)
  /-- Each `S'_λ` is Noetherian.  This is what makes `Tor_1^{R_λ}(M_λ, R_λ/𝔪_λ)`
  finitely generated in 10.128.3. -/
  isNoetherianD : ∀ i, IsNoetherianRing (D i)
  /-- `R_λ → S'_λ` is local. -/
  isLocalHomCD : ∀ i, IsLocalHom (cd i)
  /-- The `C` transitions are functorial. -/
  cT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (cT h₂).comp (cT h₁) = cT (le_trans' h₁ h₂)
  /-- The `D` transitions are functorial. -/
  dT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
    (dT h₂).comp (dT h₁) = dT (le_trans' h₁ h₂)
  /-- The vertical maps are natural in `Λ`. -/
  comm_T : ∀ {i j} (h : le i j), (cd j).comp (cT h) = (dT h).comp (cd i)
  /-- The `C` transitions are local. -/
  isLocalHomCT : ∀ {i j} (h : le i j), IsLocalHom (cT h)
  /-- The `D` transitions are local. -/
  isLocalHomDT : ∀ {i j} (h : le i j), IsLocalHom (dT h)
  /-- The square `C i → D i → Dbot` / `C i → Cbot → Dbot` commutes. -/
  comm_cocone : ∀ i, (dToD i).comp (cd i) = w.comp (cToC i)
  /-- `cToC` is a cocone. -/
  comm_cToC : ∀ {i j} (h : le i j), (cToC j).comp (cT h) = cToC i
  /-- `dToD` is a cocone. -/
  comm_dToD : ∀ {i j} (h : le i j), (dToD j).comp (dT h) = dToD i
  /-- The `C` cocone maps are local. -/
  isLocalHomCToC : ∀ i, IsLocalHom (cToC i)
  /-- The `D` cocone maps are local. -/
  isLocalHomDToD : ∀ i, IsLocalHom (dToD i)
  /-- `Cbot` is the colimit, half one. -/
  c_surj : ∀ x : Cbot, ∃ i, ∃ y : C i, cToC i y = x
  /-- `Dbot` is the colimit, half one. -/
  d_surj : ∀ x : Dbot, ∃ i, ∃ y : D i, dToD i y = x
  /-- `Cbot` is the colimit, half two. -/
  c_sep : ∀ i (x y : C i), cToC i x = cToC i y → ∃ j, ∃ h : le i j, cT h x = cT h y
  /-- `Dbot` is the colimit, half two. -/
  d_sep : ∀ i (x y : D i), dToD i x = dToD i y → ∃ j, ∃ h : le i j, dT h x = dT h y
  /-- **Hypothesis (1) of [Stacks 00MO]**: `D_μ` is a localization of `C_μ ⊗_{C_λ} D_λ`.
  See the section note for why this, and not an isomorphism, is what the source gives. -/
  isLocalizationDT : ∀ {i j} (h : le i j),
    letI : Algebra (C i) (D i) := (cd i).toAlgebra
    letI : Algebra (C i) (C j) := (cT h).toAlgebra
    letI : Algebra (C i) (D j) := ((cd j).comp (cT h)).toAlgebra
    letI : Algebra (C j) (D j) := (cd j).toAlgebra
    letI : Algebra (D i) (D j) := (dT h).toAlgebra
    haveI : IsScalarTower (C i) (C j) (D j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (C i) (D i) (D j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (comm_T h) x
    letI : Algebra (C j ⊗[C i] D i) (D j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (C i) (C j) (D j))
        (IsScalarTower.toAlgHom (C i) (D i) (D j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (C j ⊗[C i] D i), IsLocalization W (D j)


/-! #### THE RING-LEVEL INPUTS OF 00MO's STEP 2 — three general lemmas, added 2026-07-29

The fibre half of 10.128.3 needs no descent system at all: it is a statement about a single
square `C_i → C_j`, `D_i → D_j` with `D_j` a localization of `C_j ⊗_{C_i} D_i`.  The three
lemmas below say so, in that generality, and
`flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem` is one `exact` over the
last of them.  None of them mentions `Tor`, Noetherianness, or a colimit — see the
"WHY THE CORE IS STILL A SORRY" paragraph in the section note above, which predicted exactly
this and has now been discharged for this half. -/

/-- **BASE CHANGE OF A FIBRE ALONG A QUOTIENT — the ring-level heart of 00MO's step 2.**

*If `𝔪` is a maximal ideal of `Ci`, then `(Cj ⊗[Ci] Di) ⧸ 𝔪(Cj ⊗[Ci] Di)` is FLAT over
`Cj ⧸ 𝔪 Cj`.*

The proof is the three-line argument of [Stacks 00MO]'s step 2, with no `Tor` anywhere:
`k := Ci ⧸ 𝔪` is a FIELD, so the `k`-module `k ⊗[Ci] Di` is free hence flat; base change
along `k → Cj ⧸ 𝔪 Cj` keeps it flat; and the three tensor identities
`(Cj ⧸ I') ⊗[k] (k ⊗[Ci] Di) ≅ (Cj ⧸ I') ⊗[Ci] Di ≅ (Cj ⧸ I') ⊗[Cj] (Cj ⊗[Ci] Di) ≅
(Cj ⊗[Ci] Di) ⧸ I'(Cj ⊗[Ci] Di)` are `Algebra.TensorProduct.cancelBaseChange` twice and
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor` once.

Maximality of `𝔪` is what makes `Ci ⧸ 𝔪` a field and is the ONLY hypothesis: no
Noetherian, finiteness or flatness assumption on `Cj` or `Di` is used. -/
theorem flat_quotMap_tensorProduct_of_isMaximal
    {Ci Cj Di : Type*} [CommRing Ci] [CommRing Cj] [CommRing Di]
    [Algebra Ci Cj] [Algebra Ci Di] (𝔪 : Ideal Ci) [𝔪.IsMaximal] :
    Module.Flat (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      ((Cj ⊗[Ci] Di) ⧸ (𝔪.map (algebraMap Ci Cj)).map
        (algebraMap Cj (Cj ⊗[Ci] Di))) := by
  letI : Field (Ci ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Flat (Ci ⧸ 𝔪) ((Ci ⧸ 𝔪) ⊗[Ci] Di) := Module.Flat.of_free
  haveI : Module.Flat (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      ((Cj ⧸ 𝔪.map (algebraMap Ci Cj)) ⊗[Ci ⧸ 𝔪] ((Ci ⧸ 𝔪) ⊗[Ci] Di)) :=
    Module.Flat.baseChange (Ci ⧸ 𝔪) (Cj ⧸ 𝔪.map (algebraMap Ci Cj)) ((Ci ⧸ 𝔪) ⊗[Ci] Di)
  haveI : Module.Flat (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      ((Cj ⧸ 𝔪.map (algebraMap Ci Cj)) ⊗[Ci] Di) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.cancelBaseChange Ci (Ci ⧸ 𝔪)
        (Cj ⧸ 𝔪.map (algebraMap Ci Cj)) (Cj ⧸ 𝔪.map (algebraMap Ci Cj)) Di).symm.toLinearEquiv
  haveI : Module.Flat (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      ((Cj ⧸ 𝔪.map (algebraMap Ci Cj)) ⊗[Cj] (Cj ⊗[Ci] Di)) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.cancelBaseChange Ci Cj
        (Cj ⧸ 𝔪.map (algebraMap Ci Cj)) (Cj ⧸ 𝔪.map (algebraMap Ci Cj)) Di).toLinearEquiv
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Cj ⊗[Ci] Di)
      (𝔪.map (algebraMap Ci Cj))).toLinearEquiv

/-- **A QUOTIENT OF A LOCALIZATION IS A LOCALIZATION OF THE QUOTIENT, hence FLAT over it.**

*If `Dj` is the localization of `E` at `W` and `J = I Dj` for an ideal `I` of `E`, then
`Dj ⧸ J` is flat over `E ⧸ I`.*

`IsLocalization.of_surjective` upgrades `IsLocalization W Dj` along the two quotient maps to
`IsLocalization (W.map (Ideal.Quotient.mk I)) (Dj ⧸ J)`, and `IsLocalization.flat` concludes.
Stating `J` as a separate ideal together with `hJ` — rather than writing
`I.map (algebraMap E Dj)` in the conclusion — is what lets the consumer below apply this at an
ideal that is only PROPOSITIONALLY equal to the extension, with no transport. -/
theorem flat_quotMap_of_isLocalization {E Dj : Type*} [CommRing E] [CommRing Dj] [Algebra E Dj]
    (W : Submonoid E) [IsLocalization W Dj] (I : Ideal E) (J : Ideal Dj)
    [Algebra (E ⧸ I) (Dj ⧸ J)]
    (halg : (Ideal.Quotient.mk J).comp (algebraMap E Dj)
      = (algebraMap (E ⧸ I) (Dj ⧸ J)).comp (Ideal.Quotient.mk I))
    (hJ : J = I.map (algebraMap E Dj)) :
    Module.Flat (E ⧸ I) (Dj ⧸ J) := by
  haveI : IsLocalization (W.map (Ideal.Quotient.mk I)) (Dj ⧸ J) :=
    IsLocalization.of_surjective W Dj (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective halg (by simpa using hJ.le)
  exact IsLocalization.flat (Dj ⧸ J) (W.map (Ideal.Quotient.mk I))

/-- **[Stacks 00MO] STEP 2, at the ring level** — the whole fibre half of 10.128.3, with the
descent system replaced by the three maps it actually spends.

*If `Dj` is a localization of `Cj ⊗[Ci] Di` over `Cj`, and `𝔪` is a maximal ideal of `Ci`, then
`Dj ⧸ 𝔪 Dj` is FLAT over `Cj ⧸ 𝔪 Cj`.*

The factorisation is `Cj ⧸ 𝔪Cj → (Cj ⊗[Ci] Di) ⧸ 𝔪(Cj ⊗[Ci] Di) → Dj ⧸ 𝔪Dj`: the first map is
flat by `flat_quotMap_tensorProduct_of_isMaximal` (base change from the residue FIELD of `𝔪`)
and the second by `flat_quotMap_of_isLocalization` (a localization), so `Module.Flat.trans`
finishes.  Nothing here is Noetherian and nothing is a colimit — that content lives entirely in
the OTHER half of 10.128.3. -/
theorem flat_quotMap_map_of_isLocalization_tensorProduct
    {Ci Cj Di Dj : Type*} [CommRing Ci] [CommRing Cj] [CommRing Di] [CommRing Dj]
    [Algebra Ci Cj] [Algebra Ci Di] [Algebra Cj Dj]
    [Algebra (Cj ⊗[Ci] Di) Dj] [IsScalarTower Cj (Cj ⊗[Ci] Di) Dj]
    (W : Submonoid (Cj ⊗[Ci] Di)) [IsLocalization W Dj]
    (𝔪 : Ideal Ci) [𝔪.IsMaximal] :
    Module.Flat (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      (Dj ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj Dj)) := by
  have hJ : (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj Dj)
      = ((𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj (Cj ⊗[Ci] Di))).map
          (algebraMap (Cj ⊗[Ci] Di) Dj) := by
    conv_rhs => rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq Cj (Cj ⊗[Ci] Di) Dj]
  letI : Algebra ((Cj ⊗[Ci] Di) ⧸ (𝔪.map (algebraMap Ci Cj)).map
      (algebraMap Cj (Cj ⊗[Ci] Di)))
      (Dj ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj Dj)) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hJ.ge)
  haveI := flat_quotMap_of_isLocalization (Dj := Dj) W _ _ rfl hJ
  haveI := flat_quotMap_tensorProduct_of_isMaximal (Cj := Cj) (Di := Di) 𝔪
  haveI : IsScalarTower (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
      ((Cj ⊗[Ci] Di) ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj (Cj ⊗[Ci] Di)))
      (Dj ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj Dj)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [IsScalarTower.algebraMap_apply Cj (Cj ⊗[Ci] Di) Dj]
  exact Module.Flat.trans (Cj ⧸ 𝔪.map (algebraMap Ci Cj))
    ((Cj ⊗[Ci] Di) ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj (Cj ⊗[Ci] Di)))
    (Dj ⧸ (𝔪.map (algebraMap Ci Cj)).map (algebraMap Cj Dj))

/-! #### 10.128.3's TWO LEAVES — cut 2026-07-28 over the ALREADY-PROVEN 10.99.10

The three declarations below are one block and were written together.  The two leaves
are the two hypotheses of `flat_of_rTensor_injective_of_flat_quotientMap` (Stacks
10.99.10, PROVEN ~1400 lines above) at the ideal `I' = 𝔪_i C_j`, and the theorem after
them is 00MO's assembly.  Read the CORRECTED "WHY THE CORE IS STILL A SORRY" paragraph
in the section note above before touching any of them: the earlier claim that 10.128.3
is gated on building `Tor_1` and its long exact sequence is WITHDRAWN, and so is its
pairing with `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`. -/

/-! #### THE FURTHER CUT OF THE COLIMIT HALF — TAKEN 2026-07-30

The docstring below offered this cut in its own words ("**A FURTHER CUT IS AVAILABLE** if
this is too large for one owner: introduce the comparison map `T_i → T_j` as a named `def`
… and make Halves A and B two leaves over it"), and it is taken here for exactly the
reason it gave: the two halves share nothing but the map, and they want separate owners.

* `idealTensorComparison` is that map, `T_i → T_j` before restriction to the kernels:
  `↥𝔪 ⊗[Ci] Di → ↥(𝔪 Cj) ⊗[Cj] Dj`, `x ⊗ m ↦ (cT x) ⊗ (dT m)`.
* `exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem` is **HALF A**
  (00R6's own body: `T_i` is f.g., `w` is flat, tensor commutes with filtered colimits, so
  ONE `j ≥ i` kills every generator).  This is the ONLY consumer of `_hflat`,
  `c_surj`/`c_sep`/`d_surj`/`d_sep` and `directed` anywhere in 10.128.3.
* `ker_rTensor_le_span_image_idealTensorComparison_of_isNoetherianFlatDescentSystem` is
  **HALF B** (00MO's steps 4–6: Stacks 10.99.13 + 10.99.12, then localized along
  `isLocalizationDT h`, which is its only consumer).  It is the one genuinely homological
  statement left in 10.128.3.
* The parent is then PROVEN over the two: `T_j` is spanned by the image of `T_i` (Half B)
  and that image is `0` (Half A), so `T_j = ⊥`, which is `LinearMap.ker_eq_bot`.

**NOTE THE ASYMMETRY, because it is what makes the cut sound.** Half A is an `∃ j`; Half B
is `∀ i ≤ j`.  So Half B may be applied at whatever `j` Half A produces, and neither half
has to know the other's index.  Had Half B also been an `∃`, the two indices would not
have been reconcilable without a third directedness step.

**Half B does NOT need `φ` to carry `T_i` into `T_j`** — it says `T_j` lies in the `C_j`-span
of `φ(T_i)`, and the assembly needs nothing more, so no compatibility lemma is stated. (It
is true and easy — the square over `D_i → D_j` commutes — but an unconsumed lemma would be
free-floating, so its prover should state it locally.) -/

/-- The `C_i`-linear inclusion `↥𝔪 → ↥(𝔪 C_j)`, `x ↦ (algebraMap C_i C_j) x`, used only to
build `idealTensorComparison` below. -/
noncomputable def idealMapRestrict {Ci Cj : Type*} [CommRing Ci] [CommRing Cj]
    [Algebra Ci Cj] (𝔪 : Ideal Ci) :
    ↥𝔪 →ₗ[Ci] ↥(𝔪.map (algebraMap Ci Cj)) where
  toFun x := ⟨algebraMap Ci Cj x, Ideal.mem_map_of_mem _ x.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp [Algebra.smul_def]

/-- **THE COMPARISON MAP `T_i → T_j` OF [Stacks 00R6], before restricting to the kernels.**

`↥𝔪 ⊗[Ci] Di →ₗ[Ci] ↥(𝔪 Cj) ⊗[Cj] Dj`, sending `x ⊗ₜ m` to `(algebraMap Ci Cj x) ⊗ₜ
(algebraMap Di Dj m)`.  Under `Tor_1(−, C/I) = ker(I ⊗ − → −)` (Remark 10.75.9) its
restriction to kernels is the map `Tor_1^{C_i}(D_i, C_i/𝔪) → Tor_1^{C_j}(D_j, C_j/𝔪C_j)`
that Halves A and B of 10.128.3's colimit leaf are both statements about.

It is built as `mapOfCompatibleSMul ∘ TensorProduct.map`: first `x ⊗ₜ m ↦ (cT x) ⊗ₜ (dT m)`
into `↥(𝔪 Cj) ⊗[Ci] Dj` (a `TensorProduct.map` of two honestly `Ci`-linear maps), then the
canonical `Ci`-linear comparison `↥(𝔪 Cj) ⊗[Ci] Dj → ↥(𝔪 Cj) ⊗[Cj] Dj`.  Writing it that
way rather than as a `TensorProduct.lift` of a `mk₂` is what keeps the four bilinearity
side goals out of this file: they are `CompatibleSMul.isScalarTower`, i.e. the two
`IsScalarTower` hypotheses.

The two scalar-tower hypotheses are exactly what a descent system supplies at `i ≤ j`
(`IsScalarTower Ci Cj Dj` is `rfl`; `IsScalarTower Ci Di Dj` is `comm_T h`). -/
noncomputable def idealTensorComparison {Ci Cj Di Dj : Type*} [CommRing Ci] [CommRing Cj]
    [CommRing Di] [CommRing Dj] [Algebra Ci Cj] [Algebra Ci Di] [Algebra Ci Dj]
    [Algebra Cj Dj] [Algebra Di Dj] [IsScalarTower Ci Cj Dj] [IsScalarTower Ci Di Dj]
    (𝔪 : Ideal Ci) :
    (↥𝔪 ⊗[Ci] Di) →ₗ[Ci] (↥(𝔪.map (algebraMap Ci Cj)) ⊗[Cj] Dj) :=
  (TensorProduct.mapOfCompatibleSMul Cj Ci Ci (↥(𝔪.map (algebraMap Ci Cj))) Dj).comp
    (TensorProduct.map (idealMapRestrict 𝔪) (IsScalarTower.toAlgHom Ci Di Dj).toLinearMap)

/-! ### The finite descent toolkit of a `IsNoetherianFlatDescentSystem`

The six lemmas below are the whole content of the four `surj`/`sep` fields in the form
Half A of 10.128.3's colimit leaf uses them: a FINITE family of elements of `Cbot`/`Dbot`
comes from one stage, and a FINITE family of equations true in `Cbot`/`Dbot` becomes true
at one stage.  Each is `directed` applied finitely often, which is
`exists_le_of_fintype`.  They are consumed only by
`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem` below. -/

namespace IsNoetherianFlatDescentSystem

section Descent

variable {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)

include hsys

/-- Finitely many indices, together with a base index `i`, have a common upper bound. -/
theorem exists_le_of_fintype {ι : Type*} [Fintype ι] (i : Λ) (j : ι → Λ) :
    ∃ j₀ : Λ, le i j₀ ∧ ∀ x, le (j x) j₀ := by
  classical
  have key : ∀ s : Finset ι, ∃ j₀ : Λ, le i j₀ ∧ ∀ x ∈ s, le (j x) j₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨i, hsys.le_rfl i, by simp⟩
    | insert x s hx ih =>
        obtain ⟨j₀, hi₀, h₀⟩ := ih
        obtain ⟨k, hk₁, hk₂⟩ := hsys.directed (j x) j₀
        refine ⟨k, hsys.le_trans' hi₀ hk₂, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hk₁
        · exact hsys.le_trans' (h₀ y hy) hk₂
  obtain ⟨j₀, hi₀, h₀⟩ := key Finset.univ
  exact ⟨j₀, hi₀, fun x => h₀ x (Finset.mem_univ x)⟩

/-- Any finite family of elements of `Cbot` comes from a single stage above `i`. -/
theorem exists_eq_cToC_of_fintype (i : Λ) {ι : Type} [Fintype ι] (x : ι → Cbot) :
    ∃ j : Λ, ∃ _ : le i j, ∃ y : ι → C j, ∀ t, cToC j (y t) = x t := by
  classical
  choose iq zq hzq using fun t => hsys.c_surj (x t)
  obtain ⟨j, hij, hj⟩ := hsys.exists_le_of_fintype i iq
  refine ⟨j, hij, fun t => cT (hj t) (zq t), fun t => ?_⟩
  rw [← hzq t, ← DFunLike.congr_fun (hsys.comm_cToC (hj t)) (zq t)]
  rfl

/-- Any finite family of elements of `Dbot` comes from a single stage above `i`. -/
theorem exists_eq_dToD_of_fintype (i : Λ) {ι : Type} [Fintype ι] (x : ι → Dbot) :
    ∃ j : Λ, ∃ _ : le i j, ∃ y : ι → D j, ∀ t, dToD j (y t) = x t := by
  classical
  choose iq zq hzq using fun t => hsys.d_surj (x t)
  obtain ⟨j, hij, hj⟩ := hsys.exists_le_of_fintype i iq
  refine ⟨j, hij, fun t => dT (hj t) (zq t), fun t => ?_⟩
  rw [← hzq t, ← DFunLike.congr_fun (hsys.comm_dToD (hj t)) (zq t)]
  rfl

/-- Both a finite family in `Cbot` and one in `Dbot`, from ONE stage above `i`. -/
theorem exists_eq_cToC_dToD_of_fintype (i : Λ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → Cbot) (z : κ → Dbot) :
    ∃ j : Λ, ∃ _ : le i j, ∃ (y : ι → C j) (u : κ → D j),
      (∀ t, cToC j (y t) = x t) ∧ (∀ t, dToD j (u t) = z t) := by
  obtain ⟨j1, h1, y1, hy1⟩ := hsys.exists_eq_cToC_of_fintype i x
  obtain ⟨j2, h2, u2, hu2⟩ := hsys.exists_eq_dToD_of_fintype j1 z
  refine ⟨j2, hsys.le_trans' h1 h2, fun t => cT h2 (y1 t), u2, fun t => ?_, hu2⟩
  rw [← hy1 t]
  exact DFunLike.congr_fun (hsys.comm_cToC h2) (y1 t)

/-- A finite family of equations that becomes true in `Cbot` becomes true at a finite
stage. -/
theorem exists_cT_eq_of_fintype (i : Λ) {ι : Type} [Fintype ι] (x y : ι → C i)
    (h : ∀ t, cToC i (x t) = cToC i (y t)) :
    ∃ j : Λ, ∃ hij : le i j, ∀ t, cT hij (x t) = cT hij (y t) := by
  classical
  choose jq hjq hxy using fun t => hsys.c_sep i (x t) (y t) (h t)
  obtain ⟨j, hij, hj⟩ := hsys.exists_le_of_fintype i jq
  refine ⟨j, hij, fun t => ?_⟩
  have e : ∀ z : C i, cT hij z = cT (hj t) (cT (hjq t) z) := fun z =>
    (DFunLike.congr_fun (hsys.cT_comp (hjq t) (hj t)) z).symm
  rw [e (x t), e (y t), hxy t]

/-- A finite family of equations that becomes true in `Dbot` becomes true at a finite
stage. -/
theorem exists_dT_eq_of_fintype (i : Λ) {ι : Type} [Fintype ι] (x y : ι → D i)
    (h : ∀ t, dToD i (x t) = dToD i (y t)) :
    ∃ j : Λ, ∃ hij : le i j, ∀ t, dT hij (x t) = dT hij (y t) := by
  classical
  choose jq hjq hxy using fun t => hsys.d_sep i (x t) (y t) (h t)
  obtain ⟨j, hij, hj⟩ := hsys.exists_le_of_fintype i jq
  refine ⟨j, hij, fun t => ?_⟩
  have e : ∀ z : D i, dT hij z = dT (hj t) (dT (hjq t) z) := fun z =>
    (DFunLike.congr_fun (hsys.dT_comp (hjq t) (hj t)) z).symm
  rw [e (x t), e (y t), hxy t]

end Descent

end IsNoetherianFlatDescentSystem

/-- **THE PURE BILINEARITY STEP of Half A, with all the descent data already supplied.**

`a` generates `𝔪`; `g` generates the syzygies over `Di` of the images
`(algebraMap Ci Di) (a l)` (that is what `hg` says); and each generating syzygy `g r` is,
after transport to `Dj`, factored through `Cj`-coefficients `b r` and `Dj`-elements `y r`,
whose own relation with `a` is `hb`.  Then `idealTensorComparison 𝔪` kills the whole
kernel `T_i = ker(↥𝔪 ⊗_{Ci} Di → Di)`.

No flatness and no colimit occurs here — this is bookkeeping over `TensorProduct`, which
is precisely the point of the cut: flatness enters only through the equational criterion,
in the caller, and is spent before this lemma is reached. -/
theorem idealTensorComparison_eq_zero_of_syzygy_descent
    {Ci Cj Di Dj : Type*} [CommRing Ci] [CommRing Cj] [CommRing Di] [CommRing Dj]
    [Algebra Ci Cj] [Algebra Ci Di] [Algebra Ci Dj] [Algebra Cj Dj] [Algebra Di Dj]
    [IsScalarTower Ci Cj Dj] [IsScalarTower Ci Di Dj]
    (𝔪 : Ideal Ci) {p : ℕ} (a : Fin p → Ci)
    (ha : Submodule.span Ci (Set.range a) = 𝔪)
    {m : ℕ} (g : Fin m → Fin p → Di)
    (hg : ∀ d : Fin p → Di, (∑ l, algebraMap Ci Di (a l) * d l = 0) →
        ∃ c : Fin m → Di, ∀ l, d l = ∑ r, c r * g r l)
    {κ : Fin m → Type} [∀ r, Fintype (κ r)]
    (b : ∀ r, Fin p → κ r → Cj) (y : ∀ r, κ r → Dj)
    (hb : ∀ r (s : κ r), ∑ l, algebraMap Ci Cj (a l) * b r l s = 0)
    (hy : ∀ r l, algebraMap Di Dj (g r l) = ∑ s, algebraMap Cj Dj (b r l s) * y r s) :
    ∀ t ∈ LinearMap.ker (LinearMap.rTensor Di 𝔪.subtype),
      idealTensorComparison (Cj := Cj) (Dj := Dj) 𝔪 t = 0 := by
  classical
  have hmem : ∀ l, a l ∈ 𝔪 := fun l => ha ▸ Submodule.subset_span ⟨l, rfl⟩
  set A : Fin p → ↥𝔪 := fun l => ⟨a l, hmem l⟩ with hA
  set Aj : Fin p → ↥(𝔪.map (algebraMap Ci Cj)) :=
    fun l => ⟨algebraMap Ci Cj (a l), Ideal.mem_map_of_mem _ (hmem l)⟩ with hAj
  -- the comparison map on a pure tensor built from a generator
  have hcomp : ∀ (l : Fin p) (z : Di),
      idealTensorComparison (Cj := Cj) (Dj := Dj) 𝔪 (A l ⊗ₜ[Ci] z)
        = Aj l ⊗ₜ[Cj] algebraMap Di Dj z := by
    intro l z
    simp [idealTensorComparison, idealMapRestrict, hA, hAj]
  -- every element of `↥𝔪 ⊗ Di` is a combination of the `A l`
  have claimS : ∀ t : ↥𝔪 ⊗[Ci] Di, ∃ d : Fin p → Di, t = ∑ l, A l ⊗ₜ[Ci] d l := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x n =>
        have hxm : x.1 ∈ Submodule.span Ci (Set.range a) := by rw [ha]; exact x.2
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ci).mp hxm
        refine ⟨fun l => c l • n, ?_⟩
        have hx : x = ∑ l, c l • A l := by
          apply Subtype.ext
          simpa [hA] using hc.symm
        rw [hx, TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    | add x z hx hz =>
        obtain ⟨dx, hdx⟩ := hx
        obtain ⟨dz, hdz⟩ := hz
        exact ⟨dx + dz, by
          simp only [hdx, hdz, Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  -- and such a combination lies in the kernel exactly when its coefficients are a syzygy
  have claimK : ∀ d : Fin p → Di,
      (∑ l, A l ⊗ₜ[Ci] d l) ∈ LinearMap.ker (LinearMap.rTensor Di 𝔪.subtype) →
      ∑ l, algebraMap Ci Di (a l) * d l = 0 := by
    intro d hd
    have h0 : (TensorProduct.lid Ci Di)
        (LinearMap.rTensor Di 𝔪.subtype (∑ l, A l ⊗ₜ[Ci] d l)) = 0 := by
      rw [LinearMap.mem_ker.mp hd]; simp
    simpa [map_sum, hA, Algebra.smul_def] using h0
  -- ## the heart: each generating syzygy is killed, with an arbitrary `Dj`-multiplier
  have hgen : ∀ (r : Fin m) (u : Dj),
      ∑ l, Aj l ⊗ₜ[Cj] (u * algebraMap Di Dj (g r l)) = 0 := by
    intro r u
    have step : ∀ l, u * algebraMap Di Dj (g r l) = ∑ s, b r l s • (u * y r s) := by
      intro l
      rw [hy r l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Algebra.smul_def]
      ring
    have e1 : ∀ l, Aj l ⊗ₜ[Cj] (u * algebraMap Di Dj (g r l))
        = ∑ s, (b r l s • Aj l) ⊗ₜ[Cj] (u * y r s) := by
      intro l
      rw [step l, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [Finset.sum_congr rfl fun l _ => e1 l, Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← TensorProduct.sum_tmul]
    have hz : (∑ l, b r l s • Aj l) = 0 := by
      refine Subtype.ext ?_
      have hcoe : ((∑ l, b r l s • Aj l : ↥(𝔪.map (algebraMap Ci Cj))) : Cj)
          = ∑ l, b r l s * algebraMap Ci Cj (a l) := by
        simp [hAj]
      rw [hcoe, ZeroMemClass.coe_zero, ← hb r s]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hz, TensorProduct.zero_tmul]
  -- ## assembly
  intro t ht
  obtain ⟨d, hd⟩ := claimS t
  have hker : ∑ l, algebraMap Ci Di (a l) * d l = 0 := by
    refine claimK d ?_
    rw [← hd]; exact ht
  obtain ⟨c, hc⟩ := hg d hker
  have e2 : ∀ l, idealTensorComparison (Cj := Cj) (Dj := Dj) 𝔪 (A l ⊗ₜ[Ci] d l)
      = ∑ r, Aj l ⊗ₜ[Cj] (algebraMap Di Dj (c r) * algebraMap Di Dj (g r l)) := by
    intro l
    rw [hcomp l (d l), hc l, map_sum, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul]
  rw [hd, map_sum, Finset.sum_congr rfl fun l _ => e2 l, Finset.sum_comm]
  exact Finset.sum_eq_zero fun r _ => hgen r (algebraMap Di Dj (c r))

/-- **HALF A OF [Stacks 00R6]'s COLIMIT LEAF — the colimit step, and it needs no `Tor`**
(PROVEN 2026-07-30 along the "ROUTE FINDING" note below; cut 2026-07-30 out of
`exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem` below;
read that docstring's "Half A" paragraph, which is this leaf's specification).

*In a `IsNoetherianFlatDescentSystem` whose colimit `w` is flat, for every `i` there is
`j ≥ i` at which the comparison map `idealTensorComparison 𝔪_i` KILLS
`T_i = ker(𝔪_i ⊗_{C_i} D_i → C_i ⊗_{C_i} D_i)`.*

**THE PROOF** (00R6's own first paragraph, verbatim).  `𝔪_i` is f.g. because `C i` is
Noetherian (`isNoetherianC`), so `↥𝔪_i ⊗_{C_i} D_i` is a finite `D_i`-module
(`Module.Finite.base_change`), so its submodule `T_i` is f.g. because `D i` is Noetherian
(`isNoetherianD`).  Let `ξ_1, …, ξ_n` generate it.  `w` is flat, so
`↥(𝔪_i Cbot) ⊗_{Cbot} Dbot → Cbot ⊗_{Cbot} Dbot` is injective — the flat base change of
the injection `↥(𝔪_i Cbot) ↪ Cbot` — and each `ξ_k` therefore dies in
`↥(𝔪_i Cbot) ⊗_{Cbot} Dbot`.  Tensor products commute with filtered colimits, so each
`ξ_k` already dies at some finite stage, and `directed` merges the `n` stages into one `j`.
`c_surj`, `c_sep`, `d_surj`, `d_sep` and `directed` are spent HERE and nowhere else in
10.128.3, and so is `_hflat`.

**ROUTE FINDING 2026-07-30 — DO NOT BUILD THE COLIMIT THEORY THE PARAGRAPH ABOVE
SUGGESTS.**  "Tensor products commute with filtered colimits" is a true sentence and a
trap: taken literally it asks for
`colim_j (↥(𝔪_i C_j) ⊗_{C_j} D_j) ≅ ↥(𝔪_i Cbot) ⊗_{Cbot} Dbot`, over a system whose BASE
RING varies, from a datum that carries only the four `surj`/`sep` fields — and mathlib's
`Module.DirectLimit` is for a FIXED base ring, so none of
`Mathlib/Algebra/Colimit/TensorProduct.lean`,
`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean` or
`Mathlib/RingTheory/TensorProduct/DirectLimitFG.lean` applies off the shelf.  **That whole
detour is avoidable**, and what avoids it is the EQUATIONAL CRITERION OF FLATNESS, which
is in the pin:

    Module.isTrivialRelation_of_sum_smul_eq_zero      -- Mathlib/RingTheory/Flat/
      [Flat R M] {ι} [Fintype ι] {f : ι → R} {x : ι → M}   --   EquationalCriterion.lean
      (h : ∑ i, f i • x i = 0) : Module.IsTrivialRelation f x

whose conclusion unfolds to `∃ k (b : ι → Fin k → R) (y : Fin k → M)`, with
`x l = ∑ s, b l s • y s` and `∑ l, f l * b l s = 0`.  Note it is stated for a flat
MODULE, and `_hflat : w.Flat` is by definition `Module.Flat Cbot Dbot` along
`w.toAlgebra`, so it applies directly with no reformulation.

The route, in the order it should be written:

1. Take `a : Fin p → C i` generating `𝔪_i` (`isNoetherianC`, then
   `Submodule.fg_iff_exists_fin_generating_family`).  Then `↥(𝔪_i C_j)` is generated over
   `C_j` by the `cT h (a l)`, at EVERY `j` including the bottom — that uniformity is what
   makes one family of indices do for the whole argument.
2. Reduce to relations.  Put `Syz := ker((Fin p → D i) →ₗ[D i] D i)` for
   `d ↦ ∑ l, (cd i) (a l) * d l`.  `Syz` is f.g. because `D i` is Noetherian
   (`isNoetherianD`) — no `Module.Finite.base_change` needed — and `T_i` is exactly the
   image of `Syz` under `d ↦ ∑ l, ⟨a l⟩ ⊗ₜ d l`, because the `⟨a l⟩ ⊗ₜ 1` generate
   `↥𝔪_i ⊗_{C_i} D_i` over `D_i`.  So it suffices to kill the finitely many GENERATORS of
   `Syz`, and `idealTensorComparison` is semilinear along `dT h`
   (`x ⊗ₜ (e · y) ↦ dT h e · (…)`), which is what makes killing generators enough.
3. For ONE relation `d ∈ Syz`: apply `dToD i` to `∑ l, (cd i) (a l) * d l = 0` and use
   `comm_cocone` to land `∑ l, cToC i (a l) • dToD i (d l) = 0` in `Dbot`.  Feed THAT to
   the equational criterion.  It returns `b l s ∈ Cbot` and `y s ∈ Dbot`, finitely many.
4. Descend the finitely many `b l s` (`c_surj`), the `y s` (`d_surj`), the syzygy equations
   `∑ l, cToC i (a l) * b l s = 0` (`c_sep`) and the factorisations
   `dToD i (d l) = ∑ s, b l s • y s` (`d_sep`) to a common `j ≥ i`, merging with
   `directed`.  **This step is the bulk of the Lean, and it wants one reusable helper
   first**: from a `Fintype ι` and a family `j : ι → Λ` with `le i (j x)`, produce a single
   `j₀` with `le i j₀` and `∀ x, le (j x) j₀` (Finset induction on `directed`).  Nothing
   else in the leaf is more than bookkeeping.
5. Conclude at that `j` by PURE BILINEARITY, with no flatness and no colimit left in play:
   `∑ l ⟨cT(a l)⟩ ⊗ dT(d l) = ∑ l ⟨cT(a l)⟩ ⊗ (∑ s β l s • η s)`
   `= ∑ s ⟨∑ l β l s * cT(a l)⟩ ⊗ η s = ∑ s ⟨0⟩ ⊗ η s = 0`.

So the four `surj`/`sep` fields are still exactly what is spent, as the paragraph above
says — but they are spent on descending a FINITE list of ring elements and equations, not
on constructing a colimit.  **The check that would refute this route:** if the equational
criterion's `b l s` could not be descended because `Cbot` is not a filtered union of the
`C_j` — but that is literally `c_surj` plus `c_sep`, which the datum supplies.

**WHAT THIS DOES NOT NEED.**  No `Tor` formalism, no projective resolution, no long exact
sequence, and no localization: `isLocalizationDT` belongs to Half B alone.  Note also that
the colimit is used only through the four `surj`/`sep` fields — `Ring.DirectLimit` does not
appear in this development and must not be introduced to state it.  Nor is right-exactness
of tensor products needed: an earlier draft of the route above went through a presentation
`↥(𝔪_i C_j) = C_j^p / Syz_j` and `TensorProduct.rTensor_exact`, and the equational
criterion makes that presentation unnecessary — it hands over the syzygies directly.

**FAITHFULNESS.**  The ideal in the target is `𝔪_i C_j`, the EXTENSION along `cT h`, not
`𝔪_j`; that is what `idealTensorComparison` produces and what 00MO's `I' = IR'` says.  The
`∃ j` is not discharged by `j = i`: at `j = i` the comparison map is the identity (up to
the algebra structures) and the claim would read `T_i = 0`, which is 10.128.3 at a single
stage — true only after the whole argument, not before it. -/
theorem exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem
    {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)
    (hflat : w.Flat) (i : Λ) :
    ∃ j : Λ, ∃ h : le i j,
      letI := hsys.isLocalRingC i
      letI : Algebra (C i) (D i) := (cd i).toAlgebra
      letI : Algebra (C i) (C j) := (cT h).toAlgebra
      letI : Algebra (C j) (D j) := (cd j).toAlgebra
      letI : Algebra (C i) (D j) := ((cd j).comp (cT h)).toAlgebra
      letI : Algebra (D i) (D j) := (dT h).toAlgebra
      haveI : IsScalarTower (C i) (C j) (D j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : IsScalarTower (C i) (D i) (D j) :=
        IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (hsys.comm_T h) x
      ∀ t ∈ LinearMap.ker
          (LinearMap.rTensor (D i) (IsLocalRing.maximalIdeal (C i)).subtype),
        idealTensorComparison (Cj := C j) (Dj := D j)
          (IsLocalRing.maximalIdeal (C i)) t = 0 := by
  classical
  letI := hsys.isLocalRingC i
  letI : Algebra (C i) (D i) := (cd i).toAlgebra
  letI : Algebra Cbot Dbot := w.toAlgebra
  haveI : Module.Flat Cbot Dbot := hflat
  haveI : IsNoetherianRing (C i) := hsys.isNoetherianC i
  haveI : IsNoetherianRing (D i) := hsys.isNoetherianD i
  -- ## generators of `𝔪_i`
  obtain ⟨p, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal (C i)))
  -- ## generators of the syzygy module of those generators over `D i`
  set φ : (Fin p → D i) →ₗ[D i] D i :=
    { toFun := fun d => ∑ l, (cd i) (a l) * d l
      map_add' := by
        intro x z
        simp only [Pi.add_apply, mul_add]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring } with hφ
  haveI : IsNoetherian (D i) (Fin p → D i) := inferInstance
  obtain ⟨m, g, hgspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  have hgmem : ∀ r, ∑ l, (cd i) (a l) * g r l = 0 := by
    intro r
    have hmem : g r ∈ LinearMap.ker φ := hgspan ▸ Submodule.subset_span ⟨r, rfl⟩
    simpa [hφ] using hmem
  have hg : ∀ d : Fin p → D i, (∑ l, (cd i) (a l) * d l = 0) →
      ∃ c : Fin m → D i, ∀ l, d l = ∑ r, c r * g r l := by
    intro d hd
    have hmem : d ∈ LinearMap.ker φ := by simpa [hφ] using hd
    rw [← hgspan] at hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (D i)).mp hmem
    exact ⟨c, fun l => by rw [← hc]; simp⟩
  -- ## the relation in `Dbot`, and the equational criterion of flatness
  have hrel : ∀ r, ∑ l, (cToC i (a l)) • (dToD i (g r l)) = 0 := by
    intro r
    have h1 : ∀ l, (cToC i (a l)) • (dToD i (g r l)) = dToD i ((cd i) (a l) * g r l) := by
      intro l
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      exact (DFunLike.congr_fun (hsys.comm_cocone i) (a l)).symm
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← map_sum, hgmem r, map_zero]
  choose k b y hb1' hb2' using fun r =>
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Cbot) (M := Dbot)
      (f := fun l => cToC i (a l)) (x := fun l => dToD i (g r l)) (hrel r)
  -- `hb1'`/`hb2'` come out with the `f`/`x` lambdas unreduced; restate them beta-reduced
  have hb1 : ∀ (r : Fin m) (l : Fin p), dToD i (g r l) = ∑ s, b r l s • y r s := hb1'
  have hb2 : ∀ (r : Fin m) (s : Fin (k r)), ∑ l, cToC i (a l) * b r l s = 0 := hb2'
  -- functoriality of the transition maps, in the applied form the `rw`s below need
  have hcT : ∀ {x z : Λ} {y : Λ} (h₁ : le x y) (h₂ : le y z) (h₃ : le x z) (u : C x),
      cT h₃ u = cT h₂ (cT h₁ u) := fun h₁ h₂ _ u =>
    (DFunLike.congr_fun (hsys.cT_comp h₁ h₂) u).symm
  have hdT : ∀ {x z : Λ} {y : Λ} (h₁ : le x y) (h₂ : le y z) (h₃ : le x z) (u : D x),
      dT h₃ u = dT h₂ (dT h₁ u) := fun h₁ h₂ _ u =>
    (DFunLike.congr_fun (hsys.dT_comp h₁ h₂) u).symm
  -- ## descend the finitely many coefficients and elements to one stage
  obtain ⟨j1, h1, β, η, hβ, hη⟩ := hsys.exists_eq_cToC_dToD_of_fintype i
    (fun t : Fin p × Σ r : Fin m, Fin (k r) => b t.2.1 t.1 t.2.2)
    (fun t : Σ r : Fin m, Fin (k r) => y t.1 t.2)
  -- the descended families, restated with the `Sigma`/`Prod` projections reduced
  have hβ' : ∀ (l : Fin p) (r : Fin m) (s : Fin (k r)), cToC j1 (β (l, ⟨r, s⟩)) = b r l s :=
    fun l r s => hβ (l, ⟨r, s⟩)
  have hη' : ∀ (r : Fin m) (s : Fin (k r)), dToD j1 (η ⟨r, s⟩) = y r s :=
    fun r s => hη ⟨r, s⟩
  -- ## descend the `C`-side syzygy equations
  have hC : ∀ t : Σ r : Fin m, Fin (k r),
      cToC j1 (∑ l, cT h1 (a l) * β (l, t)) = cToC j1 ((fun _ => 0) t) := by
    rintro ⟨r, s⟩
    show cToC j1 (∑ l, cT h1 (a l) * β (l, ⟨r, s⟩)) = cToC j1 0
    rw [map_sum, map_zero, ← hb2 r s]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hβ' l r s]
    congr 1
    exact DFunLike.congr_fun (hsys.comm_cToC h1) (a l)
  obtain ⟨j2, h12, hCeq'⟩ := hsys.exists_cT_eq_of_fintype j1
    (fun t : Σ r : Fin m, Fin (k r) => ∑ l, cT h1 (a l) * β (l, t)) (fun _ => 0) hC
  have hCeq : ∀ (r : Fin m) (s : Fin (k r)),
      cT h12 (∑ l, cT h1 (a l) * β (l, ⟨r, s⟩)) = cT h12 0 := fun r s => hCeq' ⟨r, s⟩
  -- ## descend the `D`-side factorisation equations
  have hD : ∀ t : Fin m × Fin p,
      dToD j1 (dT h1 (g t.1 t.2))
        = dToD j1 (∑ s, (cd j1) (β (t.2, ⟨t.1, s⟩)) * η ⟨t.1, s⟩) := by
    rintro ⟨r, l⟩
    show dToD j1 (dT h1 (g r l))
      = dToD j1 (∑ s, (cd j1) (β (l, ⟨r, s⟩)) * η ⟨r, s⟩)
    have hlhs : dToD j1 (dT h1 (g r l)) = dToD i (g r l) :=
      DFunLike.congr_fun (hsys.comm_dToD h1) (g r l)
    rw [hlhs, hb1 r l, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul, hη' r s, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    congr 1
    rw [← hβ' l r s]
    exact (DFunLike.congr_fun (hsys.comm_cocone j1) (β (l, ⟨r, s⟩))).symm
  obtain ⟨j3, h13, hDeq'⟩ := hsys.exists_dT_eq_of_fintype j1
    (fun t : Fin m × Fin p => dT h1 (g t.1 t.2))
    (fun t : Fin m × Fin p => ∑ s, (cd j1) (β (t.2, ⟨t.1, s⟩)) * η ⟨t.1, s⟩) hD
  have hDeq : ∀ (r : Fin m) (l : Fin p),
      dT h13 (dT h1 (g r l))
        = dT h13 (∑ s, (cd j1) (β (l, ⟨r, s⟩)) * η ⟨r, s⟩) := fun r l => hDeq' (r, l)
  -- ## merge the two stages
  obtain ⟨J, hj2J, hj3J⟩ := hsys.directed j2 j3
  have hJ1 : le j1 J := hsys.le_trans' h12 hj2J
  have hiJ : le i J := hsys.le_trans' h1 hJ1
  -- ## the two hypotheses of the killing lemma, now at stage `J`
  have hb' : ∀ (r : Fin m) (s : Fin (k r)),
      ∑ l, cT hiJ (a l) * cT hJ1 (β (l, ⟨r, s⟩)) = 0 := by
    intro r s
    have h0 : cT hJ1 (∑ l, cT h1 (a l) * β (l, ⟨r, s⟩)) = 0 := by
      rw [hcT h12 hj2J hJ1, hCeq r s, map_zero, map_zero]
    rw [map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    congr 1
    exact hcT h1 hJ1 hiJ (a l)
  have hy' : ∀ (r : Fin m) (l : Fin p),
      dT hiJ (g r l) = ∑ s, (cd J) (cT hJ1 (β (l, ⟨r, s⟩))) * dT hJ1 (η ⟨r, s⟩) := by
    intro r l
    have h0 : dT hJ1 (dT h1 (g r l))
        = dT hJ1 (∑ s, (cd j1) (β (l, ⟨r, s⟩)) * η ⟨r, s⟩) := by
      rw [hdT h13 hj3J hJ1, hdT h13 hj3J hJ1, hDeq r l]
    rw [hdT h1 hJ1 hiJ (g r l), h0, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_mul]
    congr 1
    exact (DFunLike.congr_fun (hsys.comm_T hJ1) (β (l, ⟨r, s⟩))).symm
  refine ⟨J, hiJ, ?_⟩
  letI : Algebra (C i) (C J) := (cT hiJ).toAlgebra
  letI : Algebra (C J) (D J) := (cd J).toAlgebra
  letI : Algebra (C i) (D J) := ((cd J).comp (cT hiJ)).toAlgebra
  letI : Algebra (D i) (D J) := (dT hiJ).toAlgebra
  haveI : IsScalarTower (C i) (C J) (D J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (C i) (D i) (D J) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (hsys.comm_T hiJ) x
  intro t ht
  exact idealTensorComparison_eq_zero_of_syzygy_descent
    (IsLocalRing.maximalIdeal (C i)) a ha g hg
    (κ := fun r => Fin (k r))
    (fun r l s => cT hJ1 (β (l, ⟨r, s⟩)))
    (fun r s => dT hJ1 (η ⟨r, s⟩)) hb' hy' t ht

/-- **HALF B OF [Stacks 00R6]'s COLIMIT LEAF — the surjectivity, and it is the ONLY
genuinely homological statement left in 10.128.3** (sorry leaf, cut 2026-07-30 out of
`exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem` below;
read that docstring's "Half B" paragraph, which is this leaf's specification).

*In a `IsNoetherianFlatDescentSystem`, for every `i ≤ j`, `T_j` lies in the `C_j`-span of
the image of `T_i` under `idealTensorComparison 𝔪_i`.*

**THE PROOF.**  This is the surjectivity of `T_i ⊗_{C_i} C_j → T_j`, i.e. of
`Tor_1^{C_i}(D_i, C_i/𝔪_i) ⊗_{C_i} C_j → Tor_1^{C_j}(D_j, C_j/𝔪_i C_j)`: Stacks 10.99.13
(`Tor_1^R(M, R'/I') ↠ Tor_1^{R'}(M ⊗_R R', R'/I')`) composed with 10.99.12 applied to
`C_i → C_i/𝔪_i → C_j/𝔪_i C_j`, then LOCALIZED along `isLocalizationDT h` — which is what
turns `D_i ⊗_{C_i} C_j` into `D_j`, and is this leaf's only use of that field.  Every
object is the kernel of an explicit `TensorProduct.lift` (Remark 10.75.9), so no derived
functor and no six-term sequence occurs; the content is two surjectivity statements about
explicit maps.

**WHY A SPAN AND NOT A SURJECTION.**  `Submodule.span (C j) (φ '' T_i)` is the image of
`T_i ⊗_{C_i} C_j → T_j` written without constructing that map, so this leaf needs no new
definition and its prover may build the base-changed map however is convenient.  `≤` rather
than `=` because that is all the assembly consumes, and the reverse inclusion is trivial.

**FAITHFULNESS.**  `∀ i ≤ j`, deliberately NOT `∃ j` — see the "NOTE THE ASYMMETRY"
paragraph in the section note above: Half A chooses the index, Half B must hold at it.
The statement is NOT vacuous and is not implied by Half A: at `j = i` it says `T_i` is
spanned by its own image under a map that is then essentially the identity, which is true
and harmless; the content is at `j > i`, where `𝔪_i C_j` may be a proper extension.

**THE ONE RISK IN THIS CUT, stated so its prover checks it FIRST.**  The `∀ i ≤ j` is a
reading of the parent docstring's Half B sentence, which carries no quantifier: 10.99.13
and 10.99.12 are statements about an arbitrary base change `C_i → C_j` and do not choose
`j`, so every `j ≥ i` should work.  If a prover finds that the surjectivity genuinely needs
`j` ENLARGED (beyond what Half A already gives), then this leaf is FALSE AS STATED and the
correct repair is to merge the two halves' indices — make this leaf `∃ j' ≥ j` too and have
the parent take the `directed` join — NOT to add hypotheses to it.  Refuting it that way is
a successful outcome; say so in the report. -/
theorem ker_rTensor_le_span_image_idealTensorComparison_of_isNoetherianFlatDescentSystem
    {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)
    {i j : Λ} (h : le i j) :
    letI := hsys.isLocalRingC i
    letI : Algebra (C i) (D i) := (cd i).toAlgebra
    letI : Algebra (C i) (C j) := (cT h).toAlgebra
    letI : Algebra (C j) (D j) := (cd j).toAlgebra
    letI : Algebra (C i) (D j) := ((cd j).comp (cT h)).toAlgebra
    letI : Algebra (D i) (D j) := (dT h).toAlgebra
    haveI : IsScalarTower (C i) (C j) (D j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (C i) (D i) (D j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (hsys.comm_T h) x
    LinearMap.ker (LinearMap.rTensor (D j)
        ((IsLocalRing.maximalIdeal (C i)).map (algebraMap (C i) (C j))).subtype)
      ≤ Submodule.span (C j)
          (idealTensorComparison (Cj := C j) (Dj := D j) (IsLocalRing.maximalIdeal (C i)) ''
            (LinearMap.ker (LinearMap.rTensor (D i)
              (IsLocalRing.maximalIdeal (C i)).subtype) :
              Set (↥(IsLocalRing.maximalIdeal (C i)) ⊗[C i] D i))) :=
  sorry

/-- **THE `Tor_1` VANISHING AT A LARGE STAGE — the colimit half of [Stacks 00R6]**
(**PROVEN 2026-07-30** over the two halves immediately above, which are its FURTHER CUT —
read the section note just above them; cut 2026-07-28 out of
`exists_flat_index_of_isNoetherianFlatDescentSystem` below).

*In a `IsNoetherianFlatDescentSystem` whose colimit `w` is flat, for every `i` there is
`j ≥ i` with `Tor_1^{C_j}(C_j/𝔪_i C_j, D_j) = 0`.*

The vanishing is written without derived functors, as injectivity of
`↥(𝔪_i C_j) ⊗_{C_j} D_j → C_j ⊗_{C_j} D_j`, i.e. as
`Function.Injective (LinearMap.rTensor (D j) I'.subtype)` with `I' = 𝔪_i C_j`.  That is
exactly the shape `flat_of_rTensor_injective_of_flat_quotientMap` consumes, which is why
the seam is here and not one step earlier or later.

**THE PROOF, which is 00R6's own, in two independent halves.**

*Half A — the colimit (00R6's body).*  `T_i := ker(𝔪_i ⊗_{C_i} D_i → D_i)` is a finitely
generated `D_i`-module: `𝔪_i` is f.g. because `C_i` is Noetherian (`isNoetherianC`), so
`𝔪_i ⊗_{C_i} D_i` is a finite `D_i`-module (`Module.Finite.base_change`), and `D_i` is
Noetherian (`isNoetherianD`), so the submodule `T_i` is f.g.  Let `ξ_1, …, ξ_n` generate
it.  Because `w` is flat, `(𝔪_i Cbot) ⊗_{Cbot} Dbot → Dbot` is injective, so each `ξ_k`
maps to `0` in `(𝔪_i Cbot) ⊗_{Cbot} Dbot`.  Tensor products commute with filtered
colimits, so — and this is the ONLY place `c_surj`/`c_sep`/`d_surj`/`d_sep` and
`directed` are spent — a single `j ≥ i` kills all `n` of them at once, i.e. the
comparison map `T_i → T_j := ker(𝔪_i C_j ⊗_{C_j} D_j → D_j)` is ZERO.

*Half B — the surjectivity (00MO's steps 4–6).*  The `C_j`-linear extension
`T_i ⊗_{C_i} C_j → T_j` of that same comparison map is SURJECTIVE.  This is Stacks
10.99.13 (`Tor_1^{C_i}(D_i, C_j/I') ↠ Tor_1^{C_j}(D_i ⊗_{C_i} C_j, C_j/I')`) composed
with 10.99.12 applied to `C_i → C_i/𝔪_i → C_j/I'`, then localized along
`isLocalizationDT h` — which is precisely what turns `D_i ⊗_{C_i} C_j` into `D_j`, and is
the only use of that field here.

Half A and Half B together give `T_j = 0`: `T_j` is spanned by the image of `T_i`, and
that image is `0`.  Injectivity of `LinearMap.rTensor (D j) I'.subtype` is `T_j = 0`.

**WHAT IS AND IS NOT NEEDED.**  Every object above is the kernel of an explicit
`TensorProduct.lift`, since `Tor_1(−, C/I) = ker(I ⊗ − → −)` (Remark 10.75.9).  **No
projective resolution, no derived functor and no long exact sequence occurs in either
half.**  Half A needs no `Tor` formalism whatsoever.  Half B is the only genuinely
homological content left anywhere in 10.128.3, and it is two surjectivity statements
about explicit maps — not a six-term sequence.

**THAT FURTHER CUT HAS BEEN TAKEN (2026-07-30) and this theorem is now PROVEN over it.**
The comparison map is `idealTensorComparison` just above (NOT corestricted to the kernels —
that turned out to be unnecessary, see the section note), Half A is
`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem` and Half B is
`ker_rTensor_le_span_image_idealTensorComparison_of_isNoetherianFlatDescentSystem`.  Those
two are the open leaves now; this docstring's Half A / Half B paragraphs above are their
specifications and are repeated on them.  Do not dispatch anyone at THIS declaration.

**FAITHFULNESS.**  The ideal is `𝔪_i C_j`, the EXTENSION of the stage-`i` maximal ideal
along `cT h` — NOT `𝔪_j`.  That is what 00MO's `I' = IR'` says, and what Half B's
surjectivity is a statement about; replacing it by `𝔪_j` would be a different and
strictly stronger claim that 00R6's proof does not deliver.

**NON-VACUITY, checked in both directions.**  The `∃ j` is not discharged by `j = i`:
at `j = i` (available from `le_rfl`) the conclusion reads
`Tor_1^{C_i}(C_i/𝔪_i, D_i) = 0`, which by 10.99.10 together with the fibre leaf below is
equivalent to `D_i` being flat over `C_i` — i.e. it is the whole content of 10.128.3 at a
single stage, true but certainly not free.  Nor is the statement vacuous for lack of
inhabitants: both `isNoetherianFlatDescentSystem_baseTot` and
`isNoetherianFlatDescentSystem_fibre` are written out below, so the hypothesis is
satisfiable. -/
theorem exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem
    {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)
    (hflat : w.Flat) (i : Λ) :
    ∃ j : Λ, ∃ h : le i j,
      letI := hsys.isLocalRingC i
      letI : Algebra (C j) (D j) := (cd j).toAlgebra
      Function.Injective (LinearMap.rTensor (D j)
        ((IsLocalRing.maximalIdeal (C i)).map (cT h)).subtype) := by
  obtain ⟨j, h, hA⟩ :=
    exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem hsys hflat i
  refine ⟨j, h, ?_⟩
  letI := hsys.isLocalRingC i
  letI : Algebra (C i) (D i) := (cd i).toAlgebra
  letI : Algebra (C i) (C j) := (cT h).toAlgebra
  letI : Algebra (C j) (D j) := (cd j).toAlgebra
  letI : Algebra (C i) (D j) := ((cd j).comp (cT h)).toAlgebra
  letI : Algebra (D i) (D j) := (dT h).toAlgebra
  haveI : IsScalarTower (C i) (C j) (D j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (C i) (D i) (D j) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (hsys.comm_T h) x
  have hB : LinearMap.ker (LinearMap.rTensor (D j)
      ((IsLocalRing.maximalIdeal (C i)).map (algebraMap (C i) (C j))).subtype)
      ≤ Submodule.span (C j)
        (idealTensorComparison (Cj := C j) (Dj := D j) (IsLocalRing.maximalIdeal (C i)) ''
          (LinearMap.ker (LinearMap.rTensor (D i)
            (IsLocalRing.maximalIdeal (C i)).subtype) :
            Set (↥(IsLocalRing.maximalIdeal (C i)) ⊗[C i] D i))) :=
    ker_rTensor_le_span_image_idealTensorComparison_of_isNoetherianFlatDescentSystem hsys h
  have hspan : Submodule.span (C j)
      (idealTensorComparison (Cj := C j) (Dj := D j) (IsLocalRing.maximalIdeal (C i)) ''
        (LinearMap.ker (LinearMap.rTensor (D i)
          (IsLocalRing.maximalIdeal (C i)).subtype) :
          Set (↥(IsLocalRing.maximalIdeal (C i)) ⊗[C i] D i))) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    simp [hA t ht]
  exact LinearMap.ker_eq_bot.mp (le_antisymm (hB.trans hspan) bot_le)

/-- **THE FIBRE IS FLAT AT EVERY STAGE — 00MO's step 2, and it involves NO `Tor`**
(**PROVEN 2026-07-29**; cut 2026-07-28 out of
`exists_flat_index_of_isNoetherianFlatDescentSystem` below).

*In a `IsNoetherianFlatDescentSystem`, for every `i ≤ j` the induced map
`C_j/𝔪_i C_j → D_j/𝔪_i D_j` is flat.*

This is the second hypothesis of the local criterion 10.99.10 at the ideal
`I' = 𝔪_i C_j`, and it is the one step of [Stacks 00MO] that is pure base change:

* `D_i/𝔪_i D_i` is flat over `C_i/𝔪_i` **for free**, because `C_i/𝔪_i` is a FIELD
  (`isLocalRingC i` makes `𝔪_i` maximal, and every module over a field is flat).  This
  is 00MO's hypothesis (2), which in our application is a theorem rather than an
  assumption because `M = S'`;
* base change along `C_i/𝔪_i → C_j/I'` (Stacks 10.39.7, `Module.Flat.baseChange`) makes
  `(D_i/𝔪_i D_i) ⊗_{C_i/𝔪_i} (C_j/I')` flat over `C_j/I'`, and that tensor product is
  `(C_j ⊗_{C_i} D_i)/I'(C_j ⊗_{C_i} D_i)` because quotients commute with base change;
* `D_j` is a localization of `C_j ⊗_{C_i} D_i` (`isLocalizationDT h`), so `D_j/I' D_j` is
  the corresponding localization of that quotient, and a localization of a flat algebra
  is flat over the base — localization is flat, then `Module.Flat.trans`.

**WHICH FIELDS THIS LEAF SPENDS, and it is a short list.**  Only `isLocalRingC`,
`isLocalHomCD` and `isLocalizationDT h`.  In particular NONE of `isNoetherianC`,
`isNoetherianD`, `c_surj`, `d_surj`, `c_sep`, `d_sep`, `directed` is used, and neither is
flatness of `w` — which is why this leaf carries no `hflat` hypothesis at all.  A prover
who finds they need a colimit condition or a Noetherian hypothesis here should say so
rather than adding one: it would mean the seam is in the wrong place.

**FAITHFULNESS.**  The ideal is `𝔪_i C_j`, matching
`exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem` and
00MO's `I' = IR'`.  With `𝔪_j` in its place the statement would be about the closed
fibre of stage `j` rather than about the base change of stage `i`'s fibre, and the third
bullet would no longer apply — so the two leaves must be read as a matched pair, and
changing the ideal in one without the other breaks the assembly below.

**NON-DEGENERACY.**  At `j = i` the statement is the first bullet alone (flatness over a
field), so it is TRUE but not vacuous: the whole content sits in the transition `i ≤ j`,
where the base change and the localization happen. -/
theorem flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem
    {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)
    {i j : Λ} (h : le i j) :
    letI := hsys.isLocalRingC i
    letI : Algebra (C j) (D j) := (cd j).toAlgebra
    (Ideal.quotientMap
      (((IsLocalRing.maximalIdeal (C i)).map (cT h)).map (algebraMap (C j) (D j)))
      (algebraMap (C j) (D j)) Ideal.le_comap_map).Flat := by
  letI := hsys.isLocalRingC i
  letI : Algebra (C i) (D i) := (cd i).toAlgebra
  letI : Algebra (C i) (C j) := (cT h).toAlgebra
  letI : Algebra (C i) (D j) := ((cd j).comp (cT h)).toAlgebra
  letI : Algebra (C j) (D j) := (cd j).toAlgebra
  letI : Algebra (D i) (D j) := (dT h).toAlgebra
  haveI : IsScalarTower (C i) (C j) (D j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (C i) (D i) (D j) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (hsys.comm_T h) x
  letI : Algebra (C j ⊗[C i] D i) (D j) :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (C i) (C j) (D j))
      (IsScalarTower.toAlgHom (C i) (D i) (D j))
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  obtain ⟨W, hW⟩ := hsys.isLocalizationDT h
  haveI := hW
  haveI : IsScalarTower (C j) (C j ⊗[C i] D i) (D j) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show cd j x = Algebra.TensorProduct.lift _ _ _ (x ⊗ₜ[C i] 1)
      simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
  exact RingHom.flat_algebraMap_iff.mpr
    (flat_quotMap_map_of_isLocalization_tensorProduct W (IsLocalRing.maximalIdeal (C i)))

/-- **STACKS 10.128.3** ([Stacks 00R6]; **PROVEN 2026-07-28** over the two leaves
immediately above and the already-proven 10.99.10 — read the section note above before
touching it).

*In a `IsNoetherianFlatDescentSystem` whose colimit `w` is flat, `cd j` is flat cofinally
in `Λ`.*

**THE PROOF, from the source.**  Fix `i`.  `Tor_1^{C_i}(D_i, C_i/𝔪_i)` is the kernel of
`𝔪_i ⊗_{C_i} D_i → D_i` (Remark 10.75.9), and it is a finitely generated `D_i`-module
because `D_i` is Noetherian (`isNoetherianD`); let `ξ_1, …, ξ_n` generate it.  Flatness
of `Dbot` over `Cbot` gives `ker(𝔪_i Cbot ⊗_{Cbot} Dbot → Dbot) = 0`, and tensor products
commute with filtered colimits, so — using `c_surj`/`c_sep`/`d_surj`/`d_sep` — there is
`j ≥ i` with every `ξ_k` mapping to zero in `𝔪_i C_j ⊗_{C_j} D_j`.  Hence
`Tor_1^{C_i}(D_i, C_i/𝔪_i) → Tor_1^{C_j}(D_j, C_j/𝔪_i C_j)` is zero, and since
`D_i ⊗_{C_i} C_i/𝔪_i` is flat over the FIELD `C_i/𝔪_i`, [Stacks 00MO] applied to the
square `C_i → C_j`, `D_i → D_j` — whose hypothesis (1) is `isLocalizationDT` — gives
`D_j` flat over `C_j`.

**WHAT BLOCKS IT AT THIS PIN — CORRECTED 2026-07-28.**  The previous version of this
paragraph said the last step needs a `Tor` long exact sequence, that
`Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean` is where such a theory belongs,
and that "a prover who builds `Tor_1` and its six-term sequence in the first variable
closes that leaf and this one together".  **All three clauses are withdrawn**; the
refuting check was one grep in this file.  [Stacks 00MO]'s proof invokes **Lemma
10.99.10**, which is PROVEN here as `flat_of_rTensor_injective_of_flat_quotientMap`, and
everything 00MO needs beyond it is expressible as kernels of explicit
`TensorProduct.lift`s (Remark 10.75.9: `Tor_1(−, C/I) = ker(I ⊗ − → −)`).  No derived
functor, projective resolution or long exact sequence occurs anywhere in the cut below.
See the CORRECTED paragraph in the section note above for the line-by-line reading.

**THIS LEAF IS NOW PROVEN**, over the two leaves immediately above it — the colimit half
`exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem` and the
fibre half `flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem` — plus
10.99.10.  The body is exactly 00MO's shape: the two leaves supply 10.99.10's two
hypotheses at the ideal `I' = 𝔪_i C_j`, and `IsLocalRing.map_maximalIdeal_le` supplies
`I' ≤ 𝔪_j` from `isLocalHomCT`.

**FAITHFULNESS.**  The conclusion is 10.128.3's, in the cofinal form its PROOF delivers
(the proof fixes `λ` and produces `λ' ≥ λ`); restricting the system to `{j | i ≤ j}`
turns the cofinal form back into 10.128.3's bare `∃ λ`, so this is not a strengthening.
The statement is UNCHANGED by the 2026-07-28 cut — both applications
(`exists_flatBase_index_of_noetherianApproxSystem`,
`exists_flatFibre_index_of_noetherianApproxSystem`) still consume it verbatim.

[Stacks 00R6]: https://stacks.math.columbia.edu/tag/00R6
[Stacks 00MO]: https://stacks.math.columbia.edu/tag/00MO
[Stacks 00ML]: https://stacks.math.columbia.edu/tag/00ML -/
theorem exists_flat_index_of_isNoetherianFlatDescentSystem
    {Λ : Type u} {le : Λ → Λ → Prop} {C D : Λ → Type u}
    [∀ i, CommRing (C i)] [∀ i, CommRing (D i)]
    {cd : ∀ i, C i →+* D i}
    {cT : ∀ {i j : Λ}, le i j → (C i →+* C j)} {dT : ∀ {i j : Λ}, le i j → (D i →+* D j)}
    {Cbot Dbot : Type u} [CommRing Cbot] [CommRing Dbot] {w : Cbot →+* Dbot}
    {cToC : ∀ i, C i →+* Cbot} {dToD : ∀ i, D i →+* Dbot}
    (hsys : IsNoetherianFlatDescentSystem le C D cd cT dT w cToC dToD)
    (hflat : w.Flat) (i : Λ) :
    ∃ j : Λ, ∃ _ : le i j, (cd j).Flat := by
  letI := hsys.isLocalRingC i
  obtain ⟨j, hij, htor⟩ :=
    exists_le_rTensor_map_maximalIdeal_injective_of_isNoetherianFlatDescentSystem
      hsys hflat i
  refine ⟨j, hij, ?_⟩
  haveI := hsys.isLocalRingC j
  haveI := hsys.isLocalRingD j
  haveI := hsys.isNoetherianC j
  haveI := hsys.isNoetherianD j
  haveI := hsys.isLocalHomCT hij
  algebraize [cd j]
  haveI : IsLocalHom (algebraMap (C j) (D j)) := hsys.isLocalHomCD j
  exact flat_of_rTensor_injective_of_flat_quotientMap
    (I := (IsLocalRing.maximalIdeal (C i)).map (cT hij))
    (J := ((IsLocalRing.maximalIdeal (C i)).map (cT hij)).map (algebraMap (C j) (D j)))
    (IsLocalRing.map_maximalIdeal_le (cT hij)) rfl Ideal.le_comap_map htor
    (flat_quotientMap_map_maximalIdeal_of_isNoetherianFlatDescentSystem hsys hij)

/-- **THE `R_λ → S'_λ` TOWER OF A `NoetherianApproxSystem` IS A DESCENT SYSTEM**
(PROVEN).  Every field is a field of the system, a composite of two of them, or a
one-line consequence of the commuting squares; `isLocalizationDT` is
`isLocalizationTotBaseT` VERBATIM, which is what that field exists for. -/
theorem NoetherianApproxSystem.isNoetherianFlatDescentSystem_baseTot {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A] {g : R →+* B} {v : B →+* A}
    (sys : NoetherianApproxSystem g v) :
    IsNoetherianFlatDescentSystem sys.le (fun i => sys.Base i) (fun i => sys.Tot i)
      (fun i => (sys.midToTot i).comp (sys.baseToMid i))
      (fun {_ _} h => sys.baseT h) (fun {_ _} h => sys.totT h)
      (v.comp g) sys.baseToR sys.totToA where
  le_rfl := sys.le_rfl
  le_trans' := sys.le_trans'
  directed := sys.directed
  isLocalRingC := sys.isLocalRingBase
  isLocalRingD := sys.isLocalRingTot
  isNoetherianC := sys.isNoetherianBase
  isNoetherianD := sys.isNoetherianTot
  isLocalHomCD i := by
    haveI := sys.isLocalHomBaseToMid i
    haveI := sys.isLocalHomMidToTot i
    infer_instance
  cT_comp := sys.baseT_comp
  dT_comp := sys.totT_comp
  comm_T h := by
    rw [RingHom.comp_assoc, sys.comm_baseT h, ← RingHom.comp_assoc, sys.comm_midT h,
      RingHom.comp_assoc]
  isLocalHomCT := sys.isLocalHomBaseT
  isLocalHomDT := sys.isLocalHomTotT
  comm_cocone i := by
    rw [← RingHom.comp_assoc, sys.comm_midTot i, RingHom.comp_assoc, sys.comm_baseMid i,
      ← RingHom.comp_assoc]
  comm_cToC := sys.comm_baseToR
  comm_dToD := sys.comm_totToA
  isLocalHomCToC := sys.isLocalHomBaseToR
  isLocalHomDToD := sys.isLocalHomTotToA
  c_surj := sys.base_surj
  d_surj := sys.tot_surj
  c_sep := sys.base_sep
  d_sep := sys.tot_sep
  isLocalizationDT h := sys.isLocalizationTotBaseT h

/-- **A QUOTIENT MAP ALONG A LOCAL HOM IS LOCAL** (PROVEN), provided the ideal downstairs
sits inside the maximal ideal.  Bookkeeping for the fibre system below: `IsLocalHom` of an
`Ideal.quotientMap` is needed six times there and the argument is the same each time —
a unit upstairs in `T ⧸ I` forces a unit in `T`, because `I ≤ 𝔪_T` makes `1` a unit
modulo `I` only if it is one already. -/
theorem isLocalHom_quotientMap {S₀ T₀ : Type u} [CommRing S₀] [CommRing T₀] [IsLocalRing T₀]
    {J : Ideal S₀} {I : Ideal T₀} (φ : S₀ →+* T₀) [IsLocalHom φ] (H : J ≤ I.comap φ)
    (hI : I ≤ IsLocalRing.maximalIdeal T₀) :
    IsLocalHom (Ideal.quotientMap I φ H) := by
  constructor
  intro a ha
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  have hfs : IsUnit (φ s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    obtain ⟨t, ht⟩ := ha.exists_right_inv
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    have ht' : φ s * t' - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, ht, sub_self]
    have h1 : (1 : T₀) ∈ IsLocalRing.maximalIdeal T₀ := by
      have hmul : φ s * t' ∈ IsLocalRing.maximalIdeal T₀ := Ideal.mul_mem_right _ _ hmem
      have h2 := (IsLocalRing.maximalIdeal T₀).sub_mem hmul (hI ht')
      rwa [sub_sub_cancel] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal T₀).ne_top
      ((IsLocalRing.maximalIdeal T₀).eq_top_iff_one.mpr h1)
  exact ((isUnit_map_iff φ s).mp hfs).map _

namespace NoetherianApproxSystem

section FibreData

variable {R B A : Type u} [CommRing R] [CommRing B] [CommRing A] {g : R →+* B} {v : B →+* A}

/-- `𝔭_λ S_λ`, the ideal `𝔪_{R_λ}` cuts out in `S_λ`. -/
def fibreIdealMid (sys : NoetherianApproxSystem g v) (i : sys.Λ) : Ideal (sys.Mid i) :=
  letI := sys.isLocalRingBase i
  (IsLocalRing.maximalIdeal (sys.Base i)).map (sys.baseToMid i)

/-- `𝔭_λ S'_λ`. -/
def fibreIdealTot (sys : NoetherianApproxSystem g v) (i : sys.Λ) : Ideal (sys.Tot i) :=
  letI := sys.isLocalRingBase i
  (IsLocalRing.maximalIdeal (sys.Base i)).map ((sys.midToTot i).comp (sys.baseToMid i))

theorem fibreIdealMid_eq (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    letI := sys.isLocalRingBase i
    sys.fibreIdealMid i = (IsLocalRing.maximalIdeal (sys.Base i)).map (sys.baseToMid i) := rfl

theorem fibreIdealTot_eq (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    letI := sys.isLocalRingBase i
    sys.fibreIdealTot i =
      (IsLocalRing.maximalIdeal (sys.Base i)).map ((sys.midToTot i).comp (sys.baseToMid i)) := rfl

theorem fibreIdealMid_le_comap_midToTot (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    sys.fibreIdealMid i ≤ (sys.fibreIdealTot i).comap (sys.midToTot i) :=
  letI := sys.isLocalRingBase i
  map_le_comap_map_comp (sys.baseToMid i) (sys.midToTot i) (IsLocalRing.maximalIdeal (sys.Base i))

theorem fibreIdealMid_le_comap_midT (sys : NoetherianApproxSystem g v) {i j : sys.Λ}
    (h : sys.le i j) : sys.fibreIdealMid i ≤ (sys.fibreIdealMid j).comap (sys.midT h) := by
  letI := sys.isLocalRingBase i
  letI := sys.isLocalRingBase j
  haveI := sys.isLocalHomBaseT h
  rw [sys.fibreIdealMid_eq i, Ideal.map_le_iff_le_comap]
  intro x hx
  show sys.midT h (sys.baseToMid i x) ∈ sys.fibreIdealMid j
  rw [show sys.midT h (sys.baseToMid i x) = sys.baseToMid j (sys.baseT h x) from
    (DFunLike.congr_fun (sys.comm_baseT h) x).symm, sys.fibreIdealMid_eq j]
  refine Ideal.mem_map_of_mem _ ?_
  have hmem : x ∈ (IsLocalRing.maximalIdeal (sys.Base j)).comap (sys.baseT h) := by
    rw [IsLocalRing.maximalIdeal_comap]; exact hx
  exact hmem

theorem fibreIdealTot_le_comap_totT (sys : NoetherianApproxSystem g v) {i j : sys.Λ}
    (h : sys.le i j) : sys.fibreIdealTot i ≤ (sys.fibreIdealTot j).comap (sys.totT h) := by
  letI := sys.isLocalRingBase i
  letI := sys.isLocalRingBase j
  haveI := sys.isLocalHomBaseT h
  rw [sys.fibreIdealTot_eq i, Ideal.map_le_iff_le_comap]
  intro x hx
  show sys.totT h (sys.midToTot i (sys.baseToMid i x)) ∈ sys.fibreIdealTot j
  have e : sys.totT h (sys.midToTot i (sys.baseToMid i x))
      = sys.midToTot j (sys.baseToMid j (sys.baseT h x)) := by
    rw [show sys.baseToMid j (sys.baseT h x) = sys.midT h (sys.baseToMid i x) from
      DFunLike.congr_fun (sys.comm_baseT h) x]
    exact (DFunLike.congr_fun (sys.comm_midT h) (sys.baseToMid i x)).symm
  rw [e, sys.fibreIdealTot_eq j]
  refine Ideal.mem_map_of_mem _ ?_
  have hmem : x ∈ (IsLocalRing.maximalIdeal (sys.Base j)).comap (sys.baseT h) := by
    rw [IsLocalRing.maximalIdeal_comap]; exact hx
  exact hmem

/-- `S_λ/𝔭_λ S_λ → S'_λ/𝔭_λ S'_λ`, the fibre of the stage.  This is the map
`exists_flatFibre_index_of_noetherianApproxSystem` asks to be flat. -/
def fibreCD (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    (sys.Mid i ⧸ sys.fibreIdealMid i) →+* (sys.Tot i ⧸ sys.fibreIdealTot i) :=
  Ideal.quotientMap _ (sys.midToTot i) (sys.fibreIdealMid_le_comap_midToTot i)

/-- The transition map of the fibre `Mid` tower. -/
def fibreCT (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j) :
    (sys.Mid i ⧸ sys.fibreIdealMid i) →+* (sys.Mid j ⧸ sys.fibreIdealMid j) :=
  Ideal.quotientMap _ (sys.midT h) (sys.fibreIdealMid_le_comap_midT h)

/-- The transition map of the fibre `Tot` tower. -/
def fibreDT (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j) :
    (sys.Tot i ⧸ sys.fibreIdealTot i) →+* (sys.Tot j ⧸ sys.fibreIdealTot j) :=
  Ideal.quotientMap _ (sys.totT h) (sys.fibreIdealTot_le_comap_totT h)

@[simp] theorem fibreCD_mk (sys : NoetherianApproxSystem g v) (i : sys.Λ) (x : sys.Mid i) :
    sys.fibreCD i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sys.midToTot i x) :=
  Ideal.quotientMap_mk

@[simp] theorem fibreCT_mk (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j)
    (x : sys.Mid i) :
    sys.fibreCT h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sys.midT h x) :=
  Ideal.quotientMap_mk

@[simp] theorem fibreDT_mk (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j)
    (x : sys.Tot i) :
    sys.fibreDT h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sys.totT h x) :=
  Ideal.quotientMap_mk

/-- Naturality of the fibre tower, extracted because it is needed BEFORE the descent-system
instance below (it is what makes the `IsScalarTower` in `exists_isLocalization_fibre`'s
statement typecheck) as well as inside it. -/
theorem fibre_comm_T (sys : NoetherianApproxSystem g v) {i j : sys.Λ} (h : sys.le i j) :
    (sys.fibreCD j).comp (sys.fibreCT h) = (sys.fibreDT h).comp (sys.fibreCD i) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, fibreCT_mk, fibreCD_mk, fibreDT_mk]
  exact congrArg _ (DFunLike.congr_fun (sys.comm_midT h) x)

end FibreData

section FibreColimit

variable {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] {g : R →+* B} {v : B →+* A}

theorem fibreIdealMid_le_comap_midToB (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    sys.fibreIdealMid i ≤ ((IsLocalRing.maximalIdeal R).map g).comap (sys.midToB i) := by
  letI := sys.isLocalRingBase i
  haveI := sys.isLocalHomBaseToR i
  rw [sys.fibreIdealMid_eq i, Ideal.map_le_iff_le_comap]
  intro x hx
  show sys.midToB i (sys.baseToMid i x) ∈ (IsLocalRing.maximalIdeal R).map g
  rw [show sys.midToB i (sys.baseToMid i x) = g (sys.baseToR i x) from
    DFunLike.congr_fun (sys.comm_baseMid i) x]
  refine Ideal.mem_map_of_mem _ ?_
  have hmem : x ∈ (IsLocalRing.maximalIdeal R).comap (sys.baseToR i) := by
    rw [IsLocalRing.maximalIdeal_comap]; exact hx
  exact hmem

theorem fibreIdealTot_le_comap_totToA (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    sys.fibreIdealTot i ≤ ((IsLocalRing.maximalIdeal R).map (v.comp g)).comap (sys.totToA i) := by
  letI := sys.isLocalRingBase i
  haveI := sys.isLocalHomBaseToR i
  rw [sys.fibreIdealTot_eq i, Ideal.map_le_iff_le_comap]
  intro x hx
  show sys.totToA i (sys.midToTot i (sys.baseToMid i x)) ∈
    (IsLocalRing.maximalIdeal R).map (v.comp g)
  have e : sys.totToA i (sys.midToTot i (sys.baseToMid i x)) = v (g (sys.baseToR i x)) := by
    rw [show sys.totToA i (sys.midToTot i (sys.baseToMid i x))
        = v (sys.midToB i (sys.baseToMid i x)) from
      DFunLike.congr_fun (sys.comm_midTot i) (sys.baseToMid i x)]
    rw [show sys.midToB i (sys.baseToMid i x) = g (sys.baseToR i x) from
      DFunLike.congr_fun (sys.comm_baseMid i) x]
  rw [e]
  refine Ideal.mem_map_of_mem _ ?_
  have hmem : x ∈ (IsLocalRing.maximalIdeal R).comap (sys.baseToR i) := by
    rw [IsLocalRing.maximalIdeal_comap]; exact hx
  exact hmem

/-- The cocone map `S_λ/𝔭_λ S_λ → S/𝔪_R S`. -/
def fibreCToC (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    (sys.Mid i ⧸ sys.fibreIdealMid i) →+* (B ⧸ (IsLocalRing.maximalIdeal R).map g) :=
  Ideal.quotientMap _ (sys.midToB i) (sys.fibreIdealMid_le_comap_midToB i)

/-- The cocone map `S'_λ/𝔭_λ S'_λ → S'/𝔪_R S'`. -/
def fibreDToD (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    (sys.Tot i ⧸ sys.fibreIdealTot i) →+*
      (A ⧸ (IsLocalRing.maximalIdeal R).map (v.comp g)) :=
  Ideal.quotientMap _ (sys.totToA i) (sys.fibreIdealTot_le_comap_totToA i)

@[simp] theorem fibreCToC_mk (sys : NoetherianApproxSystem g v) (i : sys.Λ) (x : sys.Mid i) :
    sys.fibreCToC i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sys.midToB i x) :=
  Ideal.quotientMap_mk

@[simp] theorem fibreDToD_mk (sys : NoetherianApproxSystem g v) (i : sys.Λ) (x : sys.Tot i) :
    sys.fibreDToD i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (sys.totToA i x) :=
  Ideal.quotientMap_mk

end FibreColimit

end NoetherianApproxSystem

/-! ### THE TWO "`𝔪_R` IS THE UNION OF THE STAGE IDEALS" LEAVES, PROVEN 2026-07-28

The docstring of `exists_mem_fibreIdealTot` asked for exactly this: "a prover should
factor the common argument out into a lemma about a single tower over the `Base` system
rather than writing it twice".  `exists_mem_map_maximalIdeal_of_colimitTower` below is
that lemma, and both leaves are one application of it apiece — the `Mid` tower with
`φ = g`, and the `Tot` tower with `φ = v.comp g` and `baseToE i = midToTot i ∘ baseToMid i`,
which is the composite `fibreIdealTot` is the `Ideal.map` along.
-/

/-- **`𝔪_R · X` IS THE UNION OF THE IMAGES OF THE STAGE IDEALS `𝔪_{Base i} · E i`**
(PROVEN 2026-07-28) — the shared engine of `exists_mem_fibreIdealMid` and
`exists_mem_fibreIdealTot`.

*Given a filtered system of local rings `Base i` with colimit the local ring `R`, and ONE
tower `E i` over it with colimit `X` along `φ : R →+* X`, an element of `E i` landing in
`(𝔪_R).map φ` already lies in the stage ideal `(𝔪_{Base j}).map (baseToE j)` at some
`j ≥ i`.*

**THE PROOF, and why it is not the finite-expansion argument.**  The obvious route expands
`eToX i z = ∑_k x_k · φ m_k`, pulls each `m_k` and each `x_k` back to a stage, and uses
`directed` finitely many times to align the indices.  That works and costs a page of
`Finset` bookkeeping.  Instead, note that

  `J := {x : X | ∀ a (w : E a), eToX a w = x → ∃ b ≥ a, eT w ∈ (𝔪_{Base b}).map (baseToE b)}`

is an IDEAL of `X` — `hzero`, `hadd`, `hsmul` below, each proven by pulling the one or two
elements involved back with `e_surj`, aligning with `directed`, and closing the resulting
equation in `X` with a single `e_sep`.  Then `Ideal.map_le_iff_le_comap` reduces
`(𝔪_R).map φ ≤ J` to the GENERATORS: `φ m ∈ J` for `m ∈ 𝔪_R`, which is `hgen`.  No sum is
ever formed, and the hypothesis is applied to `z` itself at the very end.

**WHERE LOCALITY IS SPENT.**  Exactly twice, both inside `hgen`: `isLocalHomBaseToR` turns
`baseToR p y = m ∈ 𝔪_R` into `y ∈ 𝔪_{Base p}` (a unit would map to a unit), and
`isLocalHomBaseT` carries that along the base transitions.  `push` uses `isLocalHomBaseT`
for the same reason.  Nothing else in the proof needs a ring to be local — in particular
the `E` tower's rings are NOT assumed local, which is why the lemma applies verbatim to the
`Mid` and the `Tot` towers of a `NoetherianApproxSystem`.

**WHY `comp` MAY TAKE AN ARBITRARY THIRD PROOF.**  `le a c` is a `Prop`, so proof
irrelevance is definitional and `eT h₃` is the same function as `eT (le_trans' h₁ h₂)` for
any `h₃`.  That is what keeps the index bookkeeping to one lemma instead of a transport.

**FAITHFULNESS.**  Every hypothesis is a field of `NoetherianApproxSystem` (or, for the
`Tot` instance, a one-`rw` composite of two of them), so nothing is asked for that the two
call sites cannot supply — which is the check a hypothesis-side datum has to pass, and it is
discharged by the compiler at both applications rather than by argument.  Note `Noetherian`
appears NOWHERE: this statement is pure colimit bookkeeping, and the Noetherian hypotheses of
00R7 are spent elsewhere.

**NON-DEGENERACY.**  Not vacuous and not trivial: with `Λ` a point and `E = X`, `Base = R`,
`baseToE = φ`, every hypothesis holds and the conclusion says `z ∈ (𝔪_R).map φ`, which is the
input — so the content is exactly the passage from the colimit `X` to a finite stage, and it
is `e_sep`/`base_surj` that carry it. -/
theorem exists_mem_map_maximalIdeal_of_colimitTower
    {Λ : Type u} {le : Λ → Λ → Prop}
    {R X : Type u} [CommRing R] [CommRing X] [IsLocalRing R] {φ : R →+* X}
    {Base E : Λ → Type u} [∀ i, CommRing (Base i)] [∀ i, CommRing (E i)]
    [hLocBase : ∀ i, IsLocalRing (Base i)]
    {baseT : ∀ {i j : Λ}, le i j → (Base i →+* Base j)}
    {eT : ∀ {i j : Λ}, le i j → (E i →+* E j)}
    {baseToE : ∀ i, Base i →+* E i}
    {baseToR : ∀ i, Base i →+* R} {eToX : ∀ i, E i →+* X}
    (le_trans' : ∀ {i j k}, le i j → le j k → le i k)
    (directed : ∀ i j, ∃ k, le i k ∧ le j k)
    (eT_comp : ∀ {i j k} (h₁ : le i j) (h₂ : le j k),
      (eT h₂).comp (eT h₁) = eT (le_trans' h₁ h₂))
    (comm_baseE : ∀ i, (eToX i).comp (baseToE i) = φ.comp (baseToR i))
    (comm_baseT : ∀ {i j} (h : le i j), (baseToE j).comp (baseT h) = (eT h).comp (baseToE i))
    (comm_baseToR : ∀ {i j} (h : le i j), (baseToR j).comp (baseT h) = baseToR i)
    (comm_eToX : ∀ {i j} (h : le i j), (eToX j).comp (eT h) = eToX i)
    (isLocalHomBaseT : ∀ {i j} (h : le i j), IsLocalHom (baseT h))
    (isLocalHomBaseToR : ∀ i, IsLocalHom (baseToR i))
    (base_surj : ∀ x : R, ∃ i, ∃ y : Base i, baseToR i y = x)
    (e_surj : ∀ x : X, ∃ i, ∃ y : E i, eToX i y = x)
    (e_sep : ∀ i (x y : E i), eToX i x = eToX i y → ∃ j, ∃ h : le i j, eT h x = eT h y)
    (i : Λ) (z : E i) (hz : eToX i z ∈ (IsLocalRing.maximalIdeal R).map φ) :
    ∃ j, ∃ h : le i j,
      eT h z ∈ (IsLocalRing.maximalIdeal (Base j)).map (baseToE j) := by
  -- Transitivity of the tower transitions, in applied form.  The third proof
  -- argument may be ANY proof of `le a c`: `le a c` is a `Prop`, so proof
  -- irrelevance makes `eT h₃` and `eT (le_trans' h₁ h₂)` definitionally equal.
  have comp : ∀ {a b c : Λ} (h₁ : le a b) (h₂ : le b c) (_h₃ : le a c) (w : E a),
      eT h₂ (eT h₁ w) = eT _h₃ w := fun h₁ h₂ _ w => DFunLike.congr_fun (eT_comp h₁ h₂) w
  -- Stage-ideal membership pushes forward along the tower.
  have push : ∀ {a b : Λ} (h : le a b) (w : E a),
      w ∈ (IsLocalRing.maximalIdeal (Base a)).map (baseToE a) →
      eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b) := by
    intro a b h w hw
    haveI := isLocalHomBaseT h
    have hle : (IsLocalRing.maximalIdeal (Base a)).map (baseToE a) ≤
        ((IsLocalRing.maximalIdeal (Base b)).map (baseToE b)).comap (eT h) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      show eT h (baseToE a x) ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b)
      rw [show eT h (baseToE a x) = baseToE b (baseT h x) from
        (DFunLike.congr_fun (comm_baseT h) x).symm]
      refine Ideal.mem_map_of_mem _ ?_
      have hmem : x ∈ (IsLocalRing.maximalIdeal (Base b)).comap (baseT h) := by
        rw [IsLocalRing.maximalIdeal_comap]; exact hx
      exact hmem
    exact hle hw
  -- The set of elements of `X` witnessed by a stage ideal is an ideal of `X`.
  have hzero : ∀ (a : Λ) (w : E a), eToX a w = 0 →
      ∃ b, ∃ h : le a b, eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b) := by
    intro a w hw
    obtain ⟨b, h, hb⟩ := e_sep a w 0 (by rw [hw, map_zero])
    exact ⟨b, h, by rw [hb, map_zero]; exact Ideal.zero_mem _⟩
  have hadd : ∀ x y : X,
      (∀ (a : Λ) (w : E a), eToX a w = x →
        ∃ b, ∃ h : le a b, eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b)) →
      (∀ (a : Λ) (w : E a), eToX a w = y →
        ∃ b, ∃ h : le a b, eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b)) →
      ∀ (a : Λ) (w : E a), eToX a w = x + y →
        ∃ b, ∃ h : le a b,
          eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b) := by
    intro x y hx hy a w hw
    obtain ⟨p, zx, hzx⟩ := e_surj x
    obtain ⟨q, zy, hzy⟩ := e_surj y
    obtain ⟨k₁, hak₁, hpk₁⟩ := directed a p
    obtain ⟨k, hk₁k, hqk⟩ := directed k₁ q
    have hak : le a k := le_trans' hak₁ hk₁k
    have hpk : le p k := le_trans' hpk₁ hk₁k
    have key : eToX k (eT hak w) = eToX k (eT hpk zx + eT hqk zy) := by
      rw [map_add,
        show eToX k (eT hak w) = eToX a w from DFunLike.congr_fun (comm_eToX hak) w,
        show eToX k (eT hpk zx) = eToX p zx from DFunLike.congr_fun (comm_eToX hpk) zx,
        show eToX k (eT hqk zy) = eToX q zy from DFunLike.congr_fun (comm_eToX hqk) zy,
        hw, hzx, hzy]
    obtain ⟨m, hkm, hm⟩ := e_sep k _ _ key
    obtain ⟨b₁, hmb₁, hb₁⟩ := hx m (eT hkm (eT hpk zx)) (by
      rw [show eToX m (eT hkm (eT hpk zx)) = eToX k (eT hpk zx) from
          DFunLike.congr_fun (comm_eToX hkm) _,
        show eToX k (eT hpk zx) = eToX p zx from DFunLike.congr_fun (comm_eToX hpk) zx, hzx])
    obtain ⟨b₂, hmb₂, hb₂⟩ := hy m (eT hkm (eT hqk zy)) (by
      rw [show eToX m (eT hkm (eT hqk zy)) = eToX k (eT hqk zy) from
          DFunLike.congr_fun (comm_eToX hkm) _,
        show eToX k (eT hqk zy) = eToX q zy from DFunLike.congr_fun (comm_eToX hqk) zy, hzy])
    obtain ⟨b, hb₁b, hb₂b⟩ := directed b₁ b₂
    have hmb : le m b := le_trans' hmb₁ hb₁b
    have hakm : le a m := le_trans' hak hkm
    have hab : le a b := le_trans' hakm hmb
    refine ⟨b, hab, ?_⟩
    rw [show eT hab w = eT hmb (eT hkm (eT hak w)) from by
      rw [comp hak hkm hakm w, comp hakm hmb hab w], hm, map_add, map_add]
    refine Ideal.add_mem _ ?_ ?_
    · rw [show eT hmb (eT hkm (eT hpk zx)) = eT hb₁b (eT hmb₁ (eT hkm (eT hpk zx))) from
        (comp hmb₁ hb₁b hmb _).symm]
      exact push hb₁b _ hb₁
    · rw [show eT hmb (eT hkm (eT hqk zy)) = eT hb₂b (eT hmb₂ (eT hkm (eT hqk zy))) from
        (comp hmb₂ hb₂b hmb _).symm]
      exact push hb₂b _ hb₂
  have hsmul : ∀ (r : X) (x : X),
      (∀ (a : Λ) (w : E a), eToX a w = x →
        ∃ b, ∃ h : le a b, eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b)) →
      ∀ (a : Λ) (w : E a), eToX a w = r • x →
        ∃ b, ∃ h : le a b,
          eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b) := by
    intro r x hx a w hw
    rw [smul_eq_mul] at hw
    obtain ⟨p, zr, hzr⟩ := e_surj r
    obtain ⟨q, zx, hzx⟩ := e_surj x
    obtain ⟨k₁, hak₁, hpk₁⟩ := directed a p
    obtain ⟨k, hk₁k, hqk⟩ := directed k₁ q
    have hak : le a k := le_trans' hak₁ hk₁k
    have hpk : le p k := le_trans' hpk₁ hk₁k
    have key : eToX k (eT hak w) = eToX k (eT hpk zr * eT hqk zx) := by
      rw [map_mul,
        show eToX k (eT hak w) = eToX a w from DFunLike.congr_fun (comm_eToX hak) w,
        show eToX k (eT hpk zr) = eToX p zr from DFunLike.congr_fun (comm_eToX hpk) zr,
        show eToX k (eT hqk zx) = eToX q zx from DFunLike.congr_fun (comm_eToX hqk) zx,
        hw, hzr, hzx]
    obtain ⟨m, hkm, hm⟩ := e_sep k _ _ key
    obtain ⟨b, hmb, hb⟩ := hx m (eT hkm (eT hqk zx)) (by
      rw [show eToX m (eT hkm (eT hqk zx)) = eToX k (eT hqk zx) from
          DFunLike.congr_fun (comm_eToX hkm) _,
        show eToX k (eT hqk zx) = eToX q zx from DFunLike.congr_fun (comm_eToX hqk) zx, hzx])
    have hakm : le a m := le_trans' hak hkm
    have hab : le a b := le_trans' hakm hmb
    refine ⟨b, hab, ?_⟩
    rw [show eT hab w = eT hmb (eT hkm (eT hak w)) from by
      rw [comp hak hkm hakm w, comp hakm hmb hab w], hm, map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ hb
  have hgen : ∀ m ∈ IsLocalRing.maximalIdeal R, ∀ (a : Λ) (w : E a), eToX a w = φ m →
      ∃ b, ∃ h : le a b,
        eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b) := by
    intro m hm a w hw
    obtain ⟨p, y, hy⟩ := base_surj m
    haveI := isLocalHomBaseToR p
    have hymem : y ∈ IsLocalRing.maximalIdeal (Base p) := by
      have hcm : y ∈ (IsLocalRing.maximalIdeal R).comap (baseToR p) := by rw [Ideal.mem_comap, hy]; exact hm
      rwa [IsLocalRing.maximalIdeal_comap] at hcm
    obtain ⟨k, hak, hpk⟩ := directed a p
    haveI := isLocalHomBaseT hpk
    have key : eToX k (eT hak w) = eToX k (baseToE k (baseT hpk y)) := by
      rw [show eToX k (eT hak w) = eToX a w from DFunLike.congr_fun (comm_eToX hak) w, hw,
        show eToX k (baseToE k (baseT hpk y)) = φ (baseToR k (baseT hpk y)) from
          DFunLike.congr_fun (comm_baseE k) (baseT hpk y),
        show baseToR k (baseT hpk y) = baseToR p y from
          DFunLike.congr_fun (comm_baseToR hpk) y, hy]
    obtain ⟨b, hkb, hbeq⟩ := e_sep k _ _ key
    have hab : le a b := le_trans' hak hkb
    refine ⟨b, hab, ?_⟩
    haveI := isLocalHomBaseT hkb
    rw [show eT hab w = eT hkb (eT hak w) from (comp hak hkb hab w).symm, hbeq,
      show eT hkb (baseToE k (baseT hpk y)) = baseToE b (baseT hkb (baseT hpk y)) from
        (DFunLike.congr_fun (comm_baseT hkb) (baseT hpk y)).symm]
    refine Ideal.mem_map_of_mem _ ?_
    have h2 : baseT hpk y ∈ IsLocalRing.maximalIdeal (Base k) := by
      have h3 : y ∈ (IsLocalRing.maximalIdeal (Base k)).comap (baseT hpk) := by
        rw [IsLocalRing.maximalIdeal_comap]; exact hymem
      exact h3
    have h4 : baseT hpk y ∈ (IsLocalRing.maximalIdeal (Base b)).comap (baseT hkb) := by
      rw [IsLocalRing.maximalIdeal_comap]; exact h2
    exact h4
  let J : Ideal X :=
    { carrier := {x : X | ∀ (a : Λ) (w : E a), eToX a w = x →
        ∃ b, ∃ h : le a b, eT h w ∈ (IsLocalRing.maximalIdeal (Base b)).map (baseToE b)}
      zero_mem' := hzero
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      smul_mem' := fun r x hx => hsmul r x hx }
  have hmaple : (IsLocalRing.maximalIdeal R).map φ ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    exact hgen m hm
  exact hmaple hz i z rfl

/-- `S/𝔪_R S → S'/𝔪_R S'`, the colimit of the fibre system.  This is the map
`exists_flatFibre_index_of_noetherianApproxSystem` assumes flat, written as a definition so
that it can be handed to `exists_flat_index_of_isNoetherianFlatDescentSystem` as the `w`
of the fibre system without a transport. -/
def fibreBaseMap {R B A : Type u} [CommRing R] [CommRing B] [CommRing A] [IsLocalRing R]
    (g : R →+* B) (v : B →+* A) :
    (B ⧸ (IsLocalRing.maximalIdeal R).map g) →+*
      (A ⧸ (IsLocalRing.maximalIdeal R).map (v.comp g)) :=
  Ideal.quotientMap _ v (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))

@[simp] theorem fibreBaseMap_mk {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] (g : R →+* B) (v : B →+* A) (x : B) :
    fibreBaseMap g v (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (v x) :=
  Ideal.quotientMap_mk

namespace NoetherianApproxSystem

section FibreSystem

variable {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]

omit [IsLocalRing B] [IsLocalRing A] [IsLocalHom g] [IsLocalHom v] in
/-- **`𝔪_R S` IS THE UNION OF THE IMAGES OF THE `𝔭_λ S_λ`** (**PROVEN 2026-07-28**; one of
the three pieces of the fibre-system verification, which is what
`exists_flatFibre_index_of_noetherianApproxSystem` owns beyond the shared 10.128.3 core).

This is the load-bearing half of 00R7's sentence "the colimit of the fibre system is
`S/𝔪_R S → S'/𝔪_R S'`", and it is where the LOCALITY of the cocone maps
(`isLocalHomBaseToR`) is spent — the field exists for this leaf.

The body is one application of `exists_mem_map_maximalIdeal_of_colimitTower` above, to the
`Mid` tower with `φ = g`; see that lemma's docstring for the argument.

**A NOTE ON THE ROUTE, since the plan recorded here was different.**  The proof sketch this
docstring used to carry ran through an explicit finite expansion `midToB i z = ∑_k b_k·g m_k`
and then aligned finitely many indices with `directed`.  That works, but the `Finset`
bookkeeping is entirely avoidable: the set of elements of `B` that *are* witnessed by a stage
ideal is itself an IDEAL of `B` (that is `hzero`/`hadd`/`hsmul` in the lemma above), so
`Ideal.map_le_iff_le_comap` reduces the whole statement to the GENERATORS `g m`, `m ∈ 𝔪_R`,
where the argument is the four-line one the old sketch gave for a single term.  Each closure
step needs only `directed` twice and one `e_sep`.  No sum is ever formed.

**FAITHFULNESS.**  Stated as the cofinal `∃ j ≥ i` because that is what the colimit
argument delivers and what `c_sep` of the fibre system needs; the converse inclusion
(`𝔭_j S_j` maps into `𝔪_R S`) is `fibreIdealMid_le_comap_midToB`, PROVEN above, so this
leaf is exactly the half that is not formal. -/
theorem exists_mem_fibreIdealMid (sys : NoetherianApproxSystem g v) (i : sys.Λ)
    (z : sys.Mid i) (hz : sys.midToB i z ∈ (IsLocalRing.maximalIdeal R).map g) :
    ∃ j, ∃ h : sys.le i j, sys.midT h z ∈ sys.fibreIdealMid j :=
  exists_mem_map_maximalIdeal_of_colimitTower
    (Base := fun i => sys.Base i) (E := fun i => sys.Mid i)
    (hLocBase := sys.isLocalRingBase)
    (baseT := fun {_ _} h => sys.baseT h) (eT := fun {_ _} h => sys.midT h)
    (baseToE := sys.baseToMid) (baseToR := sys.baseToR) (eToX := sys.midToB)
    (le_trans' := fun {_ _ _} h₁ h₂ => sys.le_trans' h₁ h₂)
    (directed := sys.directed) (eT_comp := fun {_ _ _} h₁ h₂ => sys.midT_comp h₁ h₂)
    (comm_baseE := sys.comm_baseMid) (comm_baseT := fun {_ _} h => sys.comm_baseT h)
    (comm_baseToR := fun {_ _} h => sys.comm_baseToR h)
    (comm_eToX := fun {_ _} h => sys.comm_midToB h)
    (isLocalHomBaseT := fun {_ _} h => sys.isLocalHomBaseT h)
    (isLocalHomBaseToR := sys.isLocalHomBaseToR)
    (base_surj := sys.base_surj) (e_surj := sys.mid_surj) (e_sep := sys.mid_sep)
    i z hz

omit [IsLocalRing B] [IsLocalRing A] [IsLocalHom g] [IsLocalHom v] in
/-- **`𝔪_R S'` IS THE UNION OF THE IMAGES OF THE `𝔭_λ S'_λ`** (**PROVEN 2026-07-28**).  The
same argument as `exists_mem_fibreIdealMid`, run on the `Tot` tower: `base_surj` plus
locality of `baseToR` to put the generators at a stage, `directed` to align the indices,
`tot_sep` to close the gap.  Both are stated because the fibre system needs `c_sep` and
`d_sep` separately; this docstring's instruction to "factor the common argument out into a
lemma about a single tower over the `Base` system rather than writing it twice" is what
`exists_mem_map_maximalIdeal_of_colimitTower` above is, and both leaves are now a single
application of it apiece.

The one thing the `Tot` instance has to say that the `Mid` one does not: its `baseToE` is the
COMPOSITE `midToTot i ∘ baseToMid i`, because that is the map `fibreIdealTot` is the
`Ideal.map` along, and its two commuting squares are therefore the `comm_baseT`/`comm_midT`
and `comm_midTot`/`comm_baseMid` pairs pasted — the same two `rw` chains that
`isNoetherianFlatDescentSystem_baseTot` uses for `comm_T` and `comm_cocone`. -/
theorem exists_mem_fibreIdealTot (sys : NoetherianApproxSystem g v) (i : sys.Λ)
    (z : sys.Tot i) (hz : sys.totToA i z ∈ (IsLocalRing.maximalIdeal R).map (v.comp g)) :
    ∃ j, ∃ h : sys.le i j, sys.totT h z ∈ sys.fibreIdealTot j :=
  exists_mem_map_maximalIdeal_of_colimitTower
    (Base := fun i => sys.Base i) (E := fun i => sys.Tot i)
    (hLocBase := sys.isLocalRingBase)
    (baseT := fun {_ _} h => sys.baseT h) (eT := fun {_ _} h => sys.totT h)
    (baseToE := fun i => (sys.midToTot i).comp (sys.baseToMid i))
    (baseToR := sys.baseToR) (eToX := sys.totToA)
    (le_trans' := fun {_ _ _} h₁ h₂ => sys.le_trans' h₁ h₂)
    (directed := sys.directed) (eT_comp := fun {_ _ _} h₁ h₂ => sys.totT_comp h₁ h₂)
    (comm_baseE := fun i => by
      rw [← RingHom.comp_assoc, sys.comm_midTot i, RingHom.comp_assoc, sys.comm_baseMid i,
        ← RingHom.comp_assoc])
    (comm_baseT := fun {_ _} h => by
      rw [RingHom.comp_assoc, sys.comm_baseT h, ← RingHom.comp_assoc, sys.comm_midT h,
        RingHom.comp_assoc])
    (comm_baseToR := fun {_ _} h => sys.comm_baseToR h)
    (comm_eToX := fun {_ _} h => sys.comm_totToA h)
    (isLocalHomBaseT := fun {_ _} h => sys.isLocalHomBaseT h)
    (isLocalHomBaseToR := sys.isLocalHomBaseToR)
    (base_surj := sys.base_surj) (e_surj := sys.tot_surj) (e_sep := sys.tot_sep)
    i z hz

omit [IsLocalRing R] [IsLocalRing B] [IsLocalRing A] [IsLocalHom g] [IsLocalHom v] in
/-- **THE LOCALIZATION PROPERTY OF THE FIBRE SYSTEM** (**PROVEN 2026-07-28**; the third
piece of the fibre-system verification).

*`S'_μ/𝔭_μ S'_μ` is a localization of `(S_μ/𝔭_μ S_μ) ⊗_{S_λ/𝔭_λ S_λ} (S'_λ/𝔭_λ S'_λ)`.*

**THE PROOF AS WRITTEN, and how it differs from the sketch this docstring used to carry.**
The old sketch chained three steps — "localization commutes with quotients", then
`(S_μ ⊗_{S_λ} S'_λ)/𝔭_μ ≅ (S_μ/𝔭_μ) ⊗_{S_λ} S'_λ`, then the base-change identification
`M ⊗_R N ≅ M ⊗_{R/I} (N/IN)` for `IM = 0` — and so needed two ISOMORPHISMS of tensor
products that this pin states only in special shapes.  None of that is necessary: mathlib's
`IsLocalization.of_surjective` takes the whole thing in one step, and it asks only for a
SURJECTION, never an isomorphism.

Write `T = S_μ ⊗_{S_λ} S'_λ` and `Q = (S_μ/𝔭_μ) ⊗_{S_λ/𝔭_λ} (S'_λ/𝔭_λ S'_λ)`.
`isLocalizationTotT` gives `W ≤ T` with `S'_μ = W^{-1}T`.  Build
`f : T →+* Q` by `Algebra.TensorProduct.lift` of the two composites
`S_μ ↠ S_μ/𝔭_μ ↪ Q` and `S'_λ ↠ S'_λ/𝔭_λ S'_λ ↪ Q` (the second is an `S_λ`-algebra map
because `includeLeftRingHom ∘ algebraMap = includeRight ∘ algebraMap` into `Q`, which is
`Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap`).  Then
`IsLocalization.of_surjective W S'_μ f hf (Ideal.Quotient.mk _) _ H H'` gives
`IsLocalization (W.map f) (S'_μ/𝔭_μ S'_μ)`, so `W.map f` is the required submonoid.  Its
two side conditions are:

* `H`, that the square commutes — checked on pure tensors, where both sides are
  `[x] · [y]` in `S'_μ/𝔭_μ`;
* `H'`, that `ker(S'_μ ↠ S'_μ/𝔭_μ S'_μ) = 𝔭_μ S'_μ` lies in `(ker f) · S'_μ`.

**THE ONE ARITHMETIC INPUT, and a correction to the old sketch.**  `H'` is exactly
`𝔭_μ S'_μ = (𝔭_μ S_μ)·S'_μ`, i.e. `fibreIdealTot j = (fibreIdealMid j).map (midToTot j)`,
which is `Ideal.map_map` applied to the two definitions — the maximal ideal of `R_μ` may be
pushed to `S'_μ` through `S_μ` or directly.  So only the LEFT tensor factor contributes
generators of `ker f`, and `fibreIdealMid_le_comap_midT` (`𝔭_λ S_μ ⊆ 𝔭_μ S_μ`), which the
old sketch named as load-bearing, is NOT used here at all: it is what makes the RIGHT
factor's quotient legitimate, and that is already discharged by `Q` being formed over
`S_λ/𝔭_λ`.  The old sketch was not wrong, only more expensive than needed.

**WHY IT IS NOT AN ISOMORPHISM.**  For the same reason `isLocalizationTotT` is not — see
the CORRECTION block in the section note "THE CUT OF THE APPROXIMATION LEAF"; a quotient
of a localization is a localization, not an isomorphism, and asking for more here would
make the leaf false.  Note the proof CONSUMES that weakness rather than fighting it:
`of_surjective` transports `IsLocalization` along a surjection in exactly this generality.

**WHY THE LOCALITY HYPOTHESES ARE OMITTED.**  `[IsLocalRing R] [IsLocalRing B]
[IsLocalRing A] [IsLocalHom g] [IsLocalHom v]` are section variables that neither the
statement nor the proof touches — the whole leaf lives at `FibreData` level, over the
stagewise ideals `𝔭_λ` alone — so they are `omit`ted to keep the module warning-clean.
That is a weakening of the hypotheses, not of the conclusion; the consumer
`isNoetherianFlatDescentSystem_fibre` applies it unchanged.  (The `omit` line must precede
the doc comment, not sit between it and the `theorem`: a doc comment binds to a
DECLARATION, so `/-- … -/ omit … in theorem` is a parse error reported at the END of the
docstring as `unexpected token 'omit'; expected 'lemma'`.) -/
theorem exists_isLocalization_fibre (sys : NoetherianApproxSystem g v) {i j : sys.Λ}
    (h : sys.le i j) :
    letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot i ⧸ sys.fibreIdealTot i) :=
      (sys.fibreCD i).toAlgebra
    letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Mid j ⧸ sys.fibreIdealMid j) :=
      (sys.fibreCT h).toAlgebra
    letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
      ((sys.fibreCD j).comp (sys.fibreCT h)).toAlgebra
    letI : Algebra (sys.Mid j ⧸ sys.fibreIdealMid j) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
      (sys.fibreCD j).toAlgebra
    letI : Algebra (sys.Tot i ⧸ sys.fibreIdealTot i) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
      (sys.fibreDT h).toAlgebra
    haveI : IsScalarTower (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Mid j ⧸ sys.fibreIdealMid j)
        (sys.Tot j ⧸ sys.fibreIdealTot j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot i ⧸ sys.fibreIdealTot i)
        (sys.Tot j ⧸ sys.fibreIdealTot j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.fibre_comm_T h) x
    letI : Algebra ((sys.Mid j ⧸ sys.fibreIdealMid j) ⊗[sys.Mid i ⧸ sys.fibreIdealMid i]
        (sys.Tot i ⧸ sys.fibreIdealTot i)) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
      (Algebra.TensorProduct.lift
        (IsScalarTower.toAlgHom (sys.Mid i ⧸ sys.fibreIdealMid i)
          (sys.Mid j ⧸ sys.fibreIdealMid j) (sys.Tot j ⧸ sys.fibreIdealTot j))
        (IsScalarTower.toAlgHom (sys.Mid i ⧸ sys.fibreIdealMid i)
          (sys.Tot i ⧸ sys.fibreIdealTot i) (sys.Tot j ⧸ sys.fibreIdealTot j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid ((sys.Mid j ⧸ sys.fibreIdealMid j) ⊗[sys.Mid i ⧸ sys.fibreIdealMid i]
      (sys.Tot i ⧸ sys.fibreIdealTot i)), IsLocalization W (sys.Tot j ⧸ sys.fibreIdealTot j) := by
  -- The fibre-level structures, exactly as the statement inlines them.
  letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot i ⧸ sys.fibreIdealTot i) :=
    (sys.fibreCD i).toAlgebra
  letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Mid j ⧸ sys.fibreIdealMid j) :=
    (sys.fibreCT h).toAlgebra
  letI : Algebra (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
    ((sys.fibreCD j).comp (sys.fibreCT h)).toAlgebra
  letI : Algebra (sys.Mid j ⧸ sys.fibreIdealMid j) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
    (sys.fibreCD j).toAlgebra
  letI : Algebra (sys.Tot i ⧸ sys.fibreIdealTot i) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
    (sys.fibreDT h).toAlgebra
  haveI : IsScalarTower (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Mid j ⧸ sys.fibreIdealMid j)
      (sys.Tot j ⧸ sys.fibreIdealTot j) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot i ⧸ sys.fibreIdealTot i)
      (sys.Tot j ⧸ sys.fibreIdealTot j) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.fibre_comm_T h) x
  letI : Algebra ((sys.Mid j ⧸ sys.fibreIdealMid j) ⊗[sys.Mid i ⧸ sys.fibreIdealMid i]
      (sys.Tot i ⧸ sys.fibreIdealTot i)) (sys.Tot j ⧸ sys.fibreIdealTot j) :=
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (sys.Mid i ⧸ sys.fibreIdealMid i)
        (sys.Mid j ⧸ sys.fibreIdealMid j) (sys.Tot j ⧸ sys.fibreIdealTot j))
      (IsScalarTower.toAlgHom (sys.Mid i ⧸ sys.fibreIdealMid i)
        (sys.Tot i ⧸ sys.fibreIdealTot i) (sys.Tot j ⧸ sys.fibreIdealTot j))
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  -- The upstairs structures, exactly as `isLocalizationTotT` states them.
  letI : Algebra (sys.Mid i) (sys.Tot i) := (sys.midToTot i).toAlgebra
  letI : Algebra (sys.Mid i) (sys.Mid j) := (sys.midT h).toAlgebra
  letI : Algebra (sys.Mid i) (sys.Tot j) := ((sys.midToTot j).comp (sys.midT h)).toAlgebra
  letI : Algebra (sys.Mid j) (sys.Tot j) := (sys.midToTot j).toAlgebra
  letI : Algebra (sys.Tot i) (sys.Tot j) := (sys.totT h).toAlgebra
  haveI : IsScalarTower (sys.Mid i) (sys.Mid j) (sys.Tot j) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (sys.Mid i) (sys.Tot i) (sys.Tot j) :=
    IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.comm_midT h) x
  letI : Algebra (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j) :=
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (sys.Mid i) (sys.Mid j) (sys.Tot j))
      (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) (sys.Tot j))
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  obtain ⟨W, hW⟩ := sys.isLocalizationTotT h
  -- The `S_λ`-algebra structure on the fibre tensor product `Q`, through the left factor.
  letI : Algebra (sys.Mid i) ((sys.Mid j ⧸ sys.fibreIdealMid j)
      ⊗[sys.Mid i ⧸ sys.fibreIdealMid i] (sys.Tot i ⧸ sys.fibreIdealTot i)) :=
    (Algebra.TensorProduct.includeLeftRingHom.comp
      ((Ideal.Quotient.mk (sys.fibreIdealMid j)).comp (sys.midT h))).toAlgebra
  have hleft : ∀ x : sys.Mid i,
      algebraMap (sys.Mid i) ((sys.Mid j ⧸ sys.fibreIdealMid j)
        ⊗[sys.Mid i ⧸ sys.fibreIdealMid i] (sys.Tot i ⧸ sys.fibreIdealTot i)) x
      = Algebra.TensorProduct.includeLeftRingHom
          (Ideal.Quotient.mk (sys.fibreIdealMid j) (sys.midT h x)) := fun _ => rfl
  -- `S_μ → Q` and `S'_λ → Q` as `S_λ`-algebra maps.
  let φ₁ : sys.Mid j →ₐ[sys.Mid i] ((sys.Mid j ⧸ sys.fibreIdealMid j)
      ⊗[sys.Mid i ⧸ sys.fibreIdealMid i] (sys.Tot i ⧸ sys.fibreIdealTot i)) :=
    { Algebra.TensorProduct.includeLeftRingHom.comp
        (Ideal.Quotient.mk (sys.fibreIdealMid j)) with
      commutes' := fun _ => rfl }
  let φ₂ : sys.Tot i →ₐ[sys.Mid i] ((sys.Mid j ⧸ sys.fibreIdealMid j)
      ⊗[sys.Mid i ⧸ sys.fibreIdealMid i] (sys.Tot i ⧸ sys.fibreIdealTot i)) :=
    { (Algebra.TensorProduct.includeRight :
          (sys.Tot i ⧸ sys.fibreIdealTot i) →ₐ[sys.Mid i ⧸ sys.fibreIdealMid i] _).toRingHom.comp
        (Ideal.Quotient.mk (sys.fibreIdealTot i)) with
      commutes' := by
        intro x
        show Algebra.TensorProduct.includeRight
            (Ideal.Quotient.mk (sys.fibreIdealTot i) (sys.midToTot i x)) = _
        have e1 : Ideal.Quotient.mk (sys.fibreIdealTot i) (sys.midToTot i x)
            = algebraMap (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Tot i ⧸ sys.fibreIdealTot i)
                (Ideal.Quotient.mk (sys.fibreIdealMid i) x) := by
          rw [RingHom.algebraMap_toAlgebra]
          exact (sys.fibreCD_mk i x).symm
        have e2 : Ideal.Quotient.mk (sys.fibreIdealMid j) (sys.midT h x)
            = algebraMap (sys.Mid i ⧸ sys.fibreIdealMid i) (sys.Mid j ⧸ sys.fibreIdealMid j)
                (Ideal.Quotient.mk (sys.fibreIdealMid i) x) := by
          rw [RingHom.algebraMap_toAlgebra]
          exact (sys.fibreCT_mk h x).symm
        rw [hleft x, e1, e2]
        exact (DFunLike.congr_fun
          (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
            (R := sys.Mid i ⧸ sys.fibreIdealMid i) (A := sys.Mid j ⧸ sys.fibreIdealMid j)
            (B := sys.Tot i ⧸ sys.fibreIdealTot i))
          (Ideal.Quotient.mk (sys.fibreIdealMid i) x)).symm }
  -- `f : T ↠ Q`, the surjection `of_surjective` runs on.
  let f : (sys.Mid j ⊗[sys.Mid i] sys.Tot i) →+*
      ((sys.Mid j ⧸ sys.fibreIdealMid j) ⊗[sys.Mid i ⧸ sys.fibreIdealMid i]
        (sys.Tot i ⧸ sys.fibreIdealTot i)) :=
    (Algebra.TensorProduct.lift φ₁ φ₂ fun _ _ => Commute.all _ _).toRingHom
  have hf_tmul : ∀ (x : sys.Mid j) (y : sys.Tot i),
      f (x ⊗ₜ[sys.Mid i] y)
        = (Ideal.Quotient.mk (sys.fibreIdealMid j) x) ⊗ₜ
            (Ideal.Quotient.mk (sys.fibreIdealTot i) y) := by
    intro x y
    show φ₁ x * φ₂ y = _
    show (Ideal.Quotient.mk (sys.fibreIdealMid j) x ⊗ₜ (1 : sys.Tot i ⧸ sys.fibreIdealTot i)) *
        ((1 : sys.Mid j ⧸ sys.fibreIdealMid j) ⊗ₜ Ideal.Quotient.mk (sys.fibreIdealTot i) y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : Function.Surjective f := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c d =>
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
        exact ⟨x ⊗ₜ[sys.Mid i] y, hf_tmul x y⟩
    | add z w hz hw =>
        obtain ⟨a, rfl⟩ := hz
        obtain ⟨b, rfl⟩ := hw
        exact ⟨a + b, map_add _ _ _⟩
  have halg_tmul : ∀ (x : sys.Mid j) (y : sys.Tot i),
      algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j) (x ⊗ₜ[sys.Mid i] y)
        = sys.midToTot j x * sys.totT h y := fun _ _ => rfl
  -- The square commutes.
  have hH : (Ideal.Quotient.mk (sys.fibreIdealTot j)).comp
      (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)) =
      (algebraMap ((sys.Mid j ⧸ sys.fibreIdealMid j) ⊗[sys.Mid i ⧸ sys.fibreIdealMid i]
        (sys.Tot i ⧸ sys.fibreIdealTot i)) (sys.Tot j ⧸ sys.fibreIdealTot j)).comp f := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        simp only [RingHom.comp_apply, halg_tmul, hf_tmul, map_mul]
        show Ideal.Quotient.mk _ (sys.midToTot j x) * Ideal.Quotient.mk _ (sys.totT h y) = _
        rw [RingHom.algebraMap_toAlgebra]
        show _ = (Algebra.TensorProduct.lift _ _ _)
          (Ideal.Quotient.mk (sys.fibreIdealMid j) x ⊗ₜ Ideal.Quotient.mk (sys.fibreIdealTot i) y)
        rw [Algebra.TensorProduct.lift_tmul]
        show _ = algebraMap (sys.Mid j ⧸ sys.fibreIdealMid j) (sys.Tot j ⧸ sys.fibreIdealTot j)
            (Ideal.Quotient.mk _ x) *
          algebraMap (sys.Tot i ⧸ sys.fibreIdealTot i) (sys.Tot j ⧸ sys.fibreIdealTot j)
            (Ideal.Quotient.mk _ y)
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, sys.fibreCD_mk,
          sys.fibreDT_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  -- `𝔭_μ S'_μ = (𝔭_μ S_μ)·S'_μ` lands inside `(ker f)·S'_μ`.
  have hker : sys.fibreIdealTot j
      ≤ (RingHom.ker f).map (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)) := by
    letI := sys.isLocalRingBase j
    have hmapeq : sys.fibreIdealTot j = (sys.fibreIdealMid j).map (sys.midToTot j) := by
      rw [sys.fibreIdealMid_eq j, Ideal.map_map, sys.fibreIdealTot_eq j]
    rw [hmapeq, Ideal.map_le_iff_le_comap]
    intro x hx
    have hmem : (x ⊗ₜ[sys.Mid i] (1 : sys.Tot i)) ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, hf_tmul]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, TensorProduct.zero_tmul]
    have := Ideal.mem_map_of_mem
      (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)) hmem
    rw [halg_tmul, map_one, mul_one] at this
    exact this
  exact ⟨W.map f, IsLocalization.of_surjective W (sys.Tot j) f hf
    (Ideal.Quotient.mk (sys.fibreIdealTot j)) Ideal.Quotient.mk_surjective hH
    (by rw [Ideal.mk_ker]; exact hker)⟩

/-- **THE FIBRE SYSTEM IS AGAIN A NOETHERIAN DESCENT SYSTEM** (PROVEN over the three leaves
above).  This is 00R7's paragraph beginning "Note that this also implies", and it is the
part of `exists_flatFibre_index_of_noetherianApproxSystem` that is NOT shared with the base
application — which is why the two leaves were given one owner and why the naive three-way
split "10.127.13 / 10.128.3 / assembly" was rejected (see the section note "THE CUT OF THE
APPROXIMATION LEAF").

Everything formal is discharged here: Noetherianity and locality of the quotients, the
functoriality of `Ideal.quotientMap`, the commuting squares, and the surjectivity half of
both colimit conditions.  What is left over is exactly the three leaves above — the two
"the maximal ideal is the union of the stage ideals" statements, where the locality of
`baseToR` is spent, and the quotient of the localization property.

**STATUS, 2026-07-28**: the third of those, `exists_isLocalization_fibre`, is now PROVEN,
so only the two `exists_mem_fibreIdealMid` / `exists_mem_fibreIdealTot` statements remain
open here.  Do not read "the three leaves above" as a live frontier count; regenerate it
from the compiler's `declaration uses 'sorry'` set. -/
theorem isNoetherianFlatDescentSystem_fibre (sys : NoetherianApproxSystem g v) :
    IsNoetherianFlatDescentSystem sys.le
      (fun i => sys.Mid i ⧸ sys.fibreIdealMid i) (fun i => sys.Tot i ⧸ sys.fibreIdealTot i)
      sys.fibreCD (fun {_ _} h => sys.fibreCT h) (fun {_ _} h => sys.fibreDT h)
      (fibreBaseMap g v) sys.fibreCToC sys.fibreDToD where
  le_rfl := sys.le_rfl
  le_trans' := sys.le_trans'
  directed := sys.directed
  isLocalRingC i := by
    letI := sys.isLocalRingBase i
    letI := sys.isLocalRingMid i
    haveI := sys.isLocalHomBaseToMid i
    haveI : Nontrivial (sys.Mid i ⧸ sys.fibreIdealMid i) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top (sys.baseToMid i)))
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  isLocalRingD i := by
    letI := sys.isLocalRingBase i
    letI := sys.isLocalRingTot i
    haveI := sys.isLocalHomBaseToMid i
    haveI := sys.isLocalHomMidToTot i
    haveI : Nontrivial (sys.Tot i ⧸ sys.fibreIdealTot i) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top
          ((sys.midToTot i).comp (sys.baseToMid i))))
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  isNoetherianC i := by
    haveI := sys.isNoetherianMid i; infer_instance
  isNoetherianD i := by
    haveI := sys.isNoetherianTot i; infer_instance
  isLocalHomCD i := by
    letI := sys.isLocalRingBase i
    letI := sys.isLocalRingTot i
    haveI := sys.isLocalHomBaseToMid i
    haveI := sys.isLocalHomMidToTot i
    exact isLocalHom_quotientMap _ _
      (IsLocalRing.map_maximalIdeal_le ((sys.midToTot i).comp (sys.baseToMid i)))
  cT_comp h₁ h₂ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, fibreCT_mk]
    exact congrArg _ (DFunLike.congr_fun (sys.midT_comp h₁ h₂) x)
  dT_comp h₁ h₂ := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, fibreDT_mk]
    exact congrArg _ (DFunLike.congr_fun (sys.totT_comp h₁ h₂) x)
  comm_T h := sys.fibre_comm_T h
  isLocalHomCT := fun {_ j} h => by
    letI := sys.isLocalRingBase j
    letI := sys.isLocalRingMid j
    haveI := sys.isLocalHomMidT h
    haveI := sys.isLocalHomBaseToMid j
    exact isLocalHom_quotientMap _ _ (IsLocalRing.map_maximalIdeal_le (sys.baseToMid j))
  isLocalHomDT := fun {_ j} h => by
    letI := sys.isLocalRingBase j
    letI := sys.isLocalRingTot j
    haveI := sys.isLocalHomTotT h
    haveI := sys.isLocalHomBaseToMid j
    haveI := sys.isLocalHomMidToTot j
    exact isLocalHom_quotientMap _ _
      (IsLocalRing.map_maximalIdeal_le ((sys.midToTot j).comp (sys.baseToMid j)))
  comm_cocone i := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, fibreCD_mk, fibreDToD_mk, fibreCToC_mk, fibreBaseMap_mk]
    exact congrArg _ (DFunLike.congr_fun (sys.comm_midTot i) x)
  comm_cToC h := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, fibreCT_mk, fibreCToC_mk]
    exact congrArg _ (DFunLike.congr_fun (sys.comm_midToB h) x)
  comm_dToD h := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, fibreDT_mk, fibreDToD_mk]
    exact congrArg _ (DFunLike.congr_fun (sys.comm_totToA h) x)
  isLocalHomCToC i := by
    haveI := sys.isLocalHomMidToB i
    exact isLocalHom_quotientMap _ _ (IsLocalRing.map_maximalIdeal_le g)
  isLocalHomDToD i := by
    haveI := sys.isLocalHomTotToA i
    exact isLocalHom_quotientMap _ _ (IsLocalRing.map_maximalIdeal_le (v.comp g))
  c_surj x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨i, y, hy⟩ := sys.mid_surj b
    exact ⟨i, Ideal.Quotient.mk _ y, by rw [sys.fibreCToC_mk i y, hy]⟩
  d_surj x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨i, y, hy⟩ := sys.tot_surj a
    exact ⟨i, Ideal.Quotient.mk _ y, by rw [sys.fibreDToD_mk i y, hy]⟩
  c_sep i x y hxy := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [sys.fibreCToC_mk i a, sys.fibreCToC_mk i b,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub] at hxy
    obtain ⟨j, h, hj⟩ := sys.exists_mem_fibreIdealMid i (a - b) hxy
    refine ⟨j, h, ?_⟩
    rw [sys.fibreCT_mk h a, sys.fibreCT_mk h b, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
    exact hj
  d_sep i x y hxy := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [sys.fibreDToD_mk i a, sys.fibreDToD_mk i b,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub] at hxy
    obtain ⟨j, h, hj⟩ := sys.exists_mem_fibreIdealTot i (a - b) hxy
    refine ⟨j, h, ?_⟩
    rw [sys.fibreDT_mk h a, sys.fibreDT_mk h b, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
    exact hj
  isLocalizationDT h := sys.exists_isLocalization_fibre h

end FibreSystem

end NoetherianApproxSystem

/-- **STACKS 10.128.3, FIRST APPLICATION: flatness over the base descends to a
stage** (cut 2026-07-28; **PROVEN 2026-07-28** over the shared engine
`exists_flat_index_of_isNoetherianFlatDescentSystem` — read the section note "10.128.3 IS
ONE LEMMA APPLIED TWICE" above first).

*If `M = A` is flat over `R`, then in any `NoetherianApproxSystem` and cofinally
in `Λ`, `S'_j` is flat over `R_j`.*

**Why the conclusion is `∀ i, ∃ j ≥ i` and not `∃ j`.**  Because that is what
10.128.3's proof gives, and because it is the only form that composes with the
fibre leaf below — see the section note.  Restricting the system to `{j | i ≤ j}`
turns the cofinal form back into the bare `∃ j`, so this is not a strengthening.

**WHERE THE PROOF WENT.**  The argument that used to be recorded here — the
`Tor_1^{R_i}(S'_i, R_i/𝔪_i)` computation and the passage to a large `j` — is
10.128.3 itself, and it is now stated once, for an abstract two-tower system, as
`exists_flat_index_of_isNoetherianFlatDescentSystem`; read its docstring for the
argument and for what blocks it at this pin.  All that is left here is to exhibit
the `Base → Tot` tower of `sys` as such a system, which is
`NoetherianApproxSystem.isNoetherianFlatDescentSystem_baseTot`, PROVEN — and whose
`isLocalizationDT` field is `sys.isLocalizationTotBaseT` verbatim.

**FAITHFULNESS.**  The statement quantifies over ALL systems, so it cannot be
weakened by a bad choice of system upstream; and it uses only fields the source's
argument uses (`isNoetherianTot`, the six colimit conditions, and the locality of
the cocone maps).  It says nothing when `Λ` is empty, which is why
`nonemptyΛ` is a field of the system rather than a hypothesis here. -/
theorem exists_flatBase_index_of_noetherianApproxSystem
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (sys : NoetherianApproxSystem g v)
    (hflat : (v.comp g).Flat) (i : sys.Λ) :
    ∃ j : sys.Λ, ∃ _ : sys.le i j, ((sys.midToTot j).comp (sys.baseToMid j)).Flat :=
  exists_flat_index_of_isNoetherianFlatDescentSystem
    sys.isNoetherianFlatDescentSystem_baseTot hflat i

/-- **STACKS 10.128.3, SECOND APPLICATION: fibre flatness descends to a stage**
(cut 2026-07-28; **PROVEN 2026-07-28** over the shared engine
`exists_flat_index_of_isNoetherianFlatDescentSystem` and the fibre-system verification —
read the section note "10.128.3 IS ONE LEMMA APPLIED TWICE" above first).

*If `A/𝔪_R A` is flat over `B/𝔪_R B`, then in any `NoetherianApproxSystem` and
cofinally in `Λ`, `S'_j/𝔭_j S'_j` is flat over `S_j/𝔭_j S_j`, where
`𝔭_j = 𝔪_{R_j}`.*

**THIS LEAF OWNS THE FIBRE-SYSTEM VERIFICATION.**  That is the paragraph of
00R7's proof beginning "Note that this also implies", and it is why the naive
three-way split "10.127.13 / 10.128.3 / assembly" was rejected: the check that
`(S_λ/𝔭_λ S_λ → S'_λ/𝔭_λ S'_λ)` is again a system as in 10.127.13 is substantial,
so it must live inside a leaf and not in glue.  Concretely, for `λ ≤ μ` the
quotients of `isLocalizationMidT` and `isLocalizationTotT` are again
localizations (a localization base-changes to a localization, and quotients
commute with base change), each `S_λ/𝔭_λ S_λ` is Noetherian local because
`S_λ` is, and the colimit of the fibre system is `S/𝔪_R S → S'/𝔪_R S'` because
the cocone maps are LOCAL (`isLocalHomBaseToR`), which is exactly what makes
`𝔪_R` the union of the images of the `𝔪_{R_λ}`: if `x ∈ 𝔪_R` comes from
`y ∈ R_λ`, then `y` is not a unit — a unit would map to a unit — so
`y ∈ 𝔪_{R_λ}`.  With that in hand, 10.128.3 applies verbatim to the fibre system
over `{j | i ≤ j}` and yields the cofinal conclusion.

**AND IT IS NOW DISCHARGED, as `isNoetherianFlatDescentSystem_fibre`** (2026-07-28).
Everything formal in that paragraph is PROVEN there — Noetherianity and locality of
`S_λ/𝔭_λ S_λ` and `S'_λ/𝔭_λ S'_λ`, functoriality and locality of the quotient
transition maps, the commuting squares, and the surjectivity half of both colimit
conditions.  What survives as sorries is exactly the three named leaves
`exists_mem_fibreIdealMid`, `exists_mem_fibreIdealTot` (the two "`𝔪_R` is the union of
the images of the `𝔭_λ`" statements, where `isLocalHomBaseToR` is spent) and
`exists_isLocalization_fibre`.  The second application of 10.128.3 itself is NOT here:
it is the shared engine above, which the base application uses too.

**FAITHFULNESS.**  As for the first application: it quantifies over all systems
and uses only fields of the structure.  Note the ideal is `𝔪_{R_j}`, the maximal
ideal of the STAGE — not the contraction of `𝔪_R` — because that is what
`FlatNoetherianStage.flatFibre` asks for and what 00R7 writes (`𝔭_λ`).  The
`Ideal.quotientMap` written out in the conclusion is, on the nose,
`sys.fibreCD j` — which is why the descent system is a predicate over given data and
not a bundled structure: no transport of `RingHom.Flat` is needed anywhere. -/
theorem exists_flatFibre_index_of_noetherianApproxSystem
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (sys : NoetherianApproxSystem g v)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) (i : sys.Λ) :
    ∃ j : sys.Λ, ∃ _ : sys.le i j,
      letI := sys.isLocalRingBase j
      (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal (sys.Base j)).map
          ((sys.midToTot j).comp (sys.baseToMid j)))
        (sys.midToTot j)
        (map_le_comap_map_comp (sys.baseToMid j) (sys.midToTot j)
          (IsLocalRing.maximalIdeal (sys.Base j)))).Flat :=
  exists_flat_index_of_isNoetherianFlatDescentSystem
    sys.isNoetherianFlatDescentSystem_fibre hfib i

/-- **THE LOCALIZATION SEAM, PASSED TO THE COLIMIT** (cut 2026-07-28 out of
`nonempty_flatNoetherianStage_of_essFinitePresentation`; **PROVEN the same day**.
Read the section note "THE CUT OF THE APPROXIMATION LEAF" above first).

*At every stage `i` of a `NoetherianApproxSystem`, `A` is a localization of
`B ⊗_{S_i} S'_i`.*

This is the field `FlatNoetherianStage.isLocalizationTensor` and nothing else, so
its docstring — including the CORRECTION that replaced `Algebra.IsPushout` by
`IsLocalization` on 2026-07-27, and the checked degeneracy argument for why plain
`Module.Flat` there would be too weak — is the specification for this leaf.

**THE PROOF, and it needs NO colimit machinery at all.**  The submonoid is not
constructed as a union of the stage submonoids; it is simply

  `W = {w ∈ B ⊗_{S_i} S'_i | the image of w in A is a unit}`,

for which `IsLocalization.map_units` is true by definition.  The other two
clauses of `isLocalization_iff` are then each discharged at a SINGLE stage:

* *`surj`.*  Given `a : A`, `tot_surj` puts `a = totToA j₀ t₀`; `directed`
  raises `j₀` to some `k ≥ i` and `comm_totToA` carries `t₀` along, so
  `a = totToA k t` with `t : S'_k`.  Now `isLocalizationTotT` at `i ≤ k` says
  `S'_k` is a localization of `S_k ⊗_{S_i} S'_i`, so `t = x/w` there, and
  applying `totToA k` to that equation gives `a = φ_k x / φ_k w` after the
  comparison `key` below.  `φ_k w` lies in `W` because a ring map sends units to
  units.
* *`exists_of_eq`.*  Given `f x = f y`, write `x - y` as an explicit finite sum
  `∑ midToB j (m_l) ⊗ₜ t_l` — this is `hsum`, an induction on the tensor product
  using `mid_surj` and `directed`, and it is the ONLY place where "every element
  comes from some stage" is used.  Its stage-`j` lift `d_j = ∑ m_l ⊗ₜ t_l` has
  `totToA j (ψ_j d_j) = f (x - y) = 0`, so `tot_sep` gives `k ≥ j` with
  `totT (ψ_j d_j) = 0`; the stage-`k` lift `d_k = ∑ midT (m_l) ⊗ₜ t_l` then has
  `ψ_k d_k = 0` (by `comm_midT` and `totT_comp`, termwise), and
  `IsLocalization.exists_of_eq` at `k` produces `c` with `c · d_k = 0`.  Pushing
  down, `φ_k c ∈ W` kills `x - y`.

The one recurring ingredient is the comparison `key`: the two ring maps
`S_k ⊗_{S_i} S'_i → A` — one through `B ⊗_{S_i} S'_i`, one through `S'_k` —
agree.  Both are determined by their values on pure tensors, where the identity
is `comm_midTot` together with `comm_totToA`; the proof is a three-case
`TensorProduct.induction_on`.

So the "filtered colimit of localizations is a localization" sentence of the
older design note is TRUE but was never needed: only `mid_surj`, `tot_surj`,
`tot_sep`, `directed`, the three `comm_*` naturality fields, `totT_comp` and
`isLocalizationTotT` are consumed, and the colimit itself never has to be built.

**FAITHFULNESS.**  Stated at EVERY `i`, which is what the source's property list
gives (it holds for every `λ`, not for large `λ`), and what the assembly needs:
the index at which the two flatness leaves land is chosen by them, not by this
one. -/
theorem exists_isLocalization_tensor_of_noetherianApproxSystem
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    {g : R →+* B} {v : B →+* A} (sys : NoetherianApproxSystem g v) (i : sys.Λ) :
    letI : Algebra (sys.Mid i) (sys.Tot i) := (sys.midToTot i).toAlgebra
    letI : Algebra (sys.Mid i) B := (sys.midToB i).toAlgebra
    letI : Algebra (sys.Tot i) A := (sys.totToA i).toAlgebra
    letI : Algebra B A := v.toAlgebra
    letI : Algebra (sys.Mid i) A := (v.comp (sys.midToB i)).toAlgebra
    haveI : IsScalarTower (sys.Mid i) B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (sys.Mid i) (sys.Tot i) A :=
      IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun (sys.comm_midTot i) x).symm
    letI : Algebra (B ⊗[sys.Mid i] sys.Tot i) A :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (sys.Mid i) B A)
        (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) A)
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    ∃ W : Submonoid (B ⊗[sys.Mid i] sys.Tot i), IsLocalization W A := by
  letI : Algebra (sys.Mid i) (sys.Tot i) := (sys.midToTot i).toAlgebra
  letI : Algebra (sys.Mid i) B := (sys.midToB i).toAlgebra
  letI : Algebra (sys.Tot i) A := (sys.totToA i).toAlgebra
  letI : Algebra B A := v.toAlgebra
  letI : Algebra (sys.Mid i) A := (v.comp (sys.midToB i)).toAlgebra
  haveI : IsScalarTower (sys.Mid i) B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (sys.Mid i) (sys.Tot i) A :=
    IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun (sys.comm_midTot i) x).symm
  letI : Algebra (B ⊗[sys.Mid i] sys.Tot i) A :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (sys.Mid i) B A)
      (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) A)
      fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  show ∃ W : Submonoid (B ⊗[sys.Mid i] sys.Tot i), IsLocalization W A
  -- Pointwise forms of the system's naturality/cocone fields.
  have hMB : ∀ {a b : sys.Λ} (hh : sys.le a b) (m : sys.Mid a),
      sys.midToB b (sys.midT hh m) = sys.midToB a m :=
    fun hh m => DFunLike.congr_fun (sys.comm_midToB hh) m
  have hTA : ∀ {a b : sys.Λ} (hh : sys.le a b) (t : sys.Tot a),
      sys.totToA b (sys.totT hh t) = sys.totToA a t :=
    fun hh t => DFunLike.congr_fun (sys.comm_totToA hh) t
  have hMT : ∀ (a : sys.Λ) (m : sys.Mid a),
      sys.totToA a (sys.midToTot a m) = v (sys.midToB a m) :=
    fun a m => DFunLike.congr_fun (sys.comm_midTot a) m
  have hMTT : ∀ {a b : sys.Λ} (hh : sys.le a b) (m : sys.Mid a),
      sys.midToTot b (sys.midT hh m) = sys.totT hh (sys.midToTot a m) :=
    fun hh m => DFunLike.congr_fun (sys.comm_midT hh) m
  have hTT : ∀ {a b c : sys.Λ} (h₁ : sys.le a b) (h₂ : sys.le b c) (t : sys.Tot a),
      sys.totT h₂ (sys.totT h₁ t) = sys.totT (sys.le_trans' h₁ h₂) t :=
    fun h₁ h₂ t => DFunLike.congr_fun (sys.totT_comp h₁ h₂) t
  -- The structure map `B ⊗_{S_i} S'_i → A` on pure tensors.
  have hf : ∀ (b : B) (t : sys.Tot i),
      algebraMap (B ⊗[sys.Mid i] sys.Tot i) A (b ⊗ₜ[sys.Mid i] t) = v b * sys.totToA i t :=
    fun _ _ => rfl
  -- Every element of `B ⊗_{S_i} S'_i` is an explicit finite sum coming from one stage.
  have hsum : ∀ d : B ⊗[sys.Mid i] sys.Tot i, ∃ (j : sys.Λ) (_ : sys.le i j)
      (L : List (sys.Mid j × sys.Tot i)),
      d = (L.map (fun p => (sys.midToB j p.1) ⊗ₜ[sys.Mid i] p.2)).sum := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨i, sys.le_rfl i, [], by simp⟩
    | tmul b t =>
        obtain ⟨j₀, m, hm⟩ := sys.mid_surj b
        obtain ⟨k, hik, hj₀k⟩ := sys.directed i j₀
        refine ⟨k, hik, [(sys.midT hj₀k m, t)], ?_⟩
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [hMB hj₀k m, hm]
    | add d₁ d₂ h₁ h₂ =>
        obtain ⟨j₁, hij₁, L₁, hL₁⟩ := h₁
        obtain ⟨j₂, hij₂, L₂, hL₂⟩ := h₂
        obtain ⟨k, ha, hb⟩ := sys.directed j₁ j₂
        refine ⟨k, sys.le_trans' hij₁ ha,
          (L₁.map (fun p => (sys.midT ha p.1, p.2))) ++
            (L₂.map (fun p => (sys.midT hb p.1, p.2))), ?_⟩
        rw [hL₁, hL₂, List.map_append, List.sum_append]
        simp only [List.map_map, Function.comp_def, hMB]
  -- The submonoid is the full preimage of the units of `A`.
  refine ⟨{ carrier := {w | IsUnit (algebraMap (B ⊗[sys.Mid i] sys.Tot i) A w)}
            one_mem' := by simp
            mul_mem' := by
              intro a b ha hb
              simp only [Set.mem_setOf_eq, map_mul] at *
              exact ha.mul hb }, ?_⟩
  refine (isLocalization_iff _ A).mpr ⟨fun y => y.2, ?_, ?_⟩
  · -- SURJECTIVITY: every `a : A` is a fraction over the stage tensor.
    intro a
    obtain ⟨j₀, t₀, ht₀⟩ := sys.tot_surj a
    obtain ⟨k, hik, hj₀k⟩ := sys.directed i j₀
    letI : Algebra (sys.Mid i) (sys.Mid k) := (sys.midT hik).toAlgebra
    letI : Algebra (sys.Mid k) (sys.Tot k) := (sys.midToTot k).toAlgebra
    letI : Algebra (sys.Mid i) (sys.Tot k) := ((sys.midToTot k).comp (sys.midT hik)).toAlgebra
    letI : Algebra (sys.Tot i) (sys.Tot k) := (sys.totT hik).toAlgebra
    haveI : IsScalarTower (sys.Mid i) (sys.Mid k) (sys.Tot k) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (sys.Mid i) (sys.Tot i) (sys.Tot k) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.comm_midT hik) x
    letI : Algebra (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (sys.Mid i) (sys.Mid k) (sys.Tot k))
        (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) (sys.Tot k))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    obtain ⟨Wk, hWk⟩ := sys.isLocalizationTotT hik
    haveI := hWk
    let φk : (sys.Mid k ⊗[sys.Mid i] sys.Tot i) →ₐ[sys.Mid i] (B ⊗[sys.Mid i] sys.Tot i) :=
      Algebra.TensorProduct.map
        ({ toRingHom := sys.midToB k, commutes' := fun x => hMB hik x } :
          sys.Mid k →ₐ[sys.Mid i] B)
        (AlgHom.id (sys.Mid i) (sys.Tot i))
    have hφk : ∀ (m : sys.Mid k) (t : sys.Tot i),
        φk (m ⊗ₜ[sys.Mid i] t) = (sys.midToB k m) ⊗ₜ[sys.Mid i] t := fun _ _ => rfl
    have hψk : ∀ (m : sys.Mid k) (t : sys.Tot i),
        algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) (m ⊗ₜ[sys.Mid i] t)
          = sys.midToTot k m * sys.totT hik t := fun _ _ => rfl
    have key : ∀ z : sys.Mid k ⊗[sys.Mid i] sys.Tot i,
        algebraMap (B ⊗[sys.Mid i] sys.Tot i) A (φk z)
          = sys.totToA k (algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m t => rw [hφk, hψk, hf, map_mul, hMT k m, hTA hik t]
      | add z₁ z₂ e₁ e₂ => simp only [map_add, e₁, e₂]
    have ha : sys.totToA k (sys.totT hj₀k t₀) = a := by rw [hTA hj₀k t₀, ht₀]
    obtain ⟨⟨xk, wk⟩, hxw⟩ := IsLocalization.surj (M := Wk) (sys.totT hj₀k t₀)
    refine ⟨⟨φk xk, ⟨φk (wk : sys.Mid k ⊗[sys.Mid i] sys.Tot i), ?_⟩⟩, ?_⟩
    · show IsUnit (algebraMap (B ⊗[sys.Mid i] sys.Tot i) A
        (φk (wk : sys.Mid k ⊗[sys.Mid i] sys.Tot i)))
      rw [key]
      exact (IsLocalization.map_units (sys.Tot k) wk).map (sys.totToA k)
    · show a * algebraMap (B ⊗[sys.Mid i] sys.Tot i) A
          (φk (wk : sys.Mid k ⊗[sys.Mid i] sys.Tot i))
        = algebraMap (B ⊗[sys.Mid i] sys.Tot i) A (φk xk)
      rw [key, key, ← ha, ← map_mul, hxw]
  · -- SEPARATEDNESS: two elements with the same image are identified by a unit of `W`.
    intro x y hxy
    obtain ⟨j, hij, L, hL⟩ := hsum (x - y)
    letI : Algebra (sys.Mid i) (sys.Mid j) := (sys.midT hij).toAlgebra
    letI : Algebra (sys.Mid j) (sys.Tot j) := (sys.midToTot j).toAlgebra
    letI : Algebra (sys.Mid i) (sys.Tot j) := ((sys.midToTot j).comp (sys.midT hij)).toAlgebra
    letI : Algebra (sys.Tot i) (sys.Tot j) := (sys.totT hij).toAlgebra
    haveI : IsScalarTower (sys.Mid i) (sys.Mid j) (sys.Tot j) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (sys.Mid i) (sys.Tot i) (sys.Tot j) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.comm_midT hij) x
    letI : Algebra (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (sys.Mid i) (sys.Mid j) (sys.Tot j))
        (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) (sys.Tot j))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    let φj : (sys.Mid j ⊗[sys.Mid i] sys.Tot i) →ₐ[sys.Mid i] (B ⊗[sys.Mid i] sys.Tot i) :=
      Algebra.TensorProduct.map
        ({ toRingHom := sys.midToB j, commutes' := fun x => hMB hij x } :
          sys.Mid j →ₐ[sys.Mid i] B)
        (AlgHom.id (sys.Mid i) (sys.Tot i))
    have hφj : ∀ (m : sys.Mid j) (t : sys.Tot i),
        φj (m ⊗ₜ[sys.Mid i] t) = (sys.midToB j m) ⊗ₜ[sys.Mid i] t := fun _ _ => rfl
    have hψj : ∀ (m : sys.Mid j) (t : sys.Tot i),
        algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j) (m ⊗ₜ[sys.Mid i] t)
          = sys.midToTot j m * sys.totT hij t := fun _ _ => rfl
    have keyj : ∀ z : sys.Mid j ⊗[sys.Mid i] sys.Tot i,
        algebraMap (B ⊗[sys.Mid i] sys.Tot i) A (φj z)
          = sys.totToA j (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m t => rw [hφj, hψj, hf, map_mul, hMT j m, hTA hij t]
      | add z₁ z₂ e₁ e₂ => simp only [map_add, e₁, e₂]
    -- The stage-`j` lift of `x - y`, and its vanishing in `A`.
    have hdj : φj ((L.map (fun p => p.1 ⊗ₜ[sys.Mid i] p.2)).sum) = x - y := by
      rw [hL, map_list_sum, List.map_map]
      simp only [Function.comp_def, hφj]
    have hzero : sys.totToA j
        (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)
          ((L.map (fun p => p.1 ⊗ₜ[sys.Mid i] p.2)).sum)) = 0 := by
      rw [← keyj, hdj, map_sub, hxy, sub_self]
    obtain ⟨k, hjk, hsep⟩ := sys.tot_sep j
      (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)
        ((L.map (fun p => p.1 ⊗ₜ[sys.Mid i] p.2)).sum)) 0 (by rw [hzero, map_zero])
    have hik : sys.le i k := sys.le_trans' hij hjk
    letI : Algebra (sys.Mid i) (sys.Mid k) := (sys.midT hik).toAlgebra
    letI : Algebra (sys.Mid k) (sys.Tot k) := (sys.midToTot k).toAlgebra
    letI : Algebra (sys.Mid i) (sys.Tot k) := ((sys.midToTot k).comp (sys.midT hik)).toAlgebra
    letI : Algebra (sys.Tot i) (sys.Tot k) := (sys.totT hik).toAlgebra
    haveI : IsScalarTower (sys.Mid i) (sys.Mid k) (sys.Tot k) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower (sys.Mid i) (sys.Tot i) (sys.Tot k) :=
      IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun (sys.comm_midT hik) x
    letI : Algebra (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (sys.Mid i) (sys.Mid k) (sys.Tot k))
        (IsScalarTower.toAlgHom (sys.Mid i) (sys.Tot i) (sys.Tot k))
        fun _ _ => Commute.all _ _).toRingHom.toAlgebra
    obtain ⟨Wk, hWk⟩ := sys.isLocalizationTotT hik
    haveI := hWk
    let φk : (sys.Mid k ⊗[sys.Mid i] sys.Tot i) →ₐ[sys.Mid i] (B ⊗[sys.Mid i] sys.Tot i) :=
      Algebra.TensorProduct.map
        ({ toRingHom := sys.midToB k, commutes' := fun x => hMB hik x } :
          sys.Mid k →ₐ[sys.Mid i] B)
        (AlgHom.id (sys.Mid i) (sys.Tot i))
    have hφk : ∀ (m : sys.Mid k) (t : sys.Tot i),
        φk (m ⊗ₜ[sys.Mid i] t) = (sys.midToB k m) ⊗ₜ[sys.Mid i] t := fun _ _ => rfl
    have hψk : ∀ (m : sys.Mid k) (t : sys.Tot i),
        algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) (m ⊗ₜ[sys.Mid i] t)
          = sys.midToTot k m * sys.totT hik t := fun _ _ => rfl
    have keyk : ∀ z : sys.Mid k ⊗[sys.Mid i] sys.Tot i,
        algebraMap (B ⊗[sys.Mid i] sys.Tot i) A (φk z)
          = sys.totToA k (algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m t => rw [hφk, hψk, hf, map_mul, hMT k m, hTA hik t]
      | add z₁ z₂ e₁ e₂ => simp only [map_add, e₁, e₂]
    -- The stage-`k` lift of `x - y`, which is already killed at stage `k`.
    have hdk : φk ((L.map (fun p => (sys.midT hjk p.1) ⊗ₜ[sys.Mid i] p.2)).sum) = x - y := by
      rw [hL, map_list_sum, List.map_map]
      simp only [Function.comp_def, hφk, hMB]
    have hψeq : algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k)
          ((L.map (fun p => (sys.midT hjk p.1) ⊗ₜ[sys.Mid i] p.2)).sum)
        = sys.totT hjk (algebraMap (sys.Mid j ⊗[sys.Mid i] sys.Tot i) (sys.Tot j)
            ((L.map (fun p => p.1 ⊗ₜ[sys.Mid i] p.2)).sum)) := by
      rw [map_list_sum, map_list_sum, map_list_sum, List.map_map, List.map_map, List.map_map]
      simp only [Function.comp_def, hψk, hψj, map_mul, hMTT, hTT]
    have hzk : algebraMap (sys.Mid k ⊗[sys.Mid i] sys.Tot i) (sys.Tot k)
        ((L.map (fun p => (sys.midT hjk p.1) ⊗ₜ[sys.Mid i] p.2)).sum) = 0 := by
      rw [hψeq, hsep, map_zero]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Wk) (S := sys.Tot k)
      (x := (L.map (fun p => (sys.midT hjk p.1) ⊗ₜ[sys.Mid i] p.2)).sum) (y := 0)
      (by rw [hzk, map_zero])
    refine ⟨⟨φk (c : sys.Mid k ⊗[sys.Mid i] sys.Tot i), ?_⟩, ?_⟩
    · show IsUnit (algebraMap (B ⊗[sys.Mid i] sys.Tot i) A
        (φk (c : sys.Mid k ⊗[sys.Mid i] sys.Tot i)))
      rw [keyk]
      exact (IsLocalization.map_units (sys.Tot k) c).map (sys.totToA k)
    · have hkill : φk (c : sys.Mid k ⊗[sys.Mid i] sys.Tot i) * (x - y) = 0 := by
        rw [← hdk, ← map_mul, hc, mul_zero, map_zero]
      have h2 : φk (c : sys.Mid k ⊗[sys.Mid i] sys.Tot i) * x
          - φk (c : sys.Mid k ⊗[sys.Mid i] sys.Tot i) * y = 0 := by
        rw [← mul_sub]; exact hkill
      exact sub_eq_zero.mp h2

/-- **NOETHERIAN APPROXIMATION FOR 00R7: Stacks 10.127.13 + 10.128.3**
(cut 2026-07-27 out of the approximation half below; **PROVEN 2026-07-28** over
the four declarations above.  Read the section note "THE CUT OF THE APPROXIMATION
LEAF" for the design decision that produced it, and the docstring of
`FlatNoetherianStage` for what the datum is and why it is as weak as it is).

*Under 00R7's hypotheses at `M = S' = A`, a `FlatNoetherianStage v` exists.*

**THIS IS 00R7'S PROOF MINUS ITS LAST SENTENCE**, and as of 2026-07-28 the four
steps of that proof are four declarations rather than one sorry:

1. writing `R = colim R_λ` as a directed colimit of local `ℤ`-algebras
   essentially of finite type (10.127.11, so each `R_λ` is Noetherian) and
   descending `S` to `S_λ = (R_λ[x₁,…,x_n]/(f_{1,λ},…,f_{u,λ}))_{𝔮_λ}` and `S'`
   to `S'_λ = (S_λ[y₁,…,y_m]/(ḡ_{1,λ},…,ḡ_{v,λ}))_{𝔮̄'_λ}` — which is where
   `_hfpA` and `_hfpB` are both consumed, and which is why 00R7 needs essential
   finite PRESENTATION on both maps — is
   `nonempty_noetherianApproxSystem_of_essFinitePresentation`;
2. applying **10.128.3** once, to get `M_λ` flat over `R_λ` for large `λ`, is
   `exists_flatBase_index_of_noetherianApproxSystem`;
3. checking that `(S_λ/𝔭_λ S_λ → S'_λ/𝔭_λ S'_λ, M_λ/𝔭_λ M_λ)` is again a system
   as in 10.127.13 and applying **10.128.3** a second time is
   `exists_flatFibre_index_of_noetherianApproxSystem`;
4. the localization seam `S'_λ ⊗_{S_λ} S → S'`, which is 00R7's own property
   list passed to the colimit, is
   `exists_isLocalization_tensor_of_noetherianApproxSystem`.

At `M = S' = A` the presentation of `M` over `S'` may be taken to be
`(S')^{⊕0} → (S')^{⊕1} → M → 0`, so `M_λ = S'_λ` and no separate module has to
be carried — which is the whole reason `FlatNoetherianStage` has three
carriers and not four, and why `NoetherianApproxSystem` has three towers.

**WHAT IS LEFT HERE is glue plus one proven lemma.**  Steps 2 and 3 land at
DIFFERENT indices — each is cofinal, `∀ i, ∃ j ≥ i`, because that is what
10.128.3's proof delivers — so the assembly starts step 3 at the index step 2
returned and then carries step 2's conclusion up to it with
`NoetherianApproxSystem.flat_base_of_le`, which is proven above.  That transport
is the only mathematics in this body; everything else is `obtain` and a structure
instance.

**FAITHFULNESS, restated 2026-07-27 after the `isPushout` repair.**  The
hypotheses are 00R7's verbatim at `M = S' = A`, and the conclusion is now
genuinely weaker than what 10.127.13 + 10.128.3 produce (see the "WHY IT IS
SAFE" paragraph of `FlatNoetherianStage`, and the CORRECTION block in the
section note above for the field that had to be weakened to make that sentence
true).  It is therefore true if 00R7 is.

**It is still not vacuous**, and the check has been redone against the new
field.  `isLocalizationTensor` pins `A` to be a localization of
`B ⊗[Mid] Tot`, so:

* the junk stage `Base = Mid = Tot = ℤ_(p)` (or `ℚ`, whichever maps to `B`)
  collapses `B ⊗[Mid] Tot` to `B` and demands that `A` be a localization of
  `B`, which is false in general — e.g. `B = R = k`, `A = k[t]_(t)`;
* the junk stage `Base = Mid = Tot = A` fails `isNoetherianTot` unless `A`
  happens to be Noetherian, exactly as before.

The corresponding degeneracy check for the WEAKER field "`A` is flat over
`B ⊗[Mid] Tot`" FAILS — the first junk stage above satisfies it iff `A` is
flat over `B`, which is 00R7's conclusion — which is why the field is
`IsLocalization` and not `Module.Flat`.

**WHERE THE SURVEY WENT.**  The three greppable findings the previous owner left
here (mathlib's `Presentation.ModelOfHasCoeffs` machinery; the subring
realisation of the `R_λ` tower; `Λ = Finset R` and why no `Ring.DirectLimit` is
needed) are all about CONSTRUCTING the system, so they now live in the docstring
of `nonempty_noetherianApproxSystem_of_essFinitePresentation`, which is the leaf
that has to do it.  Finding 2 ended "this is the one piece that can be landed as
a proven lemma; it was not landed here only because, with no assembly written, it
would be free-floating" — that obstruction is gone: the assembly below is
written, so a `Base`-tower lemma proven inside that leaf now has a consumer.
**It was landed on 2026-07-28**, as `nonempty_noetherianLocalBaseSystem`, and
`nonempty_noetherianApproxSystem_of_essFinitePresentation` is now PROVEN over it
and the single remaining leaf
`nonempty_noetherianApproxSystem_of_baseSystem`. -/
theorem nonempty_flatNoetherianStage_of_essFinitePresentation
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    Nonempty (FlatNoetherianStage v) := by
  obtain ⟨sys⟩ := nonempty_noetherianApproxSystem_of_essFinitePresentation hfpA hfpB
  obtain ⟨i₀⟩ := sys.nonemptyΛ
  obtain ⟨j₁, _, hb₁⟩ := exists_flatBase_index_of_noetherianApproxSystem sys hflat i₀
  obtain ⟨j₂, h₂, hf₂⟩ := exists_flatFibre_index_of_noetherianApproxSystem sys hfib j₁
  exact ⟨{ Base := sys.Base j₂
           Mid := sys.Mid j₂
           Tot := sys.Tot j₂
           isLocalRingBase := sys.isLocalRingBase j₂
           isLocalRingMid := sys.isLocalRingMid j₂
           isLocalRingTot := sys.isLocalRingTot j₂
           isNoetherianBase := sys.isNoetherianBase j₂
           isNoetherianMid := sys.isNoetherianMid j₂
           isNoetherianTot := sys.isNoetherianTot j₂
           baseToMid := sys.baseToMid j₂
           midToTot := sys.midToTot j₂
           isLocalHomBaseToMid := sys.isLocalHomBaseToMid j₂
           isLocalHomMidToTot := sys.isLocalHomMidToTot j₂
           midToB := sys.midToB j₂
           totToA := sys.totToA j₂
           comm := sys.comm_midTot j₂
           flatBase := sys.flat_base_of_le h₂ hb₁
           flatFibre := hf₂
           isLocalizationTensor :=
             exists_isLocalization_tensor_of_noetherianApproxSystem sys j₂ }⟩

/-- **THE APPROXIMATION HALF OF 00R7** (cut 2026-07-27; **PROVEN the same day**
over `nonempty_flatNoetherianStage_of_essFinitePresentation`.  The section notes
"00R7 CUT" and "THE COLIMIT-API DECISION" above are the two design decisions
that produced it and should be read first).

*Assume Stacks 00MP — the statement of
`flat_of_flat_of_flat_quotientMap_noetherian` above, quantified over all
Noetherian local `R`, `B`, `A`.  Then Stacks 00R7 holds: for local
homomorphisms `R → B → A` of ARBITRARY local rings with both `R → A` and
`R → B` essentially of finite presentation, `A` flat over `R` and `A/𝔪_R A`
flat over `B/𝔪_R B` imply `A` flat over `B`.*

**WHY 00MP IS A HYPOTHESIS AND NOT AN IMPORT.**  Because that is what makes
the assembly writable without first inventing a filtered system, and because
it is what keeps 00MP from free-floating.  The alternative — state the
filtered system, then state 00MP, then assemble — was examined and rejected in
the section note above, where the cheap version of the system is REFUTED (the
subring realisation is false for `B` and `A`, whose approximating system has
non-injective transition maps).

**WHAT THE PROOF IS, now that it is written.**  The hypothesis is not a
shortcut: 00R7's proof is the approximation argument and nothing else.  All of
that argument now sits in the single leaf
`nonempty_flatNoetherianStage_of_essFinitePresentation`, which produces a
`FlatNoetherianStage v` — one Noetherian local stage `R_λ → S_λ → S'_λ` at
which 00MP's two hypotheses already hold, together with a witness that `M` is
a LOCALIZATION of `M_λ ⊗_{S_λ} S`.  What is left here is 00R7's LAST SENTENCE,
and it is exactly three steps:

1. `hNoeth` at the stage, giving `S'_λ` flat over `S_λ`;
2. `Module.Flat.baseChange`, giving `S ⊗_{S_λ} S'_λ` flat over `S`;
3. `IsLocalization.flat` and `Module.Flat.trans`, giving `A` flat over `B`.

**Step 2 used to be a single `RingHom.Flat.isStableUnderBaseChange` along an
`Algebra.IsPushout` field.  That field was too strong** — 00R7's proof lists
`S'_λ ⊗_{S_λ} S_μ → S'_μ` as a *localization*, not an isomorphism — and was
weakened on 2026-07-27; the argument is the CORRECTION block in the section
note "THE COLIMIT-API DECISION" above.  The extra step is the price, and it is
one line.

The `M = S' = A` instantiation is stable under all of this: `M_λ = S'_λ` is
finite over `S'_λ` and nonzero because `S'_λ` is local, so no extra hypothesis
of 00MP has to be re-established at the finite stage.

**WHAT WAS PINNED**, for the next owner of the finite-generation half
(`fg_ker_of_flat_quotientMap` below), who needs the same machinery for 046Y:
**no filtered colimit appears in any statement.**  The full argument, with the
three reasons and the checked consequences for 046Y, is the section note "THE
COLIMIT-API DECISION" above.

**FAITHFULNESS.**  The hypotheses are 00R7's, verbatim, at `M = S' = A`; see
the 00R7 docstring below, which is unchanged in content.  Adding a hypothesis
can only weaken a statement, so this leaf cannot be false unless 00R7 is. -/
theorem flat_of_flat_of_flat_quotientMap_of_essFinitePresentation_of_noetherian
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    (hNoeth : ∀ {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
      [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
      [IsNoetherianRing R] [IsNoetherianRing B] [IsNoetherianRing A]
      {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v],
      (v.comp g).Flat →
      (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat →
      v.Flat)
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    v.Flat := by
  obtain ⟨st⟩ := nonempty_flatNoetherianStage_of_essFinitePresentation hfpA hfpB hflat hfib
  letI := st.commRingBase
  letI := st.commRingMid
  letI := st.commRingTot
  letI := st.isLocalRingBase
  letI := st.isLocalRingMid
  letI := st.isLocalRingTot
  letI := st.isNoetherianBase
  letI := st.isNoetherianMid
  letI := st.isNoetherianTot
  letI := st.isLocalHomBaseToMid
  letI := st.isLocalHomMidToTot
  -- Step 1: 00MP at the Noetherian stage.
  have hstage : st.midToTot.Flat := hNoeth st.flatBase st.flatFibre
  -- Step 2: `M = M_λ ⊗_{S_λ} S`, so flatness base-changes up to `B → A`.
  letI : Algebra st.Mid st.Tot := st.midToTot.toAlgebra
  letI : Algebra st.Mid B := st.midToB.toAlgebra
  letI : Algebra st.Tot A := st.totToA.toAlgebra
  letI : Algebra B A := v.toAlgebra
  letI : Algebra st.Mid A := (v.comp st.midToB).toAlgebra
  haveI : IsScalarTower st.Mid B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower st.Mid st.Tot A :=
    IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun st.comm x).symm
  letI : Algebra (B ⊗[st.Mid] st.Tot) A :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom st.Mid B A)
      (IsScalarTower.toAlgHom st.Mid st.Tot A) fun _ _ => Commute.all _ _).toRingHom.toAlgebra
  obtain ⟨W, hW⟩ := st.isLocalizationTensor
  -- `Tot` is flat over `Mid`, so `B ⊗[Mid] Tot` is flat over `B`.
  haveI : Module.Flat st.Mid st.Tot := hstage
  haveI : Module.Flat B (B ⊗[st.Mid] st.Tot) := Module.Flat.baseChange _ _ _
  -- The two structure maps `B → B ⊗[Mid] Tot → A` compose to `v`.
  haveI : IsScalarTower B (B ⊗[st.Mid] st.Tot) A :=
    IsScalarTower.of_algebraMap_eq fun b => by
      show v b = _
      simp [RingHom.algebraMap_toAlgebra]
  -- Step 3: `A` is a localization of `B ⊗[Mid] Tot`, hence flat over it.
  haveI : Module.Flat (B ⊗[st.Mid] st.Tot) A := IsLocalization.flat A W
  have hflatBA : Module.Flat B A := Module.Flat.trans B (B ⊗[st.Mid] st.Tot) A
  exact hflatBA

end FibreCriterionRingLevel

/-- **THE ENGINE: Stacks 00R7** = Algebra Lemma 10.128.8, at `M = S' = A`
(cut out of `flat_of_flat_of_flat_quotientMap` on 2026-07-27 along the
source's own seam, and itself **PROVEN** the same day over the two leaves
above — see the section note "00R7 CUT" for the design decision).

*Let `R → B → A` be local homomorphisms of local rings with **both** `R → A`
and `R → B` essentially of finite **presentation**.  If `A` is flat over `R`
and `A/𝔪_R A` is flat over `B/𝔪_R B`, then `A` is flat over `B`.*

This is the SAME statement as `flat_of_flat_of_flat_quotientMap` below except
that `R → B` is assumed essentially of finite PRESENTATION rather than merely
of finite TYPE.  That single strengthening is the whole difference between
05UV and 00R7, and it is what makes this the reusable half: 05UV's proof
invokes 00R7 twice, and the corrected route audit in the section note above
records that "00R7 is the engine, not a wrong turn".

**FAITHFULNESS.**  00R7's hypotheses are (1) `R → S` and `R → S'` essentially
of finite presentation, (2) `M` of finite presentation over `S'`, (3) `M ≠ 0`,
(4) `M/𝔪M` flat over `S/𝔪S`, (5) `M` flat over `R`.  At `M = S' = A`, (2) and
(3) are theorems rather than assumptions — `A` is finitely presented over
itself, and `[IsLocalRing A]` already supplies `Nontrivial A` — so they are
omitted exactly as in the leaf below.  00R7's conclusion also asserts `S` flat
over `R`; only `M` flat over `S` is kept, because only that is consumed.
Fewer hypotheses and a weaker conclusion cannot turn a true statement false.

**WHAT PROVING IT COSTS, read off the Stacks proof.**  `00R7 = Noetherian
approximation (10.127.13 / 10.128.3) + 00MP (10.99.15)`.  So the non-Noetherian
content is ENTIRELY in the approximation, and the local criterion of flatness
is only ever needed in the Noetherian setting — which is why the "ideally
separated" hazard (Matsumura 22.3) flagged in the section note is real for a
DIRECT attack and absent from this route.  Concretely a prover needs:

* **00MP** — self-contained and Noetherian: `R`, `S`, `S'` Noetherian local,
  `M` finite over `S'`, `M ≠ 0`, `M/𝔪M` flat over `S/𝔪S`, `M` flat over `R`
  ⟹ `S` flat over `R` and `M` flat over `S`.  Its own proof cites only
  Nakayama and the local-criterion family (10.99.7 / 10.99.10 / 10.39.15).
  The audit's judgement that this is "writable today over `IsNoetherianRing`
  and `IsLocalRing` with no new definitions" stands.
* **The approximation half** — writing an essentially-of-finite-type local
  ring map as a filtered colimit of such maps of NOETHERIAN local rings, plus
  descent of flatness along that colimit.

**BOTH OF THOSE ARE NOW CUT OUT, 2026-07-27, and this paragraph replaces the
pin that used to stand here.**  The old text read:

> **THE APPROXIMATION HALF IS DELIBERATELY NOT CUT HERE, and this is the pin.**
> Stating a filtered system of rings is a design decision, and a wrong one
> manufactures a false or useless sub-leaf; so 00R7 is left ATOMIC rather than
> split into `00MP + approximation`, because the assembly of those two is
> exactly the piece that cannot be written without first making that decision.
> Stating 00MP alone would leave it FREE-FLOATING — no consumer could be
> written — which this development forbids.  Whoever takes the design decision
> should cut here first, and say what they pinned.

The decision was taken, and what was pinned is written out in the section note
"00R7 CUT" above: **the filtered system is NOT stated; 00MP is passed to the
approximation leaf as a hypothesis**, which makes the assembly a one-liner,
needs no new definitions, and leaves 00MP with a written consumer.  The note
also REFUTES the cheap subring realisation of the system, so nobody has to
rediscover that it is false.

**UPDATE, later the same day: both halves moved, on two branches at once.**  The
approximation half is PROVEN — its owner took the second design decision, how if
at all to state a filtered colimit, and the answer is **not to**; see the section
note "THE COLIMIT-API DECISION" above.  The local criterion 10.99.10 is PROVEN
too, down to one homological leaf; see the section note "10.99.10 CUT".  That
leaf, `lTensor_subtype_injective_of_pow_le`, is itself **PROVEN 2026-07-27** over
the general local criterion in
`Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`, so the residue of 00R7
is now the SINGLE open leaf
`nonempty_flatNoetherianStage_of_essFinitePresentation` (Stacks 10.127.13 +
10.128.3, i.e. 00R7's proof minus its last sentence).
(This paragraph was rewritten at integration from the merged source: each branch
named the other's leaf as still open under its own predecessor's name.) -/
theorem flat_of_flat_of_flat_quotientMap_of_essFinitePresentation {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    v.Flat :=
  -- Stacks 00R7 = Noetherian approximation + 00MP: feed the Noetherian engine
  -- to the approximation half.
  flat_of_flat_of_flat_quotientMap_of_essFinitePresentation_of_noetherian
    flat_of_flat_of_flat_quotientMap_noetherian hfpA hfpB hflat hfib

/-! ### The PRESENTATION half of 05UV's finite-generation argument — PROVEN

**This block discharges the "state it together with the presentation"
instruction that the leaf below used to carry** (2026-07-27).

05UV's proof of its first conclusion opens by writing down a presentation:
`S = C_q̄` with `C = R[x₁,…,xₙ]/I`, put `B' = R[x₁,…,xₙ]_q` and `J = I·B'`, so
that `S = B'/J` with `B'` essentially of finite PRESENTATION over `R`; the
content is then that `J` is finitely generated.  The previous version of the
leaf's docstring recorded that bookkeeping as unwritten, and inferred from
that that a bare statement of **046Y** would be free-floating.

The bookkeeping is now **written and proven**, and it turned out to need no
missing mathematics whatever — only mathlib's `Algebra.EssFiniteType` API,
`Algebra.FiniteType.iff_quotient_mvPolynomial''`, `Localization.AtPrime` and
`IsLocalization.of_surjective`:

* `exists_essFinitePresentation_surjective_of_essFiniteType` — the
  presentation itself: every local homomorphism essentially of finite TYPE is
  a SURJECTION out of a LOCAL ring essentially of finite PRESENTATION.  That
  ring is `B'`;
* `essFinitePresentation_comp_of_fg_ker` — the converse bookkeeping: if the
  kernel of such a surjection is finitely generated, the composite is
  essentially of finite presentation.  That is "`J` finitely generated ⟹ `S`
  essentially of finite presentation over `R`".

Consequently the leaf that used to stand here is now a THREE-LINE ASSEMBLY,
and all of its remaining mathematical content sits in the single new leaf
`fg_ker_of_flat_quotientMap`.

**046Y IS NOW STATED AND PROVEN** (2026-07-27; this paragraph replaces "046Y is
still not stated, for the unchanged reason: its only consumer would be inside
`fg_ker_of_flat_quotientMap`'s proof, which is still open").  That consumer got
written, so 046Y stopped being free-floating; it is
`eq_of_fg_of_flat_quotient_of_le_sup`, in the section immediately below, and it
costs no Noetherian approximation — see that section's note for why.
-/

/-- **Every essentially-of-finite-type LOCAL homomorphism is a surjection out
of an essentially-of-finite-presentation LOCAL ring** (PROVEN 2026-07-27).
This is step 0 of 05UV's finite-generation argument — the choice of the
presentation `S = B'/J` with `B' = R[x₁,…,xₙ]_q`.

**The construction, which is exactly the source's.**  `Algebra.EssFiniteType`
gives a finite-type subalgebra `T₀ ⊆ B` with `B` a localization of it;
`Algebra.FiniteType.iff_quotient_mvPolynomial''` presents `T₀` as a quotient
of `R[x₁,…,xₙ]`, giving `φ : R[x₁,…,xₙ] →+* B`; and `P` is taken to be
`R[x₁,…,xₙ]` localized at the prime `q = φ⁻¹(𝔪_B)`.

**Why `P` is LOCAL, which is the only step with any content.**  The submonoid
implicit in `EssFiniteType` is the set of elements of `T₀` that become units
in `B`; because `B` is local, that set is SATURATED — it is the complement of
the prime `φ⁻¹(𝔪_B)` — so the localization is a localization at a prime and
`Localization.AtPrime.isLocalRing` applies.  Locality of `P` is what the
consumer needs, since 00R7 is a statement about local rings.

Surjectivity of `w` is `IsLocalization.lift_mk'_spec` applied to a fraction
`t/m` written over `T₀` and then lifted through the polynomial presentation;
both `IsLocalHom` conclusions are free (`IsLocalHom.of_surjective` for `w`,
`isLocalHom_of_comp` for `gP`). -/
theorem exists_essFinitePresentation_surjective_of_essFiniteType {R B : Type u}
    [CommRing R] [CommRing B] [IsLocalRing B]
    {g : R →+* B} [IsLocalHom g] (hft : g.EssFiniteType) :
    ∃ (P : Type u) (_ : CommRing P) (_ : IsLocalRing P) (gP : R →+* P) (w : P →+* B)
      (_ : IsLocalHom gP) (_ : IsLocalHom w),
      Function.Surjective w ∧ EssFinitePresentation gP ∧ w.comp gP = g := by
  letI : Algebra R B := g.toAlgebra
  haveI hft' : Algebra.EssFiniteType R B := hft
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial''
    (R := R) (S := ↥(Algebra.EssFiniteType.subalgebra R B))).mp inferInstance
  set MvP := MvPolynomial (Fin n) R with hMvP
  set φ : MvP →+* B :=
    ((Algebra.EssFiniteType.subalgebra R B).val.comp π).toRingHom with hφ
  set q : Ideal MvP := (IsLocalRing.maximalIdeal B).comap φ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime φ _
  set P := Localization q.primeCompl with hP
  have hunit : ∀ y : q.primeCompl, IsUnit (φ y) := by
    rintro ⟨y, hy⟩
    exact IsLocalRing.notMem_maximalIdeal.mp hy
  set w : P →+* B := IsLocalization.lift hunit with hw
  set gP : R →+* P := (algebraMap MvP P).comp (algebraMap R MvP) with hgP
  have hcomp : w.comp gP = g := by
    ext r
    simp only [hgP, hw, RingHom.comp_apply, IsLocalization.lift_eq, hφ,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  have hsurj : Function.Surjective w := by
    intro b
    obtain ⟨⟨t, m⟩, e⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid R B) b
    obtain ⟨x, hx⟩ := hπ t
    obtain ⟨y, hy⟩ := hπ (m : Algebra.EssFiniteType.subalgebra R B)
    have hφy : φ y = algebraMap (Algebra.EssFiniteType.subalgebra R B) B m := by
      simp [hφ, hy]
    have hmu : IsUnit (algebraMap (Algebra.EssFiniteType.subalgebra R B) B m) := m.2
    have hyq : y ∈ q.primeCompl := by
      simpa [hq, Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal, hφy] using hmu
    refine ⟨IsLocalization.mk' P x ⟨y, hyq⟩, ?_⟩
    rw [hw, IsLocalization.lift_mk'_spec]
    rw [hφy]
    have hφx : φ x = algebraMap (Algebra.EssFiniteType.subalgebra R B) B t := by
      simp [hφ, hx]
    rw [hφx, ← e]
    exact mul_comm _ _
  have hfp : EssFinitePresentation gP := by
    refine ⟨MvP, inferInstance, algebraMap R MvP, algebraMap MvP P, q.primeCompl, ?_, rfl, ?_⟩
    · rw [RingHom.finitePresentation_algebraMap]
      infer_instance
    · have h : (algebraMap MvP P).toAlgebra = (inferInstance : Algebra MvP P) :=
        Algebra.algebra_ext _ _ (fun _ => rfl)
      rw [h]
      infer_instance
  have hlw : IsLocalHom w := IsLocalHom.of_surjective w hsurj
  haveI : IsLocalHom (w.comp gP) := by rw [hcomp]; infer_instance
  have hlgP : IsLocalHom gP := isLocalHom_of_comp gP w
  exact ⟨P, inferInstance, inferInstance, gP, w, hlgP, hlw, hsurj, hfp, hcomp⟩

/-! `essFinitePresentation_comp_of_fg_ker` USED TO STAND HERE.  It was moved
VERBATIM (name, signature and proof unchanged) to just above
`essFinitePresentation_of_essFinitePresentation_comp`, ~3000 lines up, on
2026-07-30, because that leaf's proof consumes it and Lean needs it declared
first.  Every consumer below resolves unchanged. -/

/-! ### 05UV's FINITE-GENERATION ARGUMENT — and a CORRECTION to what 046Y costs

**SECTION NOTE for the six declarations that follow** (2026-07-27).  The note
above this one said "046Y is still not stated, for the unchanged reason: its
only consumer would be inside `fg_ker_of_flat_quotientMap`'s proof, which is
still open".  That consumer is now written, so 046Y is stated — and the
surprise is that **in the shape 05UV consumes it, 046Y needs NO Noetherian
approximation at all.**

The route audit above records `046Y (10.128.4) = the same approximation +
10.99.1`, and concludes that 046Y "shares the engine's missing machinery".
That is true of 046Y in FULL generality and **false of the instance 05UV
uses**, because 05UV never has to *prove* that `B/J'` is flat over `R` —
**00R7 hands it that**, since flatness of the base is 00R7's other conclusion.
Once `R`-flatness is an INPUT rather than an output, the entire content of 046Y
at this instance is

    Tor₁^R(P/J, R/𝔪) = 0     +     Nakayama,

and the Tor half is the **equational criterion of flatness**, which IS in the
pin (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`,
`Mathlib/RingTheory/Flat/EquationalCriterion.lean`).  So the survey's "Tor for
modules is ABSENT" item does not obstruct this half either — exactly as it did
not obstruct `rTensor_map_subtype_injective_of_flat` above.

**The refuting check**, if this note goes stale: read the hypotheses of
`inf_map_le_mul_of_flat_quotient` below and ask whether any of them has to be
*proven* rather than *supplied* inside `fg_ker_of_flat_quotientMap`.  If one
does, approximation is back.

The one thing that had to be recovered is 00R7's SECOND conclusion, which the
statement of `flat_of_flat_of_flat_quotientMap_of_essFinitePresentation` above
deliberately discards ("only `M` flat over `S` is kept, because only that is
consumed") — it is consumed now.  It is recovered rather than re-sorried,
because a flat local homomorphism of local rings is FAITHFULLY flat and
flatness descends along a faithfully flat tower.

The six declarations, in dependency order:

* `isNoetherianRing_quotient_maximalIdeal_map_of_essFinitePresentation` — the
  fibre `P/𝔪P` of an essentially-of-finite-presentation local map is
  NOETHERIAN.  This is what lets 05UV choose its `f₁,…,f_k`;
* `flat_of_faithfullyFlat_tower` — flatness DESCENDS along a faithfully flat
  tower.  General commutative algebra, absent from the pin
  (`grep -rn "FaithfullyFlat" .lake/packages/mathlib/Mathlib/RingTheory/` finds
  transitivity and base-change descent, not tower descent);
* `flat_base_of_flat_of_flat_quotientMap_of_essFinitePresentation` — **00R7's
  SECOND conclusion**;
* `inf_map_le_mul_of_flat_quotient` — the Tor-vanishing statement, in ideal
  form;
* `eq_of_fg_of_flat_quotient_of_le_sup` — **046Y**, in the shape 05UV consumes
  it;
* `eq_of_fg_le_ker_of_le_sup` — 05UV's comparison step: 00R7 and 046Y applied
  to `R → P/J'' → A`.

All six are PROVEN, and the first, second, fourth and fifth are AXIOM-CLEAN
(`#print axioms` returns `[propext, Classical.choice, Quot.sound]`); the third
and sixth carry `sorryAx` only through the 00R7 leaf they consume.
-/

/-- **THE FIBRE OF AN ESSENTIALLY-OF-FINITE-PRESENTATION LOCAL MAP IS
NOETHERIAN** (PROVEN 2026-07-27).  If `R → P` is essentially of finite
presentation and `R` is local with maximal ideal `𝔪`, then `P/𝔪P` is a
Noetherian ring.

This is the step of 05UV's proof that reads "*we can find `f₁,…,f_k ∈ J` such
that the images `f̄ᵢ ∈ B/𝔪B` generate the image `J̄` of `J` in the **Noetherian
ring** `B/𝔪B`*".  The source gets Noetherianness from the explicit shape
`B = R[x₁,…,xₙ]_𝔮`; here `P` is only abstractly essentially of finite
presentation, so it is proved from the definition.

**The proof.**  Unfold `EssFinitePresentation gP` as `P = M⁻¹T` with `R → T`
finitely presented.  Then `T/𝔪T` is a finite-type algebra over the residue
FIELD `R/𝔪` — hence Noetherian by `Algebra.FiniteType.isNoetherianRing` — and
`P/𝔪P` is a localization of it at the image of `M`, which is
`IsLocalization.of_surjective` applied to the square `T → P`, `T/𝔪T → P/𝔪P`.
`IsLocalization.isNoetherianRing` finishes.  Only finite TYPE of `R → T` is
used, so this holds verbatim for `Algebra.EssFiniteType`; it is stated for
`EssFinitePresentation` because that is what the consumer has. -/
theorem isNoetherianRing_quotient_maximalIdeal_map_of_essFinitePresentation
    {R P : Type u} [CommRing R] [CommRing P] [IsLocalRing R]
    {gP : R →+* P} (hfpP : EssFinitePresentation gP) :
    IsNoetherianRing (P ⧸ (IsLocalRing.maximalIdeal R).map gP) := by
  classical
  obtain ⟨T, _, gT, vT, M, hgT, hvT, hloc⟩ := hfpP
  letI : Algebra T P := vT.toAlgebra
  haveI : IsLocalization M P := hloc
  letI : Algebra R T := gT.toAlgebra
  have hIK : ((IsLocalRing.maximalIdeal R).map gT).map vT
      = (IsLocalRing.maximalIdeal R).map gP := by
    rw [Ideal.map_map, hvT]
  haveI : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  haveI : IsNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    inferInstanceAs (IsNoetherianRing (IsLocalRing.ResidueField R))
  have hle₁ : IsLocalRing.maximalIdeal R
      ≤ ((IsLocalRing.maximalIdeal R).map gT).comap gT := Ideal.le_comap_map
  letI : Algebra (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ (IsLocalRing.maximalIdeal R).map gT) :=
    (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map gT) gT hle₁).toAlgebra
  haveI : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R)
      (T ⧸ (IsLocalRing.maximalIdeal R).map gT) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType R T := RingHom.FiniteType.of_finitePresentation hgT
  haveI : Algebra.FiniteType R (T ⧸ (IsLocalRing.maximalIdeal R).map gT) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ R ((IsLocalRing.maximalIdeal R).map gT))
      Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType (R ⧸ IsLocalRing.maximalIdeal R)
      (T ⧸ (IsLocalRing.maximalIdeal R).map gT) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  haveI : IsNoetherianRing (T ⧸ (IsLocalRing.maximalIdeal R).map gT) :=
    Algebra.FiniteType.isNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) _
  have hle₂ : (IsLocalRing.maximalIdeal R).map gT
      ≤ ((IsLocalRing.maximalIdeal R).map gP).comap vT := by
    rw [← hIK]; exact Ideal.le_comap_map
  letI : Algebra (T ⧸ (IsLocalRing.maximalIdeal R).map gT)
      (P ⧸ (IsLocalRing.maximalIdeal R).map gP) :=
    (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map gP) vT hle₂).toAlgebra
  haveI : IsLocalization (M.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gT)))
      (P ⧸ (IsLocalRing.maximalIdeal R).map gP) := by
    refine IsLocalization.of_surjective M P
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gT)) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP)) Ideal.Quotient.mk_surjective
      ?_ ?_
    · exact RingHom.ext fun _ => rfl
    · rw [Ideal.mk_ker, Ideal.mk_ker]
      exact le_of_eq hIK.symm
  exact IsLocalization.isNoetherianRing
    (M.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gT))) _ inferInstance

open scoped TensorProduct in
/-- **FLATNESS DESCENDS ALONG A FAITHFULLY FLAT TOWER** (PROVEN 2026-07-27).
For a tower `R → C → A` with `A` FAITHFULLY flat over `C` and flat over `R`,
the intermediate `C` is flat over `R`.

Absent from the pin: `Mathlib/RingTheory/Flat/FaithfullyFlat/` has transitivity
(`Module.FaithfullyFlat.trans`) and base-change descent
(`Module.Flat.of_flat_tensorProduct`), and neither is this.

**The proof** is the one-line classical argument, mechanised: for an ideal `I`
of `R`, `A ⊗_C (C ⊗_R I) ≅ A ⊗_R I` naturally
(`TensorProduct.AlgebraTensorModule.cancelBaseChange`), so `A ⊗_C (−)` carries
`C ⊗_R I → C ⊗_R R` to `A ⊗_R I → A ⊗_R R`, which is injective because `A` is
`R`-flat; and a faithfully flat `A` REFLECTS injectivity
(`Module.FaithfullyFlat.lTensor_injective_iff_injective`).  The ideal criterion
`Module.Flat.iff_lTensor_injective'` then gives `Module.Flat R C`. -/
theorem flat_of_faithfullyFlat_tower {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra C A] [Algebra R A] [IsScalarTower R C A]
    [Module.FaithfullyFlat C A] [Module.Flat R A] : Module.Flat R C := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  set F : C ⊗[R] ↥I →ₗ[C] C ⊗[R] R :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[C] C) I.subtype with hF
  have hFfun : ⇑F = ⇑(LinearMap.lTensor C I.subtype) := rfl
  rw [← hFfun, ← Module.FaithfullyFlat.lTensor_injective_iff_injective (R := C) (M := A) F]
  set cbcI := TensorProduct.AlgebraTensorModule.cancelBaseChange R C A A ↥I with hcbcI
  set cbcR := TensorProduct.AlgebraTensorModule.cancelBaseChange R C A A R with hcbcR
  have hnat : ∀ z, cbcR (LinearMap.lTensor A F z)
      = LinearMap.lTensor A I.subtype (cbcI z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a y =>
        induction y with
        | zero => simp
        | tmul c i => simp [hF, hcbcI, hcbcR]
        | add y₁ y₂ h₁ h₂ =>
            simp only [LinearMap.lTensor_tmul] at h₁ h₂
            simp only [TensorProduct.tmul_add, map_add, LinearMap.lTensor_tmul, h₁, h₂]
    | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
  have hcomp : Function.Injective (fun z => cbcR (LinearMap.lTensor A F z)) := by
    simp only [hnat]
    exact fun x y h => cbcI.injective
      ((Module.Flat.iff_lTensor_injective'.mp inferInstance I) h)
  exact fun x y h => hcomp (by simp only [h])

/-- **00R7's SECOND CONCLUSION: `R → B` is FLAT** (PROVEN 2026-07-27).

`flat_of_flat_of_flat_quotientMap_of_essFinitePresentation` above states 00R7
with only the conclusion "`M` is flat over `S`", because at the time that was
all any consumer used.  05UV's finite-generation argument uses the OTHER half —
"*Hence we conclude that `B/J'` is flat over `R` for any choice `J'`*" — so it
is recovered here.

**It is a corollary, not a new leaf.**  00R7 gives `A` flat over `B`; `B → A` is
a local homomorphism of local rings, so `A` is FAITHFULLY flat over `B`
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`); and `A` is flat over `R` by
hypothesis.  `flat_of_faithfullyFlat_tower` then descends flatness to `B`.

So this consumes exactly the same leaf as 00R7 does and adds no open
mathematics of its own. -/
theorem flat_base_of_flat_of_flat_quotientMap_of_essFinitePresentation
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfpA : EssFinitePresentation (v.comp g))
    (hfpB : EssFinitePresentation g)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    g.Flat := by
  have hvflat : v.Flat :=
    flat_of_flat_of_flat_quotientMap_of_essFinitePresentation hfpA hfpB hflat hfib
  algebraize [g, v, v.comp g]
  haveI : IsLocalHom (algebraMap B A) := ‹IsLocalHom v›
  haveI : Module.FaithfullyFlat B A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_faithfullyFlat_tower (R := R) (C := B) (A := A)

/-- **`Tor₁^R(P/J, R/I) = 0`, WRITTEN WITHOUT `Tor`** (PROVEN 2026-07-27).

*Let `R → P` be a ring map and `J ⊆ P` an ideal with `P/J` FLAT over `R`.  Then
for every ideal `I ⊆ R`,*  `J ∩ I·P ⊆ I·J`.

That containment (the reverse is trivial) is precisely the vanishing of
`Tor₁^R(P/J, R/I)`, read off the exact sequence `0 → J → P → P/J → 0`, and it is
the only place flatness enters 046Y at the instance 05UV uses.

**This closes another "Tor is absent" item without Tor.**  The proof is the
**equational criterion of flatness**, which the pin does have
(`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`): write `m ∈ J ∩ I·P` as
`m = Σᵢ aᵢ • cᵢ` with `aᵢ ∈ I`; its image in `P/J` vanishes, so the criterion
produces `y_j ∈ P/J` and `b_{ij} ∈ R` with `c̄ᵢ = Σⱼ b_{ij} yⱼ` and
`Σᵢ aᵢ b_{ij} = 0`.  Lifting `yⱼ` to `P` makes `dᵢ := cᵢ − Σⱼ b_{ij} yⱼ'` lie in
`J`, and `m = Σᵢ aᵢ • dᵢ` because the correction term is `Σⱼ (Σᵢ aᵢ b_{ij}) yⱼ' = 0`.
Each `aᵢ • dᵢ = gP(aᵢ)·dᵢ` lies in `(I·P)·J`.

No local, Noetherian or finiteness hypothesis is used, and none is available —
this is the general statement. -/
theorem inf_map_le_mul_of_flat_quotient {R P : Type u} [CommRing R] [CommRing P]
    {gP : R →+* P} {J : Ideal P} {I : Ideal R}
    (hflat : ((Ideal.Quotient.mk J).comp gP).Flat) :
    J ⊓ I.map gP ≤ (I.map gP) * J := by
  classical
  letI : Algebra R P := gP.toAlgebra
  letI : Algebra R (P ⧸ J) := ((Ideal.Quotient.mk J).comp gP).toAlgebra
  haveI : Module.Flat R (P ⧸ J) := hflat
  have hsmul : ∀ (a : R) (p : P),
      (Ideal.Quotient.mk J) (a • p) = a • (Ideal.Quotient.mk J) p := by
    intro a p
    simp only [Algebra.smul_def]
    rfl
  rintro m ⟨hmJ, hmI⟩
  obtain ⟨n, c, gg, hsum⟩ := Submodule.mem_span_set'.mp hmI
  choose a ha hgg using fun i : Fin n => (gg i).2
  have hac : ∀ i, a i • c i = c i • ((gg i : P)) := by
    intro i
    rw [Algebra.smul_def, smul_eq_mul, ← hgg i]
    show gP (a i) * c i = c i * gP (a i)
    ring
  have hsum' : ∑ i, a i • c i = m := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ => hac i
  have hrel : ∑ i, a i • (Ideal.Quotient.mk J (c i)) = 0 := by
    calc ∑ i, a i • (Ideal.Quotient.mk J (c i))
        = Ideal.Quotient.mk J (∑ i, a i • c i) := by
          rw [map_sum]; exact (Finset.sum_congr rfl fun i _ => hsmul _ _).symm
      _ = Ideal.Quotient.mk J m := by rw [hsum']
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmJ
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose y' hy' using fun j : Fin k => Ideal.Quotient.mk_surjective (y j)
  have hdJ : ∀ i, c i - ∑ j, b i j • y' j ∈ J := by
    intro i
    have hyi : Ideal.Quotient.mk J (c i) = ∑ j, b i j • y j := hy i
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum, hyi, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [hsmul, hy' j]
  have hm : m = ∑ i, a i • (c i - ∑ j, b i j • y' j) := by
    have hexp : ∀ i : Fin n, a i • (c i - ∑ j, b i j • y' j)
        = a i • c i - ∑ j, (a i * b i j) • y' j := by
      intro i
      rw [smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_sub_distrib, hsum',
      Finset.sum_comm]
    have hzero : ∀ j : Fin k, ∑ i, (a i * b i j) • y' j = 0 := by
      intro j
      rw [← Finset.sum_smul, hb j, zero_smul]
    rw [Finset.sum_congr rfl fun j _ => hzero j]
    simp
  rw [hm]
  exact Ideal.sum_mem _ fun i _ => by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (ha i)) (hdJ i)

/-- **046Y = Stacks 10.128.4, in the shape 05UV consumes it** (PROVEN
2026-07-27 — see the section note above for why this instance costs no
Noetherian approximation).

*Let `R → P` be a LOCAL homomorphism of local rings and `J' ⊆ J''` ideals of `P`
with `J''` finitely generated.  If `P/J''` is flat over `R` and
`J'' ⊆ J' + 𝔪_R·P`, then `J' = J''`.*

05UV writes this as "*`B/J' → B/J''` is a surjective map between flat
`R`-algebras which are essentially of finite presentation which is an
isomorphism modulo `𝔪`.  Hence Lemma 10.128.4 implies that `B/J' = B/J''`*".
The essential-finite-presentation hypothesis is not needed for THIS direction —
finite generation of `J''` is what Nakayama consumes — so it is omitted;
omitting a hypothesis cannot make a true statement false.

**THE PROOF.**  `J'' ⊆ J' + 𝔪·P` and `J' ⊆ J''` put `J'' − J' ⊆ J'' ∩ 𝔪·P`, so
`inf_map_le_mul_of_flat_quotient` gives `J'' ⊆ J' + (𝔪·P)·J''`; since `R → P` is
local, `𝔪·P ⊆ 𝔪_P`, and Nakayama in the form
`Submodule.le_of_le_smul_of_le_jacobson_bot` (Stacks 00DV (4)) concludes
`J'' ⊆ J'`. -/
theorem eq_of_fg_of_flat_quotient_of_le_sup {R P : Type u} [CommRing R] [CommRing P]
    [IsLocalRing R] [IsLocalRing P] {gP : R →+* P} [IsLocalHom gP]
    {J' J'' : Ideal P} (hle : J' ≤ J'') (hfg : J''.FG)
    (hflat : ((Ideal.Quotient.mk J'').comp gP).Flat)
    (hmod : J'' ≤ J' ⊔ (IsLocalRing.maximalIdeal R).map gP) :
    J' = J'' := by
  refine le_antisymm hle ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal P)
    hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
  have h1 : J'' ≤ J' ⊔ ((IsLocalRing.maximalIdeal R).map gP) * J'' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hmod hx)
    have hzJ : z ∈ J'' := by
      have hsub := Ideal.sub_mem J'' hx (hle hy)
      simpa using hsub
    exact Submodule.mem_sup.mpr ⟨y, hy, z, inf_map_le_mul_of_flat_quotient hflat ⟨hzJ, hz⟩, rfl⟩
  refine h1.trans (sup_le_sup_left ?_ _)
  rw [Ideal.smul_eq_mul]
  exact Ideal.mul_mono (IsLocalRing.map_maximalIdeal_le gP) le_rfl

/-- **05UV's COMPARISON STEP: any two finitely generated `J' ⊆ J'' ⊆ ker w`
with the same image modulo `𝔪` are EQUAL** (PROVEN 2026-07-27).

This is steps 2–3 of 05UV's finite-generation argument: 00R7 applied to
`R → P/J'' → A` makes `P/J''` flat over `R`, and 046Y then forces `J' = J''`.

**The bookkeeping, which is the whole proof.**  `J'' ⊆ ker w ⊆ 𝔪_P`, so `P/J''`
is local; `essFinitePresentation_comp_of_fg_ker` makes `R → P/J''` essentially
of finite presentation because `J''` is finitely generated (this is the second
of the two uses that lemma was written for); and the fibre hypothesis transports
because the natural map

    (P/J'') / 𝔪·(P/J'')  ⟶  B / 𝔪·B

is BIJECTIVE — surjective since `w` is, and injective because
`w⁻¹(𝔪·B) = 𝔪·P + ker w = 𝔪·P + J''` by `Ideal.comap_map_of_surjective`
together with `hkerle`.  A bijective ring map is flat, so the transported
fibre map is flat by `RingHom.Flat.comp`.

**FAITHFULNESS.**  `hkerle` (`ker w ⊆ J'' + 𝔪·P`) is load-bearing and is exactly
05UV's condition that `J'` induce an isomorphism `(B/J')⊗R/𝔪 ≅ B/𝔪B`; without
it the two fibres differ and the transport is false. -/
theorem eq_of_fg_le_ker_of_le_sup {R P B A : Type u}
    [CommRing R] [CommRing P] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing P] [IsLocalRing B] [IsLocalRing A]
    {gP : R →+* P} {w : P →+* B} {v : B →+* A}
    [IsLocalHom gP] [IsLocalHom w] [IsLocalHom v]
    (hfpP : EssFinitePresentation gP)
    (hw : Function.Surjective w)
    (hfp : EssFinitePresentation (v.comp (w.comp gP)))
    (hflat : (v.comp (w.comp gP)).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp (w.comp gP))) v
        (map_le_comap_map_comp (w.comp gP) v (IsLocalRing.maximalIdeal R))).Flat)
    {J' J'' : Ideal P} (hle : J' ≤ J'') (hJ''le : J'' ≤ RingHom.ker w) (hfg : J''.FG)
    (hkerle : RingHom.ker w ≤ J'' ⊔ (IsLocalRing.maximalIdeal R).map gP)
    (hmod : J'' ≤ J' ⊔ (IsLocalRing.maximalIdeal R).map gP) :
    J' = J'' := by
  classical
  have hkerP : RingHom.ker w ≤ IsLocalRing.maximalIdeal P := by
    refine IsLocalRing.le_maximalIdeal ?_
    rw [Ideal.ne_top_iff_one]
    intro h
    rw [RingHom.mem_ker, map_one] at h
    exact one_ne_zero h
  have hJ''P : J'' ≤ IsLocalRing.maximalIdeal P := hJ''le.trans hkerP
  have hJ''top : J'' ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal P).ne_top (top_le_iff.mp (h ▸ hJ''P))
  haveI : Nontrivial (P ⧸ J'') := Ideal.Quotient.nontrivial_iff.mpr hJ''top
  haveI hlmk : IsLocalHom (Ideal.Quotient.mk J'') :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (P ⧸ J'') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J'') Ideal.Quotient.mk_surjective
  haveI : IsLocalHom ((Ideal.Quotient.mk J'').comp gP) := RingHom.isLocalHom_comp _ _
  have hw₂ker : ∀ a ∈ J'', w a = 0 := fun a ha => hJ''le ha
  have hw₂surj : Function.Surjective (Ideal.Quotient.lift J'' w hw₂ker) := by
    intro b
    obtain ⟨p, rfl⟩ := hw b
    exact ⟨Ideal.Quotient.mk J'' p, rfl⟩
  haveI : IsLocalHom (Ideal.Quotient.lift J'' w hw₂ker) :=
    IsLocalHom.of_surjective _ hw₂surj
  haveI : IsLocalHom (v.comp (Ideal.Quotient.lift J'' w hw₂ker)) := RingHom.isLocalHom_comp _ _
  -- the comparison map between the two fibres, and its bijectivity
  have hle_e : (IsLocalRing.maximalIdeal R).map ((Ideal.Quotient.mk J'').comp gP)
      ≤ ((IsLocalRing.maximalIdeal R).map (w.comp gP)).comap
        (Ideal.Quotient.lift J'' w hw₂ker) :=
    map_le_comap_map_comp ((Ideal.Quotient.mk J'').comp gP)
      (Ideal.Quotient.lift J'' w hw₂ker) (IsLocalRing.maximalIdeal R)
  have hebij : Function.Bijective
      (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (w.comp gP))
        (Ideal.Quotient.lift J'' w hw₂ker) hle_e) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
      have hx' : w p ∈ (IsLocalRing.maximalIdeal R).map (w.comp gP) := by
        rw [show Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (w.comp gP))
              (Ideal.Quotient.lift J'' w hw₂ker) hle_e
              (Ideal.Quotient.mk _ (Ideal.Quotient.mk J'' p))
            = Ideal.Quotient.mk _ (w p) from rfl,
          Ideal.Quotient.eq_zero_iff_mem] at hx
        exact hx
      have h1 : (IsLocalRing.maximalIdeal R).map (w.comp gP)
          = ((IsLocalRing.maximalIdeal R).map gP).map w := (Ideal.map_map gP w).symm
      have h2 : p ∈ ((IsLocalRing.maximalIdeal R).map gP) ⊔ RingHom.ker w := by
        have hcm := Ideal.comap_map_of_surjective w hw ((IsLocalRing.maximalIdeal R).map gP)
        rw [← RingHom.ker_eq_comap_bot] at hcm
        rw [← hcm]
        rw [h1] at hx'
        exact hx'
      have h3 : p ∈ J'' ⊔ (IsLocalRing.maximalIdeal R).map gP :=
        sup_le (le_sup_right) hkerle h2
      rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_map]
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp h3
      have hyz : (Ideal.Quotient.mk J'') (y + z) = (Ideal.Quotient.mk J'') z := by
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]
      rw [hyz]
      exact Ideal.mem_map_of_mem _ hz
    · intro y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨p, rfl⟩ := hw b
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk J'' p), rfl⟩
  have hEq : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp (w.comp gP))) v
        (map_le_comap_map_comp (w.comp gP) v (IsLocalRing.maximalIdeal R))).comp
      (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (w.comp gP))
        (Ideal.Quotient.lift J'' w hw₂ker) hle_e)
      = Ideal.quotientMap
          ((IsLocalRing.maximalIdeal R).map
            ((v.comp (Ideal.Quotient.lift J'' w hw₂ker)).comp
              ((Ideal.Quotient.mk J'').comp gP)))
          (v.comp (Ideal.Quotient.lift J'' w hw₂ker))
          (map_le_comap_map_comp ((Ideal.Quotient.mk J'').comp gP)
            (v.comp (Ideal.Quotient.lift J'' w hw₂ker)) (IsLocalRing.maximalIdeal R)) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun c => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  have hfib₂ : (Ideal.quotientMap
          ((IsLocalRing.maximalIdeal R).map
            ((v.comp (Ideal.Quotient.lift J'' w hw₂ker)).comp
              ((Ideal.Quotient.mk J'').comp gP)))
          (v.comp (Ideal.Quotient.lift J'' w hw₂ker))
          (map_le_comap_map_comp ((Ideal.Quotient.mk J'').comp gP)
            (v.comp (Ideal.Quotient.lift J'' w hw₂ker))
            (IsLocalRing.maximalIdeal R))).Flat :=
    hEq ▸ RingHom.Flat.comp (RingHom.Flat.of_bijective hebij) hfib
  have hfpB₂ : EssFinitePresentation ((Ideal.Quotient.mk J'').comp gP) :=
    essFinitePresentation_comp_of_fg_ker hfpP Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hfg)
  have hflat₂ : ((Ideal.Quotient.mk J'').comp gP).Flat :=
    flat_base_of_flat_of_flat_quotientMap_of_essFinitePresentation
      (v := v.comp (Ideal.Quotient.lift J'' w hw₂ker)) hfp hfpB₂ hflat hfib₂
  exact eq_of_fg_of_flat_quotient_of_le_sup hle hfg hflat₂ hmod

/-- **THE WHOLE REMAINING CONTENT OF 05UV's FIRST CONCLUSION: the ideal `J` is
FINITELY GENERATED** (PROVEN 2026-07-27; cut 2026-07-27 out of
`essFinitePresentation_of_essFiniteType_of_flat_quotientMap` once the
presentation bookkeeping above was proven).

*Let `R → P → B → A` be local homomorphisms of local rings with `R → P`
essentially of finite presentation and `P → B` SURJECTIVE.  Under 05UV's
hypotheses — `R → A` essentially of finite presentation, `A` flat over `R`,
and `A/𝔪_R A` flat over `B/𝔪_R B` — the kernel of `P → B` is finitely
generated.*

This is 05UV's `J = I·B'` with `P = B'`, `B = S`, `A = M = S'`, and it is
literally the sentence its proof spends all its work on.  The two lemmas
above supply `P` (from `R → B` essentially of finite type) and convert this
conclusion back into `EssFinitePresentation`, so the leaf below is now pure
assembly and **nothing else in 05UV's first conclusion is open**.

**THE PROOF, from the Stacks argument, now written out.**

1. Choose `f₁,…,f_k ∈ J` whose images generate `J̄ ⊂ P/𝔪P`.  This is possible
   because `P/𝔪P` is NOETHERIAN
   (`isNoetherianRing_quotient_maximalIdeal_map_of_essFinitePresentation`), and
   it is the only place the essential finite presentation of `R → P` is used
   outside 00R7.  Let `J₀ = (f₁,…,f_k)`, so `J₀ ⊆ J` and `J₀ + 𝔪P = J + 𝔪P`.
2. For each finitely generated `J'' ⊆ J` with `J'' + 𝔪P = J + 𝔪P`, apply
   **00R7** to `R → P/J'' → A`; `P/J''` is then flat over `R`.
3. **046Y** forces `J₀ = J''`.  Steps 2 and 3 are the single lemma
   `eq_of_fg_le_ker_of_le_sup` above.
4. Take `J'' = J₀ + (x)` for `x ∈ J`: it satisfies 2's hypotheses, so `x ∈ J₀`.
   Hence `J = J₀`, which is finitely generated.

**A CORRECTION about what 046Y costs.**  The previous version of this docstring
said: "*046Y is the one genuinely new tool this leaf needs … its own proof is
approximation (10.127.13 / 10.128.3) plus the Noetherian 10.99.1, so it shares
the engine's missing machinery.*"  That is right about 046Y in full generality
and **wrong about the instance 05UV uses**, and the difference is the whole
reason this leaf closed: 05UV never has to PROVE that `P/J''` is flat over `R`,
because **00R7 hands it that** as its second conclusion.  With `R`-flatness an
input, 046Y at this instance is `Tor₁^R(P/J'', R/𝔪) = 0` plus Nakayama, and the
Tor half is the equational criterion of flatness, which is in the pin.  See the
section note "05UV's FINITE-GENERATION ARGUMENT" above, and
`inf_map_le_mul_of_flat_quotient` / `eq_of_fg_of_flat_quotient_of_le_sup` for
the two halves.

**So the only leaf under this declaration is 00R7**, i.e.
`flat_of_flat_of_flat_quotientMap_of_essFinitePresentation` and the two open
leaves beneath it (the approximation half and the Noetherian local criterion).
Nothing in the finite-generation argument is open.

**FAITHFULNESS.**  Every hypothesis here is one of 05UV's, transported along
the presentation rather than weakened: `hfpP` is "`B'` is essentially of
finite presentation over `R`" (which 05UV *proves* about its `B'` and which
`exists_essFinitePresentation_surjective_of_essFiniteType` proves about this
one), `hw` is `S = B'/J`, and `hfp`/`hflat`/`hfib` are 05UV's (1), (6) and
(5) verbatim at `M = S' = A`.  A false instance of this leaf would be a false
instance of 05UV. -/
theorem fg_ker_of_flat_quotientMap {R P B A : Type u}
    [CommRing R] [CommRing P] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing P] [IsLocalRing B] [IsLocalRing A]
    {gP : R →+* P} {w : P →+* B} {v : B →+* A}
    [IsLocalHom gP] [IsLocalHom w] [IsLocalHom v]
    (hfpP : EssFinitePresentation gP)
    (hw : Function.Surjective w)
    (hfp : EssFinitePresentation (v.comp (w.comp gP)))
    (hflat : (v.comp (w.comp gP)).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp (w.comp gP))) v
        (map_le_comap_map_comp (w.comp gP) v (IsLocalRing.maximalIdeal R))).Flat) :
    (RingHom.ker w).FG := by
  classical
  haveI := isNoetherianRing_quotient_maximalIdeal_map_of_essFinitePresentation hfpP
  -- Step 1: the image of `J` in the NOETHERIAN fibre `P/𝔪P` is finitely generated,
  -- and its generators lift to elements of `J`.
  obtain ⟨t, ht⟩ := Ideal.fg_of_isNoetherianRing
    ((RingHom.ker w).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP)))
  have hlift : ∀ y ∈ t, ∃ x, x ∈ RingHom.ker w ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP) x = y := by
    intro y hy
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      (ht ▸ Ideal.subset_span hy)
  choose f hfJ hfmk using hlift
  refine ⟨t.attach.image (fun y => f y.1 y.2), ?_⟩
  set J₀ : Ideal P := Ideal.span ↑(t.attach.image (fun y => f y.1 y.2)) with hJ₀
  have hJ₀le : J₀ ≤ RingHom.ker w := by
    rw [hJ₀, Ideal.span_le]
    rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact hfJ y.1 y.2
  have hJ₀map : J₀.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP))
      = (RingHom.ker w).map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP)) := by
    rw [hJ₀, Ideal.map_span, ← ht]
    congr 1
    ext y
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
      Set.image_image, true_and, Subtype.exists]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hfmk z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hfmk y hy⟩
  -- Step 1': hence `J₀` and `J` have the same image modulo `𝔪P`.
  have hsup : RingHom.ker w ⊔ (IsLocalRing.maximalIdeal R).map gP
      = J₀ ⊔ (IsLocalRing.maximalIdeal R).map gP := by
    have h1 := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP))
      Ideal.Quotient.mk_surjective (RingHom.ker w)
    have h2 := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map gP))
      Ideal.Quotient.mk_surjective J₀
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h1 h2
    rw [← h1, ← h2, hJ₀map]
  -- Steps 2–4: the comparison step at `J₀ ⊆ J₀ + (x)` puts every `x ∈ J` into `J₀`.
  have hkey : RingHom.ker w ≤ J₀ := by
    intro x hx
    have hx' : x ∈ J₀ ⊔ (IsLocalRing.maximalIdeal R).map gP := by
      rw [← hsup]; exact Ideal.mem_sup_left hx
    have hfg₀ : J₀.FG := ⟨_, rfl⟩
    have h := eq_of_fg_le_ker_of_le_sup (J' := J₀) (J'' := J₀ ⊔ Ideal.span {x})
      hfpP hw hfp hflat hfib
      le_sup_left
      (sup_le hJ₀le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)))
      (Submodule.FG.sup hfg₀ ⟨{x}, by simp⟩)
      (by
        calc RingHom.ker w ≤ RingHom.ker w ⊔ (IsLocalRing.maximalIdeal R).map gP := le_sup_left
          _ = J₀ ⊔ (IsLocalRing.maximalIdeal R).map gP := hsup
          _ ≤ (J₀ ⊔ Ideal.span {x}) ⊔ (IsLocalRing.maximalIdeal R).map gP :=
              sup_le_sup_right le_sup_left _)
      (sup_le le_sup_left (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx')))
    have hmem : x ∈ J₀ ⊔ Ideal.span {x} :=
      Ideal.mem_sup_right (Ideal.subset_span rfl)
    rw [← h] at hmem
    exact hmem
  exact le_antisymm hJ₀le hkey

/-- **THE FINITE-GENERATION HALF: 05UV's OTHER conclusion** (PROVEN
2026-07-27 from the presentation lemmas above and the single leaf
`fg_ker_of_flat_quotientMap`).  Under exactly the hypotheses of
`flat_of_flat_of_flat_quotientMap`, the map `R → B` is essentially of finite
PRESENTATION and not merely of finite type.

This is the *first* of 05UV's two conclusions, stated verbatim; the leaf below
is the second.  Splitting them is what makes the assembly a two-line
application, and it is the source's own structure: 05UV's proof ends "*Thus we
see that `S` is essentially of finite presentation over `R`.  Lemma 10.128.8
[00R7] applies to `R → S → S'` and we conclude.*"

**THE PROOF is 05UV's own opening move, now written out.**  Present `B` as
`P/J` with `R → P` essentially of finite presentation and `P` LOCAL
(`exists_essFinitePresentation_surjective_of_essFiniteType`); the content is
that `J = ker(P → B)` is finitely generated (`fg_ker_of_flat_quotientMap`, the
one remaining leaf); and a quotient by a finitely generated ideal is again
essentially of finite presentation (`essFinitePresentation_comp_of_fg_ker`).

`subst` is what makes the assembly three lines: `g` is an implicit variable,
so the factorisation `w ∘ gP = g` can simply replace it, and `hfp`, `hflat`
and `hfib` then match the leaf's hypotheses syntactically.

**WHY THIS SPLIT IS SAFE.**  Both halves are literal Stacks statements
instantiated at `M = S' = A`, and their conjunction is exactly 05UV — so
neither can be false unless 05UV is, and the assembly below consumes both
with no glue that could hide a gap. -/
theorem essFinitePresentation_of_essFiniteType_of_flat_quotientMap {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfp : EssFinitePresentation (v.comp g))
    (hft : g.EssFiniteType)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    EssFinitePresentation g := by
  obtain ⟨P, _, _, gP, w, _, _, hw, hfpP, hcomp⟩ :=
    exists_essFinitePresentation_surjective_of_essFiniteType hft
  subst hcomp
  exact essFinitePresentation_comp_of_fg_ker hfpP hw
    (fg_ker_of_flat_quotientMap hfpP hw hfp hflat hfib)

/-- **CRITÈRE DE PLATITUDE PAR FIBRES, ring level — Stacks 05UV** (PROVEN
2026-07-27 from the two leaves above; see the section note for the route
audit that produced the cut).

*Let `R → B → A` be local homomorphisms of local rings, with `R → A`
essentially of finite presentation and `R → B` essentially of finite type.
If `A` is flat over `R` and `A/𝔪_R A` is flat over `B/𝔪_R B`, then `A` is
flat over `B`.*

**FAITHFULNESS — this is 05UV instantiated at `M = S' = A`, with the source
quoted in the section note above.**  Hypotheses (3) `M` of finite
presentation over `S'` and (4) `M ≠ 0` are omitted because at `M = S' = A`
they are theorems, not assumptions: `A` is finitely presented over itself,
and `[IsLocalRing A]` already gives `Nontrivial A`.  The conclusion is
likewise *weaker* than 05UV's, which also asserts that `B` is essentially of
finite presentation and flat over `R`; only `A` flat over `B` is kept,
because only that is consumed.  A weaker conclusion and fewer hypotheses
cannot turn a true statement false, so this statement is safe in both
directions.

**THE PROOF is the last two sentences of 05UV**: the finite-generation half
upgrades `R → B` from essentially of finite TYPE to essentially of finite
PRESENTATION, and 00R7 then applies to `R → B → A` unchanged.  Note that
`hfp`, `hflat` and `hfib` are each consumed TWICE — once by each half — which
is why neither leaf may drop them. -/
theorem flat_of_flat_of_flat_quotientMap {R B A : Type u}
    [CommRing R] [CommRing B] [CommRing A]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing A]
    {g : R →+* B} {v : B →+* A} [IsLocalHom g] [IsLocalHom v]
    (hfp : EssFinitePresentation (v.comp g))
    (hft : g.EssFiniteType)
    (hflat : (v.comp g).Flat)
    (hfib : (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map (v.comp g)) v
        (map_le_comap_map_comp g v (IsLocalRing.maximalIdeal R))).Flat) :
    v.Flat :=
  -- Stacks 05UV, final two sentences: upgrade `R → B` from essentially of
  -- finite TYPE to essentially of finite PRESENTATION, then apply 00R7.
  flat_of_flat_of_flat_quotientMap_of_essFinitePresentation hfp
    (essFinitePresentation_of_essFiniteType_of_flat_quotientMap hfp hft hflat hfib)
    hflat hfib

/-! `essFinitePresentation_of_isLocalization` USED TO STAND HERE.  Moved VERBATIM
to just above `essFinitePresentation_of_essFinitePresentation_comp` on 2026-07-30,
for the same reason as `essFinitePresentation_comp_of_fg_ker` — see the note at
that lemma's old site.  Every consumer below resolves unchanged. -/

/-- **The localization of a finitely presented map is essentially of finite
presentation.**  This is the `EssFinitePresentation` analogue of mathlib's
`RingHom.HoldsForLocalization.isLocalizationMap`, and the proof is that
proof's factorization specialized to a finitely presented `f`:
`IsLocalization.map S' f` factors as the `M`-localized map
`R' → (M.map f)⁻¹S`, which is finitely presented by
`RingHom.finitePresentation_localizationPreserves`, followed by the further
localization `(M.map f)⁻¹S → S'`.

Stating it directly, rather than deriving it from the generic
`isLocalizationMap`, is what lets the whole stalk leaf avoid
`StableUnderComposition` for `EssFinitePresentation` — which is the only one
of the four meta-properties with real content, since a finitely presented
algebra over a localization descends to a finitely presented algebra only
after clearing denominators in the *relations*. -/
theorem essFinitePresentation_isLocalizationMap
    {R S : Type u} [CommRing R] [CommRing S]
    {M : Submonoid R} {T : Submonoid S}
    {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalization M R']
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S']
    {f : R →+* S} (hy : M ≤ Submonoid.comap f T) (hf : f.FinitePresentation) :
    EssFinitePresentation (IsLocalization.map (S := R') S' f hy) := by
  have hle : Submonoid.map f M ≤ T := by simpa [Submonoid.map_le_iff_le_comap]
  letI : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsLocalization (T.map (algebraMap S (Localization (M.map f)))) S' :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (M.map f) T hle
  have heq : IsLocalization.map (S := R') S' f hy =
      (algebraMap (Localization (M.map f)) S').comp
        (IsLocalization.map (M := M) (T := M.map f) (S := R') (Localization (M.map f)) f
          (M.le_comap_map)) := by
    apply IsLocalization.ringHom_ext M
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact essFinitePresentation_of_isLocalization
    (T.map (algebraMap S (Localization (M.map f))))
    (RingHom.finitePresentation_localizationPreserves f M R' _ hf)

/-- **`EssFinitePresentation` respects isomorphisms.**  Post-composition
transports the witnessing localization along the equivalence
(`IsLocalization.isLocalization_of_algEquiv`); pre-composition is absorbed
into the finitely presented half, using
`RingHom.finitePresentation_respectsIso`. -/
theorem essFinitePresentation_respectsIso :
    RingHom.RespectsIso @EssFinitePresentation := by
  constructor
  · rintro R S T' _ _ _ f e ⟨T₀, _, g, v, M, hg, hv, hloc⟩
    refine ⟨T₀, ‹_›, g, e.toRingHom.comp v, M, hg, by rw [RingHom.comp_assoc, hv], ?_⟩
    letI : Algebra T₀ S := v.toAlgebra
    letI : Algebra T₀ T' := (e.toRingHom.comp v).toAlgebra
    exact IsLocalization.isLocalization_of_algEquiv (S := S) M
      (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))
  · rintro R S T' _ _ _ f e ⟨T₀, _, g, v, M, hg, hv, hloc⟩
    exact ⟨T₀, ‹_›, g.comp e.toRingHom, v, M,
      RingHom.finitePresentation_respectsIso.2 g e hg,
      by rw [← RingHom.comp_assoc, hv], hloc⟩

/-- **The stalk of a morphism locally of finite presentation is essentially
of finite presentation** (PROVEN 2026-07-27 — general scheme theory, no
abelian varieties).

This is the exact analogue of mathlib's
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`
(`Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:99`), which proves
`(f.stalkMap x).hom.EssFiniteType` for `f` locally of finite type.  Mathlib
has NO finite-presentation counterpart: `grep -rln stalkMap
Mathlib/AlgebraicGeometry/` does not list
`Morphisms/FinitePresentation.lean`, and that file contains no `stalkMap` at
all.  A hit there refutes this note.

**Why it is true**, and why the route is the same as mathlib's: on affine
opens `f` is a finitely presented `R → S`, and the stalk map is
`R_𝔭 → S_𝔮`.  Now `S ⊗_R R_𝔭` is finitely presented over `R_𝔭` (finite
presentation is stable under base change) and `S_𝔮` is a localization of it,
so the composite is a localization of a finitely presented `R_𝔭`-algebra —
which is `EssFinitePresentation` by definition.

**HOW IT IS PROVEN, and the ONE STALE CLAIM this replaces.**  The route is
`HasRingHomProperty.stalkMap_of_respectsIso`, exactly as for the finite-type
one.  The previous version of this docstring predicted that this would need
**four** closure properties for `EssFinitePresentation` (`respectsIso`,
`stableUnderComposition`, `isStableUnderBaseChange`/`localizationPreserves`,
`holdsForLocalization`), and called `stableUnderComposition` "the only one
with any content".  That was right about the content and wrong about the
requirement: `stalkMap_of_respectsIso` asks only for

* `RespectsIso` of the *target* property — `essFinitePresentation_respectsIso`
  above, which needs no composition lemma at all; and
* the localized-map statement **for a finitely presented `f` only** —
  `essFinitePresentation_isLocalizationMap` above.

`stableUnderComposition` for `EssFinitePresentation` is therefore **not
needed here and is not proven**.  That matters, because it is the one with
the real mathematics in it: a finitely presented algebra over a localization
`M⁻¹T` descends to a finitely presented `T`-algebra only after clearing
denominators in the *relations*, and unlike the finite-type case the
subalgebra idiom is unavailable (see `EssFinitePresentation`'s own
docstring).  Anyone who later wants `EssFinitePresentation` as a genuine
meta-property should expect that lemma to be the whole cost. -/
theorem essFinitePresentation_stalkMap {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [LocallyOfFinitePresentation φ] (x : X) :
    EssFinitePresentation (φ.stalkMap x).hom :=
  HasRingHomProperty.stalkMap_of_respectsIso essFinitePresentation_respectsIso
    (fun _ hf _ _ ↦ essFinitePresentation_isLocalizationMap _ _ hf) ‹_› x

/-! ### The stalk of a scheme-theoretic fibre

The three-line summary of this block: `Scheme.Hom.fiberι` is a
**preimmersion** (mathlib, `AlgebraicGeometry/Fiber.lean`), so its stalk maps
are surjective; the pullback square defining the fibre forces `𝔪_s` into the
kernel; and the reverse inclusion is supplied by the universal property of
`Spec` of a LOCAL ring (`AlgebraicGeometry.SpecToEquivOfLocalRing`), which
produces a morphism `Spec (𝒪_{X,x}/𝔪_s𝒪_{X,x}) ⟶ X_s` splitting it.

That third step is the whole trick, and it is why this needed no
stalk-of-pullback theory (which mathlib indeed does not have — the greps on
`exists_ringEquiv_stalkMap_fiberMapOver` below were re-run 2026-07-27 and are
still empty).  `Scheme.stalkClosedPointTo` turns the morphism into a ring map
`𝒪_{X_s,z} ⟶ 𝒪_{X,x}/𝔪_s𝒪_{X,x}` which is a LEFT INVERSE of the surjection, so
the surjection is injective as well.
-/

section FiberStalk

/-- Every stalk of `Spec κ(s)` has trivial maximal ideal: `Spec` of a field has
one point and its stalk there is that field. -/
theorem maximalIdeal_stalk_residueField_eq_bot {S : Scheme.{u}} (s : S)
    (w : Spec (S.residueField s)) :
    IsLocalRing.maximalIdeal ((Spec (S.residueField s)).presheaf.stalk w) = ⊥ := by
  obtain rfl : w = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum _) _ _
  have hbij := ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom
  haveI : IsLocalHom (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom.hom :=
    _root_.IsLocalHom.of_surjective _ hbij.2
  rw [← IsLocalRing.maximalIdeal_comap
      (AlgebraicGeometry.stalkClosedPointIso (S.residueField s)).hom.hom,
    IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ hbij.1]

/-- A `stalkCongr` isomorphism maps the maximal ideal into the maximal ideal —
it is an isomorphism, hence surjective, hence local. -/
theorem stalkCongr_mem_maximalIdeal {Y : Scheme.{u}} {y y' : Y} (h : Inseparable y y')
    {a : Y.presheaf.stalk y} (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    (Y.presheaf.stalkCongr h).hom.hom a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y') := by
  haveI : IsLocalHom (Y.presheaf.stalkCongr h).hom.hom :=
    _root_.IsLocalHom.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  exact _root_.map_nonunit _ _ ha

/-- The stalk map of `Spec κ(s) ⟶ S` kills the maximal ideal: it is a local
homomorphism into a ring whose maximal ideal is `⊥`. -/
theorem stalkMap_fromSpecResidueField_eq_zero {S : Scheme.{u}} (s : S)
    (w : Spec (S.residueField s)) {a : S.presheaf.stalk (S.fromSpecResidueField s w)}
    (ha : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (S.fromSpecResidueField s w))) :
    ((S.fromSpecResidueField s).stalkMap w).hom a = 0 := by
  have h := _root_.map_nonunit ((S.fromSpecResidueField s).stalkMap w).hom a ha
  rw [maximalIdeal_stalk_residueField_eq_bot] at h
  simpa using h

variable {X S : Scheme.{u}} (p : X ⟶ S) (s : S) (z : p.fiber s)

/-- The ideal `𝔪_s · 𝒪_{X,x}` at the point `x = fiberι z`. -/
noncomputable abbrev fiberStalkIdeal : Ideal (X.presheaf.stalk (p.fiberι s z)) :=
  (IsLocalRing.maximalIdeal (S.presheaf.stalk (p (p.fiberι s z)))).map
    (p.stalkMap (p.fiberι s z)).hom

/-- `p` sends a point of the fibre to the image of the residue-field point;
this is `Scheme.Hom.fiber_fac` read on points. -/
theorem map_fiberι_eq_fromSpecResidueField :
    p (p.fiberι s z) = S.fromSpecResidueField s (p.fiberToSpecResidueField s z) := by
  rw [← Scheme.Hom.comp_apply, p.fiber_fac s, Scheme.Hom.comp_apply]

/-- **`𝔪_s · 𝒪_{X,x}` dies in the stalk of the fibre.**  The composite
`𝒪_{S,s} → 𝒪_{X,x} → 𝒪_{X_s,z}` factors through `κ(s)` by the pullback square,
and `κ(s)` has trivial maximal ideal. -/
theorem fiberStalkIdeal_le_ker :
    fiberStalkIdeal p s z ≤ RingHom.ker ((p.fiberι s).stalkMap z).hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hc : ((p.fiberι s).stalkMap z).hom ((p.stalkMap (p.fiberι s z)).hom a)
      = ((p.fiberι s ≫ p).stalkMap z).hom a := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  rw [hc, Scheme.Hom.stalkMap_congr_hom _ _ (p.fiber_fac s) z, Scheme.Hom.stalkMap_comp]
  show ((p.fiberToSpecResidueField s).stalkMap z).hom
      (((S.fromSpecResidueField s).stalkMap (p.fiberToSpecResidueField s z)).hom
        ((S.presheaf.stalkCongr
          (Inseparable.of_eq (map_fiberι_eq_fromSpecResidueField p s z))).hom.hom a)) = 0
  rw [stalkMap_fromSpecResidueField_eq_zero s _ (stalkCongr_mem_maximalIdeal _ ha), map_zero]

/-- `fiberι` is a preimmersion, so it is surjective on stalks. -/
theorem surjective_fiberι_stalkMap :
    Function.Surjective ((p.fiberι s).stalkMap z).hom :=
  (p.fiberι s).stalkMap_surjective z

/-- A point of `p.fiber s` lies over `s`. -/
theorem map_fiberι_eq_base : p (p.fiberι s z) = s := by
  rw [map_fiberι_eq_fromSpecResidueField, Scheme.fromSpecResidueField_apply]

/-- **THE STALK OF THE FIBRE IS THE QUOTIENT OF THE STALK** (PROVEN
2026-07-27): `𝒪_{X_s, z} ≅ 𝒪_{X,x} ⧸ 𝔪_s·𝒪_{X,x}` where `x = fiberι z`, and the
isomorphism carries the quotient map to the stalk map of `fiberι`.

*Surjectivity* is `IsPreimmersion (p.fiberι s)`, *`𝔪_s ⊆ ker`* is
`fiberStalkIdeal_le_ker`, and *`ker ⊆ 𝔪_s`* is the interesting half: write
`A = 𝒪_{X,x} ⧸ 𝔪_s·𝒪_{X,x}`, a LOCAL ring because `p.stalkMap x` is a local
homomorphism, and build `ψ : Spec A ⟶ X_s` out of the two legs
`Spec A ⟶ Spec 𝒪_{X,x} ⟶ X` and `Spec A ⟶ Spec κ(s)` — the second exists
precisely because `𝔪_s` dies in `A` by construction.  Then
`Scheme.stalkClosedPointTo ψ` is a left inverse of the surjection, by the
universal property `AlgebraicGeometry.SpecToEquivOfLocalRing` (morphisms out of
`Spec` of a local ring = a point plus a local homomorphism on the stalk).  A
left inverse makes the surjection injective, so it is an isomorphism. -/
theorem exists_ringEquiv_stalk_fiber :
    ∃ e : (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) ≃+*
          ((p.fiber s).presheaf.stalk z),
      e.toRingHom.comp (Ideal.Quotient.mk _) = ((p.fiberι s).stalkMap z).hom := by
  haveI hnt : Nontrivial (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top _).ne
  haveI hlr : IsLocalRing (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set A : CommRingCat.{u} :=
    CommRingCat.of (X.presheaf.stalk (p.fiberι s z) ⧸ fiberStalkIdeal p s z) with hA
  set mk0 : X.presheaf.stalk (p.fiberι s z) ⟶ A :=
    CommRingCat.ofHom (Ideal.Quotient.mk (fiberStalkIdeal p s z)) with hmk0
  haveI : IsLocalHom mk0.hom := _root_.IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hps : p (p.fiberι s z) = s := map_fiberι_eq_base p s z
  set cg : S.presheaf.stalk s ⟶ S.presheaf.stalk (p (p.fiberι s z)) :=
    (S.presheaf.stalkCongr (Inseparable.of_eq hps.symm)).hom with hcg
  set f0 : S.presheaf.stalk s ⟶ A := cg ≫ p.stalkMap (p.fiberι s z) ≫ mk0 with hf0def
  have hf0 : ∀ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s), f0.hom a = 0 := by
    intro a ha
    have h1 : cg.hom a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk (p (p.fiberι s z))) :=
      stalkCongr_mem_maximalIdeal _ ha
    have h2 : (p.stalkMap (p.fiberι s z)).hom (cg.hom a) ∈ fiberStalkIdeal p s z :=
      Ideal.mem_map_of_mem _ h1
    show mk0.hom ((p.stalkMap (p.fiberι s z)).hom (cg.hom a)) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h2
  set lif : S.residueField s ⟶ A :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ f0.hom hf0) with hlifdef
  have hlif : S.residue s ≫ lif = f0 := by
    ext a
    rfl
  set α : Spec A ⟶ X := Spec.map mk0 ≫ X.fromSpecStalk (p.fiberι s z) with hα
  set β : Spec A ⟶ Spec (S.residueField s) := Spec.map lif with hβ
  have hLHS : α ≫ p = Spec.map (p.stalkMap (p.fiberι s z) ≫ mk0) ≫
      S.fromSpecStalk (p (p.fiberι s z)) := by
    rw [hα, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
  have hRHS : β ≫ S.fromSpecResidueField s = Spec.map (p.stalkMap (p.fiberι s z) ≫ mk0) ≫
      S.fromSpecStalk (p (p.fiberι s z)) := by
    rw [hβ, Scheme.fromSpecResidueField, ← Spec.map_comp_assoc, hlif, hf0def, hcg,
      TopCat.Presheaf.stalkCongr_hom, Spec.map_comp_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hsq : α ≫ p = β ≫ S.fromSpecResidueField s := by rw [hLHS, hRHS]
  set ψ : Spec A ⟶ p.fiber s := Limits.pullback.lift α β hsq with hψ
  have hψ1 : ψ ≫ p.fiberι s = α := Limits.pullback.lift_fst _ _ _
  have hψ1' : ψ ≫ p.fiberι s =
      (SpecToEquivOfLocalRing X A).symm ⟨p.fiberι s z, mk0, inferInstance⟩ := by
    rw [hψ1, hα]; rfl
  have hEq : (SpecToEquivOfLocalRing X A) (ψ ≫ p.fiberι s) =
      ⟨p.fiberι s z, mk0, inferInstance⟩ := by
    rw [hψ1']; exact Equiv.apply_symm_apply _ _
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hEq
  have hcp : ψ (IsLocalRing.closedPoint A) = z :=
    (p.fiberι s).isEmbedding.injective (by simpa [Scheme.Hom.comp_apply] using h₁)
  set θ : (p.fiber s).presheaf.stalk z ⟶ A :=
    ((p.fiber s).presheaf.stalkCongr (Inseparable.of_eq hcp.symm)).hom ≫
      Scheme.stalkClosedPointTo ψ with hθdef
  have h₁' : p.fiberι s (ψ (IsLocalRing.closedPoint A)) = p.fiberι s z := h₁
  have hstar : (p.fiberι s).stalkMap (ψ (IsLocalRing.closedPoint A)) ≫
      Scheme.stalkClosedPointTo ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h₁')).hom ≫ mk0 := by
    rw [← Scheme.stalkClosedPointTo_comp]
    exact h₂
  have hθ : (p.fiberι s).stalkMap z ≫ θ = mk0 := by
    rw [hθdef, Scheme.Hom.stalkMap_congr_point_assoc (p.fiberι s) z
      (ψ (IsLocalRing.closedPoint A)) hcp.symm, hstar]
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc,
      TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  have hker : RingHom.ker ((p.fiberι s).stalkMap z).hom ≤ fiberStalkIdeal p s z := by
    intro a ha
    have h0 : mk0.hom a = θ.hom (((p.fiberι s).stalkMap z).hom a) := by
      rw [← hθ]; rfl
    rw [RingHom.mem_ker] at ha
    rw [ha, map_zero] at h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
  refine ⟨RingEquiv.ofBijective (Ideal.Quotient.lift _ ((p.fiberι s).stalkMap z).hom
    (fun a ha => RingHom.mem_ker.mp (fiberStalkIdeal_le_ker p s z ha))) ⟨?_, ?_⟩, ?_⟩
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    simp only [Ideal.Quotient.lift_mk] at huv
    rw [Ideal.Quotient.eq]
    apply hker
    rw [RingHom.mem_ker, map_sub, huv, sub_self]
  · intro w
    obtain ⟨a, rfl⟩ := surjective_fiberι_stalkMap p s z w
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  · ext a
    rfl

/-- `exists_ringEquiv_stalk_fiber` with the point of `X` named separately, so
that a consumer does not have to reduce `fiberι z` to it. -/
theorem exists_ringEquiv_stalk_fiber' (x : X) (hz : p.fiberι s z = x) :
    ∃ e : (X.presheaf.stalk x ⧸
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (p x))).map (p.stalkMap x).hom) ≃+*
          ((p.fiber s).presheaf.stalk z),
      e.toRingHom.comp (Ideal.Quotient.mk _) =
        ((X.presheaf.stalkCongr (Inseparable.of_eq hz.symm)).hom ≫
          (p.fiberι s).stalkMap z).hom := by
  subst hz
  obtain ⟨e, he⟩ := exists_ringEquiv_stalk_fiber p s z
  refine ⟨e, ?_⟩
  rw [he]
  simp

end FiberStalk

/-- `fiberMapOver` commutes with the two embeddings of the fibres: this is
`pullback.lift_fst` for the map defining it. -/
theorem fiberMapOver_fiberι {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) :
    fiberMapOver u h s ≫ q.fiberι s = p.fiberι s ≫ u :=
  Limits.pullback.lift_fst _ _ _

/-- `fiberMapOver_fiberι` read on points. -/
theorem fiberι_fiberMapOver_apply {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) (w : p.fiber s) :
    q.fiberι s (fiberMapOver u h s w) = u (p.fiberι s w) := by
  rw [← Scheme.Hom.comp_apply, fiberMapOver_fiberι, Scheme.Hom.comp_apply]

/-- The stalk-level square attached to `fiberMapOver`, i.e. `fiberMapOver_fiberι`
after `Scheme.Hom.stalkMap`. -/
theorem stalkMap_fiberMapOver_square {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) (s : S) (w : p.fiber s) :
    (q.fiberι s).stalkMap (fiberMapOver u h s w) ≫ (fiberMapOver u h s).stalkMap w
      = (Y.presheaf.stalkCongr
          (Inseparable.of_eq (fiberι_fiberMapOver_apply u h s w))).hom ≫
        u.stalkMap (p.fiberι s w) ≫ (p.fiberι s).stalkMap w := by
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom _ _ (fiberMapOver_fiberι u h s) w]
  rfl

/-- **The stalk of the fibre is the quotient of the stalk, compatibly with
`u`** (PROVEN 2026-07-27 — general scheme theory, no abelian varieties: this
is the whole mathematical content of
`flat_quotientMap_of_flat_stalkMap_fiberMapOver` below, which is PROVEN over
it with no residue).

**HOW IT IS PROVEN, and the survey below that it CORRECTS.**  Everything the
old survey said about mathlib is still true — there is no stalk of a fibre and
no stalk of a pullback anywhere in the pin, and all four of its greps were
re-run empty on 2026-07-27.  What the survey got wrong was the inference:
*this leaf does not need stalk-of-pullback theory at all.*  The input it needs
is the universal property of `Spec` of a LOCAL ring,
`AlgebraicGeometry.SpecToEquivOfLocalRing` (`AlgebraicGeometry/Stalk.lean`),
which says morphisms `Spec R ⟶ X` out of a local ring are exactly a point of
`X` plus a local homomorphism on its stalk.

With that, `exists_ringEquiv_stalk_fiber` above does the whole job in three
moves: `Scheme.Hom.fiberι` is a PREIMMERSION, so it is surjective on stalks;
the pullback square puts `𝔪_s` in the kernel (`fiberStalkIdeal_le_ker`); and
the reverse inclusion comes from building `ψ : Spec (𝒪_{X,x}/𝔪_s𝒪_{X,x}) ⟶ X_s`
— which exists precisely because `𝔪_s` dies in that quotient — and reading
`Scheme.stalkClosedPointTo ψ` as a LEFT INVERSE of the surjection.  A left
inverse forces injectivity, so the surjection is an isomorphism.

The reusable moral, and the reason this is worth recording rather than just
deleting: an "absent from the pin" survey ranged over the wrong axis.  It
searched for the OBJECT (a stalk of a pullback) and concluded correctly that
mathlib has none; it never asked whether the object could be avoided by a
UNIVERSAL PROPERTY, which is where the pin was in fact rich.

Two canonical identifications
`𝒪_{Y,y} ⧸ 𝔪_s 𝒪_{Y,y} ≅ 𝒪_{Y_s, y_s}` and
`𝒪_{X_s, x_s} ≅ 𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}`, and the square saying they carry the
stalk map of `fiberMapOver u rfl s` to `Ideal.quotientMap`.

**Why the two equivalences point in OPPOSITE directions.**  A `RingEquiv` in
either direction is the same data, and these two are chosen so that the
square composes with no `.symm` anywhere: the conclusion is literally
`quotientMap = eX ∘ stalkMap ∘ eY`.  That is not cosmetic — the `.symm` form
of the same statement cost a full verify cycle in coercion bookkeeping
(`RingEquiv.toRingHom` vs the `RingEquiv` coercion do not simp into each
other inside `RingHom.comp`), and this form makes the consumer a two-line
application of `RingHom.Flat.comp` and `RingHom.Flat.of_bijective`.

**The point-equality obligation flagged below never had to be paid.**  The
general lemma `exists_ringEquiv_stalk_fiber'` is stated for an ARBITRARY point
`z` of the fibre together with a hypothesis `p.fiberι s z = x`, so it applies
directly at `fiberMapOver u rfl s ((u ≫ q).asFiber x)` and the identification
of that point with `q.asFiber (u x)` is simply never needed.  The note below
is kept because its warning is still correct for anyone who states the leaf
the other way round.

**Why the point of `q.fiber s` is written
`fiberMapOver u rfl s ((u ≫ q).asFiber x)` and not `q.asFiber (u x)`.**
Those two points ARE equal — both lie over `u x` and `q.fiberι` is injective
(`Scheme.Hom.fiberHomeo`) — but proving it is a separate obligation, and
`stalkMap` forces the former.  Writing the former keeps this leaf free of
that obligation; a prover who wants the latter should prove the point
equality first and transport.  The statement is faithful either way: the
point named does lie over `u x`, since
`fiberι ≫ fiberMapOver = u ≫ fiberι`.

**A SIMPLIFICATION the old note missed.**  The old text justified "the
further localization is trivial" by `Scheme.Hom.fiberι` being injective on
points.  That is true but is not the reason, and the real reason is much
cheaper: `𝔪_s·𝒪_{X,x} ⊆ 𝔪_x` because `p.stalkMap x` is a LOCAL homomorphism,
so `𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}` is already a local ring and localizing it at its
own maximal ideal does nothing.  No point-set input is needed.

Concretely: `𝒪_{X_s, x_s} = 𝒪_{X,x} ⧸ 𝔪_s 𝒪_{X,x}` and
`𝒪_{Y_s, y_s} = 𝒪_{Y,y} ⧸ 𝔪_s 𝒪_{Y,y}`, compatibly with `u`, so flatness of
the stalk map of `fiberMapOver u h s` at `p.asFiber x` IS flatness of
`𝒪_{Y,y}/𝔪_s 𝒪_{Y,y} → 𝒪_{X,x}/𝔪_s 𝒪_{X,x}`.  The statement is phrased as
that flatness rather than as the isomorphism, so that it plugs straight into
hypothesis (5) of `flat_of_flat_of_flat_quotientMap`.

**Why it is true, and why the special feature matters.**  For a general
fibre product the local ring at a point is a *localization* of a tensor
product of local rings, not the tensor product itself.  Here it is on the
nose, because `Scheme.Hom.fiberι` is injective on points (it is a
homeomorphism onto `p ⁻¹' {s}` — `Scheme.Hom.fiberHomeo`), so the prime of
`𝒪_{X,x} ⊗_{𝒪_{S,s}} κ(s)` corresponding to `x_s` is already its unique
maximal ideal and the further localization is trivial.  Concretely on
affines, with `𝔭 ↔ x` and `𝔯 ↔ s` and `𝔭 ∩ R = 𝔯`, both sides are
`(A/𝔯A)_𝔭`.

**STILL ABSENT from the pin, with the refuting greps** (re-run 2026-07-27,
all still empty — but see the correction at the top: their absence turned out
not to matter):
`grep -n stalk Mathlib/AlgebraicGeometry/Fiber.lean` and the same over
`PullbackCarrier.lean` and `Pullbacks.lean` each return NOTHING, and
`grep -rn "stalkMap_pullback\|pullback_stalk" Mathlib/` is empty.  Mathlib
computes the **residue field** of a point of a fibre product
(`PullbackCarrier.Triplet.tensor`) and the **sections** of one
(the `pushoutSection` block, `Morphisms/Flat.lean:183–509`), but never the
stalk.

**FAITHFULNESS — the intermediate map is PINNED, deliberately.**  An earlier
draft of this leaf took the map `𝒪_{S,s} ⟶ 𝒪_{Y,y}` as an arbitrary
parameter `g` with `g ≫ u.stalkMap x = p.stalkMap x`.  That is **not safe**:
`u.stalkMap x` need not be injective, so `g` is not determined by that
equation, while the conclusion depends on `g` through the ideal `𝔪_s·𝒪_{Y,y}`
— i.e. the leaf would have quantified over data the statement is not
invariant under, and could have been FALSE.  It is therefore stated in the
substituted form `p = u ≫ q`, with the map fixed to `q.stalkMap (u x)`; the
consumer reaches it by `subst h`, which costs nothing. -/
theorem exists_ringEquiv_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {q : Y ⟶ S} (u : X ⟶ Y) (x : X) :
    ∃ (eY : (Y.presheaf.stalk (u x) ⧸
              (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                (q.stalkMap (u x)).hom) ≃+*
            ((q.fiber ((u ≫ q) x)).presheaf.stalk
              (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))))
      (eX : (((u ≫ q).fiber ((u ≫ q) x)).presheaf.stalk ((u ≫ q).asFiber x)) ≃+*
            (X.presheaf.stalk x ⧸
              (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))),
      Ideal.quotientMap
          ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
            ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))
          (u.stalkMap x).hom
          (map_le_comap_map_comp (q.stalkMap (u x)).hom (u.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))))
        = eX.toRingHom.comp
            (((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom.comp
              eY.toRingHom)
    := by
  have hzx : (u ≫ q).fiberι ((u ≫ q) x) ((u ≫ q).asFiber x) = x :=
    Scheme.Hom.fiberι_asFiber (u ≫ q) x
  have hzy : q.fiberι ((u ≫ q) x)
      (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)) = u x := by
    rw [fiberι_fiberMapOver_apply, hzx]
  have hcomp : ((u ≫ q).stalkMap x).hom
      = (u.stalkMap x).hom.comp (q.stalkMap (u x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  obtain ⟨ep, hep⟩ :=
    exists_ringEquiv_stalk_fiber' (u ≫ q) ((u ≫ q) x) ((u ≫ q).asFiber x) x hzx
  obtain ⟨eq0, heq0⟩ :=
    exists_ringEquiv_stalk_fiber' q ((u ≫ q) x)
      (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)) (u x) hzy
  have hI : (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
        ((u ≫ q).stalkMap x).hom
      = (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
        ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom) :=
    congrArg (fun f => Ideal.map f (IsLocalRing.maximalIdeal
      (S.presheaf.stalk ((u ≫ q) x)))) hcomp
  have hSQ : u.stalkMap x ≫ ((X.presheaf.stalkCongr (Inseparable.of_eq hzx.symm)).hom ≫
        ((u ≫ q).fiberι ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x))
      = ((Y.presheaf.stalkCongr (Inseparable.of_eq hzy.symm)).hom ≫
          (q.fiberι ((u ≫ q) x)).stalkMap
            (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))) ≫
        (fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x) := by
    rw [Category.assoc, Scheme.Hom.stalkMap_congr_point_assoc u x
      ((u ≫ q).fiberι ((u ≫ q) x) ((u ≫ q).asFiber x)) hzx.symm,
      stalkMap_fiberMapOver_square u rfl ((u ≫ q) x) ((u ≫ q).asFiber x)]
    simp only [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_comp_assoc]
  refine ⟨eq0, ep.symm.trans (Ideal.quotEquivOfEq hI), ?_⟩
  refine RingHom.ext fun w => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hY : eq0 (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          (q.stalkMap (u x)).hom) b)
      = ((Y.presheaf.stalkCongr (Inseparable.of_eq hzy.symm)).hom ≫
          (q.fiberι ((u ≫ q) x)).stalkMap
            (fiberMapOver u rfl ((u ≫ q) x) ((u ≫ q).asFiber x))).hom b :=
    DFunLike.congr_fun heq0 b
  have hX : ep (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u ≫ q).stalkMap x).hom) ((u.stalkMap x).hom b))
      = ((X.presheaf.stalkCongr (Inseparable.of_eq hzx.symm)).hom ≫
          ((u ≫ q).fiberι ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
            ((u.stalkMap x).hom b) :=
    DFunLike.congr_fun hep ((u.stalkMap x).hom b)
  have hsq' := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hSQ) b
  have key : ep (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u ≫ q).stalkMap x).hom) ((u.stalkMap x).hom b))
      = ((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
          (eq0 (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
              (q.stalkMap (u x)).hom) b)) := by
    rw [hX, hY]
    exact hsq'
  rw [Ideal.quotientMap_mk]
  show Ideal.Quotient.mk _ ((u.stalkMap x).hom b)
      = (ep.symm.trans (Ideal.quotEquivOfEq hI))
          (((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom
            (eq0 (Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
                (q.stalkMap (u x)).hom) b)))
  rw [RingEquiv.trans_apply, ← key, RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]

/-- **The stalk of the fibre is the base change of the stalk**, in the
flatness form the fibre criterion consumes (PROVEN 2026-07-27 over
`exists_ringEquiv_stalkMap_fiberMapOver` above, with NO residue — the whole
of what remains open is that one statement).

The statement is phrased as this flatness rather than as the isomorphism, so
that it plugs straight into hypothesis (5) of
`flat_of_flat_of_flat_quotientMap`; the isomorphism itself is the leaf above.

**What this cut buys.**  All the commutative-algebra bookkeeping —
`Ideal.quotientMap`, the ideal inclusion `map_le_comap_map_comp`, and the
transport of `RingHom.Flat` across the two identifications — is discharged
here by `RingHom.Flat.comp` and `RingHom.Flat.of_bijective`, so what remains
open is a statement of pure scheme theory that mentions flatness nowhere.
It is also strictly more reusable than the flatness form: any property of
ring maps that respects isomorphisms transports across the same square.

**FAITHFULNESS — the intermediate map is PINNED, deliberately**, exactly as
recorded on the leaf above: `p` is substituted as `u ≫ q` and the map
`𝒪_{S,s} ⟶ 𝒪_{Y,y}` is fixed to `q.stalkMap (u x)` rather than quantified
over, because `u.stalkMap x` need not be injective and the conclusion
depends on that map through the ideal `𝔪_s·𝒪_{Y,y}`. -/
theorem flat_quotientMap_of_flat_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {q : Y ⟶ S} (u : X ⟶ Y) (x : X)
    (hfib : ((fiberMapOver u rfl ((u ≫ q) x)).stalkMap ((u ≫ q).asFiber x)).hom.Flat) :
    (Ideal.quotientMap
        ((IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))).map
          ((u.stalkMap x).hom.comp (q.stalkMap (u x)).hom))
        (u.stalkMap x).hom
        (map_le_comap_map_comp (q.stalkMap (u x)).hom (u.stalkMap x).hom
          (IsLocalRing.maximalIdeal (S.presheaf.stalk ((u ≫ q) x))))).Flat := by
  obtain ⟨eY, eX, heq⟩ := exists_ringEquiv_stalkMap_fiberMapOver (q := q) u x
  rw [heq]
  exact RingHom.Flat.comp
    (RingHom.Flat.comp (RingHom.Flat.of_bijective eY.bijective) hfib)
    (RingHom.Flat.of_bijective eX.bijective)

/-- **The fibrewise criterion of flatness, AT A POINT** (PROVEN 2026-07-27
over the three leaves above —
general scheme theory, NO abelian varieties: Stacks 039C = Stacks Theorem
37.16.2, of which the global `flat_of_flat_fiberMap` below is the
specialization Stacks 039E; EGA IV 11.3.10, *critère de platitude par
fibres*).

`Flat` of a morphism is exactly flatness of every stalk map
(`AlgebraicGeometry.Flat.iff_flat_stalkMap`), so this is the statement the
global one reduces to, and it is the form in which the literature actually
proves it.  Fix `x : X`, put `s = p x` and `y = u x`.  Given that `X` is
flat over `S` at `x` and that the fibre morphism `X_s ⟶ Y_s` is flat at
`x`, conclude that `u` is flat at `x`.

**FAITHFULNESS — this is Stacks 039C verbatim, with hypotheses CHECKED
against the source on 2026-07-27** (not reconstructed from memory).  039C
reads: *`X` locally of finite presentation over `S`; `F` an `O_X`-module
of finite presentation; `Y` locally of finite type over `S`.  Let
`x ∈ X`, `y = f x`, `s` the image in `S`.  If `F_x ≠ 0` then (1) `F` flat
over `S` at `x` and `F_s` flat over `Y_s` at `x`, is equivalent to (2) `Y`
flat over `S` at `y` and `F` flat over `Y` at `x`.*  Instantiate
`F = O_X` (finitely presented as a module over itself, and `O_{X,x} ≠ 0`
because a stalk of a scheme is a local ring, hence nontrivial) and take
the direction (1) ⟹ (2), keeping only the second half of (2).  So:

* `hp` is "`F` flat over `S` at `x`";
* `hfib` is "`F_s` flat over `Y_s` at `x`" — the fibre `p.fiber (p x)` is
  `X_s`, `Scheme.Hom.asFiber` is the canonical point of it above `x`, and
  `fiberMapOver` is `f_s`;
* the conclusion is "`F` flat over `Y` at `x`".

Two hypotheses of the CONSUMER are deliberately **not** taken here,
because 039C does not use them: `Flat q` (039C *produces* flatness of `Y`
over `S` at `y` — it is the discarded first half of (2)), and
`LocallyOfFinitePresentation u`.  `LocallyOfFiniteType q` is what 039C
asks for and is weaker than the consumer's
`LocallyOfFinitePresentation q`; mathlib supplies the instance, so the
consumer still applies.  This leaf is therefore strictly STRONGER than
what `flat_of_flat_fiberMap` needs, and correspondingly reusable.

**HOW IT IS PROVEN, and the TWO STALE CLAIMS this replaces.**  The proof
is `subst h`, then `flat_of_flat_of_flat_quotientMap` — Stacks 05UV over
abstract local rings — fed by the three transports declared above:
`essFinitePresentation_stalkMap` for hypothesis (1),
`LocallyOfFiniteType.stalkMap` (mathlib, FREE) for hypothesis (2), `hp`
for hypothesis (6), and `flat_quotientMap_of_flat_stalkMap_fiberMapOver`
for hypothesis (5).  `subst h` is what lets `p.stalkMap x` factor as
`q.stalkMap (u x) ≫ u.stalkMap x` by `Scheme.Hom.stalkMap_comp` with no
`eqToHom` anywhere.

The previous version of this docstring recorded two reasons the leaf could
NOT be cut further.  **Both were wrong, and both are the same error** —
treating a missing *definition* as a missing *theory*:

1. *"Essentially of finite presentation does not exist, so the honest
   ring-level statement cannot be written down."*  It is a five-line
   definition (`EssFinitePresentation` above), and writing it is what makes
   the cut possible.  Nothing about it has to be *proven* for the cut; the
   proof obligations land on the named leaves instead.
2. *"The natural seam — the stalk of the fibre — is not available, so the
   local algebra cannot even be stated over plain rings."*  The seam does
   not need mathlib's stalk-of-pullback theory to be *stated*; it needs it
   to be *proven*, and that obligation is now
   `flat_quotientMap_of_flat_stalkMap_fiberMapOver`, isolated from the
   commutative algebra it was entangled with.

The old note's positive content survives and has been moved to the leaf it
actually describes: the Tor / local-criterion / spreading-out survey is on
`flat_of_flat_of_flat_quotientMap`, and the stalk-of-pullback survey is on
`flat_quotientMap_of_flat_stalkMap_fiberMapOver`.

**STATUS of the three leaves, 2026-07-27 (updated).**  Two of the three are
closed OUTRIGHT, and the third is the only thing left in this whole cut:

* `essFinitePresentation_stalkMap` — **PROVEN**, and its docstring records
  that `stableUnderComposition` for `EssFinitePresentation` turned out not to
  be needed at all.
* `flat_quotientMap_of_flat_stalkMap_fiberMapOver` — **PROVEN**, and now
  axiom-clean all the way down: its one-time leaf
  `exists_ringEquiv_stalkMap_fiberMapOver` is itself **PROVEN**, over the
  general `exists_ringEquiv_stalk_fiber` (the stalk of a scheme-theoretic
  fibre is the stalk modulo `𝔪_s`).  That closes the entire scheme-theoretic
  half of the fibre criterion.
* `flat_of_flat_of_flat_quotientMap` — still open, and now the SOLE remaining
  input of `flat_of_flat_fiberMap`.  It is pure commutative algebra; nothing
  above it mentions schemes any more.

An earlier version of this paragraph carried a "correction" claiming that
mathlib's `Module.free_of_maximalIdeal_rTensor_injective` narrows the gap to
"exactly the step from *finitely* to *essentially* finitely presented".
**That claim is false and has been retracted**; the refutation, which is a
one-line read of the mathlib statement (its hypothesis is finite presentation
of a MODULE, whereas this leaf has essential finite presentation of a ring
HOMOMORPHISM — incomparable notions), is written out in full on
`flat_of_flat_of_flat_quotientMap` itself, together with the axis that audit
searched and the one it did not.

**Route note that remains true and load-bearing**: `S` is an ARBITRARY
scheme, so the Noetherian engine 00MP does not reach this statement.  05UV
is the non-Noetherian local-ring form and is what the cut uses; a plan that
stops at 00MP is still incomplete. -/
theorem flat_stalkMap_of_flat_stalkMap_fiberMapOver
    {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p)
    [LocallyOfFinitePresentation p] [LocallyOfFiniteType q]
    (x : X)
    (hp : (p.stalkMap x).hom.Flat)
    (hfib : ((fiberMapOver u h (p x)).stalkMap (p.asFiber x)).hom.Flat) :
    (u.stalkMap x).hom.Flat := by
  subst h
  have hcomp : (u.stalkMap x).hom.comp (q.stalkMap (u x)).hom = ((u ≫ q).stalkMap x).hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    rfl
  have := q.prop (u x)
  exact flat_of_flat_of_flat_quotientMap (g := (q.stalkMap (u x)).hom)
    (v := (u.stalkMap x).hom)
    (hcomp ▸ essFinitePresentation_stalkMap (u ≫ q) x)
    (LocallyOfFiniteType.stalkMap (f := q) (u x)) (hcomp ▸ hp)
    (flat_quotientMap_of_flat_stalkMap_fiberMapOver u x hfib)

/-! ### The four inputs of miracle flatness

`flat_of_finite_fibres_endo` below is PROVEN over the four leaves in this
block.  The cut is at the stalks: `AlgebraicGeometry.Flat.of_stalkMap` turns
`Flat u` into a statement about each local homomorphism
`𝒪_{X,u x} ⟶ 𝒪_{X,x}`, and Matsumura 23.1 is exactly a criterion for such a
homomorphism to be flat.  Three of the four leaves are geometry (they say what
`u` and `X` do to stalks) and one is pure commutative algebra.

**What the glue itself contributes, and it is not nothing**: the hypothesis
`IsProper u` together with finite fibres is upgraded ONCE, here, to
`IsFinite u` — via `LocallyQuasiFinite.of_finite_preimage_singleton` and
Zariski's main theorem in mathlib's form
`IsFinite.of_isProper_of_locallyQuasiFinite`.  Every geometric leaf below is
therefore stated with `[IsFinite u]`, which is far more usable than "proper
with finite fibres", and no leaf has to redo that step.

**STATUS OF THE FOUR, 2026-07-27 (updated).**

* `isRegularLocalRing_stalk_of_smooth` — **PROVEN 2026-07-27**, in one line
  over the hoisted `isRegularLocalRing_stalk_of_smooth_over_field`, once the
  bundled-`K` instance defect in its own signature was repaired (see its
  docstring).  It was never mathematics: it was a HOIST and then a BINDER.
  The binder is now `{K : Type u} [Field K]` with base
  `Spec (CommRingCat.of K)` here, in `ringKrullDim_stalk_eq_of_isFinite_endo`,
  in `flat_of_finite_fibres_endo` and in `flat_mulByNat_of_field`.  It also
  unblocks `exists_isWeaklyRegular_span_eq_maximalIdeal` below.
* `ringKrullDim_quotient_map_maximalIdeal_stalkMap` — **PROVEN**, over the new
  ring-level lemma `ringKrullDim_quotient_of_quasiFinite`.  The hand-written
  affine descent the survey called for turned out to be already in mathlib as
  `Scheme.Hom.quasiFiniteAt`.
* `ringKrullDim_stalk_eq_of_isFinite_endo` — **PROVEN 2026-07-27** over ONE new
  leaf, `hasGoingDown_stalkMap_of_isFinite_endo`.  It does NOT need
  `dim 𝒪_{X,x} + dim closure{x} = dim X`, and no scheme dimension theory is
  used: both sides are heights of maximal ideals, the `≤` is Stacks 00OM and
  the fibre-dimension leaf, and the `≥` is Stacks 00ON given going-down.  The
  remaining leaf's own irreducible content is **a regular local ring is
  integrally closed** (regular ⟹ normal), absent from mathlib, this project
  and `~/cs/FLT`.
* `flat_of_isRegularLocalRing_of_ringKrullDim_eq` — **PROVEN over three new
  sub-leaves** (`exists_isWeaklyRegular_span_eq_maximalIdeal`,
  `isWeaklyRegular_map_of_ringKrullDim_eq`,
  `flat_of_isWeaklyRegular_span_eq_maximalIdeal`).  Its docstring also corrects
  the previously recorded "`Tor`-free affine route", which is a route to a
  DIFFERENT (module-finite) theorem and not to that leaf. -/

/-- **SMOOTH OVER A FIELD ⟹ THE STALKS ARE REGULAR LOCAL RINGS**
(**PROVEN 2026-07-27**, in one line.  It was previously a sorry leaf and it was
FALSE AS STATED — the FALSITY AUDIT below is kept as the record of why, since
the same defect has been reintroduced into this file twice after being
repaired.  Nothing was proven to close it: the mathematics had already been
hoisted, and the signature was then repaired across the whole family.)

**THE HOIST THIS LEAF ASKED FOR IS DONE (2026-07-27).**  The earlier version
of this docstring said the proof —
`GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
— was unreachable because it lived in `Modularity/KhareWintenberger.lean`,
strictly DOWNSTREAM of this module.  It has been HOISTED, with its entire
nine-declaration dependency cone, into `Fermat/FLT/Modularity/RegularStalks.lean`,
which this file now `public import`s (see the import block) and which
`KhareWintenberger.lean` imports in turn.  Nothing was restated or reproved:
the declarations moved byte-identically, in the same namespace, and all nine
are sorry-free.  So there is NO open mathematics under this leaf anywhere in
the tree, and the `public import` above is what this proof consumes.

**FALSITY AUDIT (2026-07-27) — the defect this signature USED TO HAVE, kept
because the same trap is one keystroke away in any file that handles a
`CommRingCat` and a field together.**  The statement used to bind
`{K : CommRingCat.{u}} [Field K]` with `(g : X ⟶ Spec K)`.  That hypothesis
does not say what
it looks like it says.  `K : CommRingCat` is a BUNDLED object, carrying its own
ring structure `K.str`; `Spec K` is built from `K.str`.  But `[Field K]`
elaborates to `Field ↥K` — a class on the CARRIER TYPE — and its `CommRing`
is `Field.toCommRing`, which is a DIFFERENT instance.  Lean says so itself:
attempting to close this leaf from the hoisted theorem produces

    X ⟶ Spec (@CommRingCat.of ↑K CommRingCat.instCommRingObjForgetRingHomCarrier)
    X ⟶ Spec (@CommRingCat.of ↑K Field.toCommRing)

as two non-unifiable types.  They are not a defeq nuisance; they are two
genuinely different schemes, because nothing ties the two ring structures
together.  `[Field K]` therefore asserts only that the carrier TYPE of `K`
happens to admit SOME field structure, which constrains `K.str` not at all.

**THE REPAIR, NOW MADE (2026-07-27).**  The signature is
`{K : Type u} [Field K]` with base `Spec (CommRingCat.of K)`, so that the
field structure of the hypothesis IS the ring structure of the base scheme.
Under it this leaf closes in the one line the audit predicted.  The repair was
threaded through the four declarations of the sub-cluster that share the binder
and pass `K` to one another — this leaf,
`ringKrullDim_stalk_eq_of_isFinite_endo`, `flat_of_finite_fibres_endo` and
`flat_mulByNat_of_field` — and it TERMINATES at `flat_fiberMap_mulByNat`, whose
`K` is `S.residueField s`, *defined* as
`CommRingCat.of (IsLocalRing.ResidueField _)`, so the unbundled form is
discharged there by `rfl`.  No proof body outside those four changed.

The OTHER cluster diagnosed by the FALSITY AUDIT on
`nonempty_module_infKernel_of_squareZero` below — that leaf,
`eq_zero_of_nsmul_eq_zero_of_squareZero`, `formallyUnramified_mulByNat`,
`finite_preimage_mulByNat_of_field_prime_to_char` and
`finite_preimage_mulByNat_of_field` — is UNTOUCHED and still needs its own
owner.  The two clusters meet only at
`flat_mulByNat_of_field`'s call of `finite_preimage_mulByNat_of_field`, which
survives the repair because the bundled statement instantiates at
`CommRingCat.of K` for a genuine field `K`.

THE COUNTEREXAMPLE.  Take `K := CommRingCat.of (ZMod 4)`, so `↥K = ZMod 4`, a
four-element type.  A `Field ↥K` instance exists — transport the field
structure of `GaloisField 2 2` along any bijection `ZMod 4 ≃ GaloisField 2 2`
— so the hypothesis `[Field K]` is satisfied while `K.str` is the ordinary
`ZMod 4`.  Take `X := Spec K` and `g := 𝟙`, which is smooth.  `ZMod 4` is
local with maximal ideal `(2)`, so the stalk at the unique point is `ZMod 4`
itself, which is not even a domain — and a regular local ring IS a domain
(`GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`, PROVEN in
`KhareWintenberger.lean`).  So the conclusion fails.

**THE REPAIR IS DONE, AND THIS LEAF IS CLOSED (2026-07-27).**  The binder is
now `{K : Type u} [Field K]` with base `Spec (CommRingCat.of K)` — the idiom
`Modularity/AbelianScheme.lean` uses everywhere and the one mathlib uses.
Under that signature the theorem is the ONE-LINE citation written below, with
no mathematics left to do.  **Everything above this paragraph is a record of
the defect, not a live warning**: the counterexample no longer applies, because
`[Field K]` now constrains the very ring `Spec (CommRingCat.of K)` is built
from.

The conversion was made across the WHOLE family in ONE commit, because a file
mixing the two conventions is worse than one with the bug throughout: with a
bundled `K` and a local `[Field ↥K]` both in scope, instance search for
`CommRing ↥K` is ambiguous at every boundary between the styles.  The fourteen
declarations converted together were `isRegularLocalRing_stalk_of_smooth`,
`ringKrullDim_stalk_eq_of_isFinite_endo`, `flat_of_finite_fibres_endo`,
`nonempty_module_infKernel_of_squareZero`,
`eq_zero_of_nsmul_eq_zero_of_squareZero`, `formallyUnramified_mulByNat`,
`finite_preimage_mulByNat_of_field_prime_to_char`,
`isQuasiAffine_ker_mulByNat_of_field_char`,
`isAffine_ker_mulByNat_of_field_char`, `finite_ker_mulByNat_of_field_char`,
`isFinite_ker_mulByNat_of_field_char`, `finite_preimage_mulByNat_of_field_char`,
`finite_preimage_mulByNat_of_field` and `flat_mulByNat_of_field`.  No proof
body changed.  The recursion terminates at the two consumers that instantiate
at a residue field (`finite_preimage_mulByNat`, `flat_fiberMap_mulByNat`),
which now pass `↥(S.residueField _)`: `Scheme.residueField` is *defined* as
`CommRingCat.of _`, so the pin is discharged by `rfl`.

**IF YOU OPEN A NEW DECLARATION IN THIS FAMILY, USE THE CONVERTED SHAPE.**  The
defect was found three times in this file — repaired across eleven
declarations, reintroduced in a declaration opened after that repair, then
found again in a third cluster.  Reintroducing the bundled binder anywhere
re-creates the ambiguity for everyone.

**ONE CLAIM OF THAT AUDIT WAS WRONG, AND IT IS CORRECTED HERE (2026-07-27).**
The audit closed by saying "the same counterexample refutes the sibling
`ringKrullDim_stalk_eq_of_isFinite_endo` below".  It does not.  In that
counterexample `X = Spec K` is a ONE-POINT scheme, so its only endomorphism is
`𝟙` and the sibling's conclusion
`dim 𝒪_{X,x} = dim 𝒪_{X,u x}` is `dim 𝒪_{X,x} = dim 𝒪_{X,x}`, which is true.
The defect is real in both leaves — with `K.str` unconstrained the smoothness
hypothesis carries no regularity and neither leaf is provable — but a leaf
whose conclusion is an EQUATION BETWEEN TWO INSTANCES OF THE SAME QUANTITY is
not refuted by a counterexample that collapses them.  This matters because a
recorded refutation is what stops the next owner from attempting a proof: it
must name a counterexample that actually falsifies the CONCLUSION, not merely
one that voids the hypotheses. -/
theorem isRegularLocalRing_stalk_of_smooth {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  _root_.GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field
    g ‹Smooth g› x

/-- **THE FIBRE OF A QUASI-FINITE ALGEBRA OVER A LOCAL RING IS ZERO-DIMENSIONAL**
(PROVEN 2026-07-27 — the ring-level core of
`ringKrullDim_quotient_map_maximalIdeal_stalkMap` below).

For `R` local and `T` a quasi-finite `R`-algebra whose fibre ring `T ⧸ 𝔪_R T` is
nonzero, that fibre ring has Krull dimension `0`.

The whole content is that `Algebra.QuasiFinite` is *by definition*
`Module.Finite κ(p) (p.Fiber T)` at every prime `p` of the BASE — so at
`p = 𝔪_R` it says exactly that the fibre is a finite-dimensional algebra over the
residue field, hence artinian.  Mathlib already carries that instance
(`IsArtinianRing (p.Fiber T)`); all this proof does is transport it along the
standard identification `κ(𝔪) ⊗[R] T ≃ₐ T ⧸ 𝔪T` and convert `Ring.KrullDimLE 0`
into `ringKrullDim = 0`, which needs the nontriviality hypothesis `hne`.

**This is where the module-finiteness trap is dodged**, and it is worth saying
how, because the warning on the geometric statement below is real: nothing here
asks `T` to be a finite `R`-MODULE.  `Algebra.QuasiFinite` is a condition on
FIBRES, and it is stable under localisation of the base in exactly the way
module-finiteness is not. -/
theorem ringKrullDim_quotient_of_quasiFinite (R T : Type u) [CommRing R] [CommRing T]
    [IsLocalRing R] [Algebra R T] [Algebra.QuasiFinite R T]
    (hne : Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R) ≠ ⊤) :
    ringKrullDim (T ⧸ Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R)) = 0 := by
  have _ : Nontrivial (T ⧸ Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  -- `κ(𝔪_R) ⊗[R] T ≃ₐ[R] T ⧸ 𝔪_R T`, the identification used in mathlib's own
  -- `Algebra.QuasiFinite.finite_of_isArtinianRing_of_isLocalRing`.
  let e : (IsLocalRing.maximalIdeal R).Fiber T ≃ₐ[R]
      T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField
        (IsLocalRing.maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot T
      (IsLocalRing.maximalIdeal R)).symm.restrictScalars _)
  have _ : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber T) := e.toEquiv.nontrivial
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    ← ringKrullDimZero_iff_ringKrullDim_eq_zero]
  infer_instance

/-- **THE FIBRE RING OF A FINITE MORPHISM AT A POINT IS ZERO-DIMENSIONAL**
(**PROVEN 2026-07-27**, over `ringKrullDim_quotient_of_quasiFinite` above —
general scheme theory, NO abelian varieties, no smoothness, no field; true for an
arbitrary finite morphism of schemes).

`𝒪_{X,x} ⧸ 𝔪_{u x} 𝒪_{X,x}` is the local ring at `x` of the scheme-theoretic
fibre `u ⁻¹ (u x)`.  For `u` finite that fibre is `Spec` of a finite
`κ(u x)`-algebra, hence artinian, hence zero-dimensional; and localising an
artinian ring keeps it artinian.  This is the hypothesis `dim M/𝔪M = 0` of
Matsumura 23.1, which is what collapses the general dimension identity
`dim M = dim A + dim M/𝔪M` to the equality supplied by
`ringKrullDim_stalk_eq_of_isFinite_endo`.

The quotient is NONTRIVIAL, so `0` is the right value and not `⊥`: the stalk
map of a morphism of schemes is a LOCAL homomorphism
(`AlgebraicGeometry.Scheme.instIsLocalHomStalkMap`), so
`𝔪_{u x} 𝒪_{X,x} ⊆ 𝔪_x ≠ ⊤`.

**ROUTE AS PLANNED, AND THE MUCH SHORTER ONE ACTUALLY TAKEN** (2026-07-27).  The
survey below proposed descending to an affine cover by hand: choose affine
`V ∋ u x`, use that `u` finite is affine so `U = u ⁻¹ᵁ V` is affine and
`B = Γ(U)` is a finite `A = Γ(V)`-module, identify the stalks with `B_q` and
`A_p` through `IsAffineOpen.isLocalization_stalk`, and localise LAST.  That
route is correct and it is also unnecessary: **mathlib has already done exactly
this descent, once, and packaged it as `Scheme.Hom.quasiFiniteAt`.**

    Scheme.Hom.quasiFiniteAt (f) [LocallyQuasiFinite f] (x) : f.QuasiFiniteAt x

i.e. `(u.stalkMap x).hom.QuasiFinite`, and `[IsFinite u]` supplies
`LocallyQuasiFinite u` by a low-priority instance.  Unfolding
`RingHom.QuasiFinite` through `RingHom.quasiFinite_algebraMap` gives
`Algebra.QuasiFinite 𝒪_{Y,ux} 𝒪_{X,x}`, whose field `finite_fiber` at the prime
`𝔪_{ux}` is *verbatim* the "finite `κ(u x)`-algebra" the survey wanted.  From
there `ringKrullDim_quotient_of_quasiFinite` above finishes it.  Total: eleven
lines, and no affine cover is ever mentioned.

The check that would have found this earlier, and it is the one to copy: the
survey's own sentence "`B ⧸ pB` is a finite `κ(p)`-algebra" IS the definition of
a mathlib class (`Algebra.QuasiFinite`, `RingTheory/QuasiFinite/Basic.lean`).
When a route note describes a property in words, grep for a class that has that
property as its DEFINING field before writing the descent by hand.

The quotient is NONTRIVIAL — needed because `ringKrullDim ⊥ = ⊥ ≠ 0` — by
`IsLocalRing.map_maximalIdeal_lt_top`, which needs only that the stalk map is a
LOCAL homomorphism (`AlgebraicGeometry.Scheme.instIsLocalHomStalkMap`).

**A WARNING, STILL LIVE AFTER THE PROOF, because it is the trap that decided
the shape of `flat_of_isRegularLocalRing_of_ringKrullDim_eq` below.**  Do NOT
try to prove this by showing the stalk map is module-finite and quoting a
finiteness argument at the level of stalks: **THE STALK MAP OF A FINITE
MORPHISM IS NOT MODULE-FINITE.**  Counterexample: `u : Spec ℤ[i] ⟶ Spec ℤ` is
finite; take `p = (5)`, which splits, and `q` one of the two primes above it.
Then `A_p = ℤ_(5)` and `B_q` is a DVR with fraction field `ℚ(i)`.  If `B_q`
were a finite `A_p`-module it would be integral over `A_p`, hence contained in
the integral closure `ℤ[i]_(5) = B_p`; but `B_q ⊋ B_p`, since it inverts the
elements of the OTHER prime above `5`.  So `B_q` is not finite over `A_p`.
Finiteness survives only BEFORE localising at `q`.

The proof below respects that: `Algebra.QuasiFinite` is a condition on FIBRES,
not a module-finiteness condition, and it is precisely the property that DOES
survive localisation of the base.  Nowhere does the proof claim
`Module.Finite 𝒪_{Y,ux} 𝒪_{X,x}`, which is false. -/
theorem ringKrullDim_quotient_map_maximalIdeal_stalkMap {X Y : Scheme.{u}}
    (u : X ⟶ Y) [IsFinite u] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      Ideal.map (u.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (u x)))) = 0 := by
  letI : Algebra (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) := (u.stalkMap x).hom.toAlgebra
  have halg : algebraMap (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) = (u.stalkMap x).hom := rfl
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (u x)) (X.presheaf.stalk x) :=
    RingHom.quasiFinite_algebraMap.mp (halg ▸ u.quasiFiniteAt x)
  rw [← halg]
  refine ringKrullDim_quotient_of_quasiFinite _ _ ?_
  refine ne_of_lt ?_
  rw [halg]
  exact IsLocalRing.map_maximalIdeal_lt_top _

/-- **A LOCAL HOMOMORPHISM WITH A ZERO-DIMENSIONAL FIBRE AND GOING-DOWN
PRESERVES THE KRULL DIMENSION** (**PROVEN 2026-07-27** — pure commutative
algebra, Matsumura 13.B Th. 19(2); this is the ring-level core of
`ringKrullDim_stalk_eq_of_isFinite_endo` below).

For `A → B` a homomorphism of Noetherian local rings with `𝔪_B` lying over
`𝔪_A`, satisfying going-down, and whose fibre `B ⧸ 𝔪_A B` is zero-dimensional,
`dim B = dim A`.

Both halves come from mathlib's height comparison across a `LiesOver` pair:
the `≤` is Stacks 00OM (`Ideal.height_le_height_add_of_liesOver`, free), and
the `≥` is Stacks 00ON
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), which upgrades it
to an equality exactly under `[Algebra.HasGoingDown A B]`.  The remaining work
is bookkeeping: `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` turns the
three heights into Krull dimensions, and
`IsLocalRing.map_maximalIdeal_of_surjective` identifies the fibre term
`𝔪_B ⬝ (B ⧸ 𝔪_A B)` with the maximal ideal of the fibre ring, so that `hfib`
applies to it.

**Where going-down is the ONLY input that is not free.**  Dropping
`[Algebra.HasGoingDown A B]` leaves `dim B ≤ dim A`, which is Stacks 00OM and
holds for every such pair.  So a consumer that needs only the inequality does
not need this lemma's hardest hypothesis — see the discussion on
`hasGoingDown_stalkMap_of_isFinite_endo` below. -/
theorem ringKrullDim_eq_of_hasGoingDown_of_ringKrullDim_quotient_eq_zero
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Algebra.HasGoingDown A B]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    (hfib : ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) = 0) :
    ringKrullDim B = ringKrullDim A := by
  set I : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hIdef
  have hI : I ≤ IsLocalRing.maximalIdeal B := by
    rw [hIdef, Ideal.LiesOver.over (p := IsLocalRing.maximalIdeal A)
      (P := IsLocalRing.maximalIdeal B)]
    exact Ideal.map_comap_le
  have hIne : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (h ▸ hI))
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : IsLocalRing (B ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmapmax : (IsLocalRing.maximalIdeal B).map (Ideal.Quotient.mk I)
      = IsLocalRing.maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  rw [← hIdef, hmapmax] at h
  have hfib0 : (IsLocalRing.maximalIdeal (B ⧸ I)).height = 0 := by
    have h0 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B ⧸ I)
    rw [hfib] at h0
    exact_mod_cast h0
  rw [hfib0, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A), h]

/-! ### The sub-leaves of going-down for the stalk map of a finite endomorphism

`hasGoingDown_stalkMap_of_isFinite_endo` below is PROVEN over the three
statements `irreducibleSpace_of_smooth_geometricallyConnected`,
`isDominant_of_isFinite_endo` and `isIntegrallyClosed_sections_of_smooth`.  See
the docstring on the consumer for why this is the cut.

**STATUS 2026-07-27, SECOND PASS — all three of those are now PROVEN, and the
frontier of this block is THREE NEW LEAVES, none of them geometric:**

* `topologicalKrullDim_lt_top_of_isProper` — a proper scheme over a field is
  finite-dimensional.  **PROVEN 2026-07-27**, and the note that stood here
  ("Noether normalisation; absent from the pin") was wrong on both counts: the
  pin carries `Mathlib/RingTheory/NoetherNormalization.lean` AND
  `MvPolynomial.ringKrullDim_of_isNoetherianRing`, and the leaf does not need
  the former.  See `exists_ringKrullDim_le_of_finiteType` below.
* `height_map_le_of_isFinite` — a finite morphism does not drop the height of an
  irreducible closed set.  Cohen–Seidenberg, `@[stacks 00OK]`, in poset form.
* `isIntegrallyClosed_of_isRegularRing` — a regular ring is normal.  The single
  piece of commutative algebra, and the one whose route note (on the leaf
  itself) is worth reading before starting.

Everything else in this block is proven, including the topological core
`irreducibleSpace_of_connected_of_isDomain_stalk` (a connected locally
noetherian scheme with domain stalks is irreducible), which is general scheme
theory and mathlib-shaped.

**2026-07-28: that core no longer carries its own proof.**  The same theorem had
been written THREE times in this development — here, in
`Modularity/MoretBailly.lean` and in
`Mathlib/AlgebraicGeometry/CurveExtension.lean` — each time because the existing
copy was unreachable from the new site.  The two ingredients now live once, in
the `Mathlib`-only shim
`Fermat/FLT/Mathlib/AlgebraicGeometry/IrreducibleNhds.lean`, which every one
of the three sites can import, and this file's four-lemma minimum-generalization
chain was deleted in favour of a two-line composition. -/

/-- **THE RESTRICTION MAP BETWEEN TWO AFFINE OPENS IS FLAT** (**PROVEN
2026-07-27** — general scheme theory, three lines over mathlib).

For affine opens `V ≤ W` of any scheme, `Γ(X, W) ⟶ Γ(X, V)` is flat, because
`Spec Γ(X,V) ⟶ Spec Γ(X,W)` is an open immersion.  Mathlib already contains this
in the shape `Flat.flat_appLE`, which for a FLAT morphism `f` asserts flatness of
`f.appLE U V e` for all affine `U`, `V`; taking `f = 𝟙 X` (an isomorphism, hence
flat) and unfolding `Scheme.Hom.appLE` — `(𝟙 X).appLE W V e = 𝟙 ≫ res` — gives
exactly the restriction map, since `(𝟙 X) ⁻¹ᵁ W = W` by `rfl`.

This is what makes `generalizingMap_of_isFinite_of_isIntegral` below able to work
with an ARBITRARY affine open `V` of the source rather than only with `f ⁻¹ᵁ U`:
`Γ(Y,U) → Γ(X,V)` factors as (module-finite) ∘ (flat), and going down is stable
under composition (`Algebra.HasGoingDown.trans`).  That factorisation is not
cosmetic — `Γ(Y,U) → Γ(X,V)` is NOT module-finite for `V` a proper affine open of
`f ⁻¹ᵁ U`, so Krull's theorem does not apply to it directly. -/
theorem flat_presheafMap_of_isAffineOpen {X : Scheme.{u}} {W V : X.Opens} (hW : IsAffineOpen W)
    (hV : IsAffineOpen V) (e : V ≤ W) : (X.presheaf.map (homOfLE e).op).hom.Flat := by
  have h := AlgebraicGeometry.Flat.flat_appLE (𝟙 X) hW hV (show V ≤ (𝟙 X) ⁻¹ᵁ W by simpa using e)
  have h2 : Scheme.Hom.appLE (𝟙 X) W V (show V ≤ (𝟙 X) ⁻¹ᵁ W by simpa using e)
      = X.presheaf.map (homOfLE e).op := by
    have h3 : Scheme.Hom.appLE (𝟙 X) W V (show V ≤ (𝟙 X) ⁻¹ᵁ W by simpa using e)
        = 𝟙 Γ(X, W) ≫ X.presheaf.map (homOfLE e).op := rfl
    simpa using h3
  rw [h2] at h
  exact h

/-- **GOING DOWN FOR A STALK MAP IS A CONSEQUENCE OF THE UNDERLYING MAP BEING
GENERALIZING** (**PROVEN 2026-07-27** — general scheme theory, no hypotheses at
all on `f`, `X` or `Y`; mathlib-shaped).

If the continuous map underlying `f : X ⟶ Y` lifts generalizations, then for
every `x` the ring map `f.stalkMap x : 𝒪_{Y,f x} ⟶ 𝒪_{X,x}` satisfies going
down.

**THIS IS THE TRANSPORT STEP THE OLD ROUTE NOTE DESPAIRED OF**, and it is why
the affine-chart hypotheses below never have to be pushed through a
localisation by hand.  The note on the consumer said the four inputs of Krull's
theorem "must be supplied on an affine chart, and then going-down transported to
the stalks", and transporting `Algebra.HasGoingDown A B` to `A_p → B_q` is real
work.  Restating going down TOPOLOGICALLY removes it: `GeneralizingMap` is local
on source and target for free (opens are stable under generalization), so the
chart statement IS the local statement, and this lemma converts back.

**THE PROOF, in the two facts about `Spec 𝒪_{X,x} ⟶ X` that carry it.**
`X.fromSpecStalk x` is a PREIMMERSION (mathlib instance), so its underlying map
is an embedding — injective, and reflecting specializations; and its range is
exactly the set of generalizations of `x` (`Scheme.range_fromSpecStalk`,
`@[stacks 01J7]`).  With the square
`Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk (f x) = X.fromSpecStalk x ≫ f`
(`Scheme.SpecMap_stalkMap_fromSpecStalk`) the argument is four lines of chasing:
a generalization `q` of `comap p` pushes down to a generalization of
`f (ι_X p)`, lifts along `f` to some `x' ⤳ ι_X p ⤳ x`, and `x' ⤳ x` puts `x'`
back in the range of `ι_X`; the embedding then supplies both the specialization
`p' ⤳ p` and the identification `comap p' = q`.

*Refute with:* an `f` whose base is generalizing but some stalk map is not — by
this proof there is none. -/
theorem hasGoingDown_stalkMap_of_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GeneralizingMap f.base) (x : X) :
    @Algebra.HasGoingDown (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) _ _
      (f.stalkMap x).hom.toAlgebra := by
  letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have halg : algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
      = (f.stalkMap x).hom := rfl
  rw [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap, halg]
  have hsq : ∀ p : Spec (X.presheaf.stalk x),
      (Y.fromSpecStalk (f.base x)).base
          (PrimeSpectrum.comap (f.stalkMap x).hom p)
        = f.base ((X.fromSpecStalk x).base p) := by
    intro p
    have h2 : (Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk (f.base x)) p
        = (X.fromSpecStalk x ≫ f) p := by
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h2
    exact h2
  have hrX : ∀ p : Spec (X.presheaf.stalk x), (X.fromSpecStalk x).base p ⤳ x := by
    intro p
    have : (X.fromSpecStalk x).base p ∈ Set.range (X.fromSpecStalk x).base :=
      Set.mem_range_self p
    rwa [Scheme.range_fromSpecStalk] at this
  intro p q hq
  have h1 : (Y.fromSpecStalk (f.base x)).base q ⤳ f.base ((X.fromSpecStalk x).base p) := by
    have := hq.map (Y.fromSpecStalk (f.base x)).base.hom.continuous
    rwa [hsq p] at this
  obtain ⟨x', hx'le, hx'eq⟩ := hf h1
  have hx'x : x' ⤳ x := hx'le.trans (hrX p)
  have : x' ∈ Set.range (X.fromSpecStalk x).base := by
    rw [Scheme.range_fromSpecStalk]; exact hx'x
  obtain ⟨p', hp'⟩ := this
  refine ⟨p', ?_, ?_⟩
  · exact (X.fromSpecStalk x).isEmbedding.toIsInducing.specializes_iff.mp (hp' ▸ hx'le)
  · refine (Y.fromSpecStalk (f.base x)).isEmbedding.injective ?_
    rw [hsq p', hp', hx'eq]

/-- **A FINITE DOMINANT MORPHISM FROM AN INTEGRAL SCHEME TO A NORMAL ONE IS
GENERALIZING** (**PROVEN 2026-07-27** — this is Krull's going-down theorem,
`@[stacks 00H8]`, descended to schemes.  General scheme theory: no smoothness,
no field, no abelian varieties.)

Normality is asked for in the only form the proof uses: `IsIntegrallyClosed`
for the sections over every NONEMPTY affine open of the target.  (There is no
`IsNormalRing` class in the pin and no normal-scheme class in
`Mathlib/AlgebraicGeometry/`; passing the hypothesis as a plain `∀` avoids
inventing one.)

**HOW THE DESCENT IS DONE, and why no affine cover is constructed by hand.**
`topologically GeneralizingMap` carries `IsZariskiLocalAtSource` and
`IsZariskiLocalAtTarget` instances in mathlib
(`AlgebraicGeometry/Morphisms/UnderlyingMap.lean`), so
`HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget` turns it
into an affine-local property and `HasRingHomProperty.iff_appLE` reduces the
whole statement to: for every affine open `U ⊆ Y` and every affine open
`V ⊆ f ⁻¹ᵁ U`, the ring map `f.appLE U V` satisfies going down.  This is exactly
the shape of mathlib's own `Flat.generalizingMap`, and it is worth copying.

**THE ONE PLACE THE NAIVE ARGUMENT BREAKS, and the fix.**  `Γ(Y,U) → Γ(X,V)` is
*not* module-finite when `V` is a proper affine open of `f ⁻¹ᵁ U` (it inverts
elements), so Krull's theorem does not apply to it.  The map is factored instead:

    Γ(Y, U)  --f.app U-->  Γ(X, f ⁻¹ᵁ U)  --restriction-->  Γ(X, V)

The first factor is module-finite by `IsFinite.finite_app` — `f ⁻¹ᵁ U` is affine
because a finite morphism is affine — and Krull applies to it; the second is FLAT
(`flat_presheafMap_of_isAffineOpen` above) and flat maps satisfy going down
(`Algebra.HasGoingDown.of_flat`, `@[stacks 00HS]`).  `Algebra.HasGoingDown.trans`
(`@[stacks 00HX]`) composes them.

**THE FOUR INPUTS OF KRULL'S INSTANCE, and where each comes from.**

1. `Algebra.IsIntegral Γ(Y,U) Γ(X, f ⁻¹ᵁ U)` — `IsFinite.finite_app` then
   `Algebra.IsIntegral.of_finite`.
2. `IsDomain Γ(X, f ⁻¹ᵁ U)` — `IsIntegral X` and `f ⁻¹ᵁ U` nonempty.
3. `FaithfulSMul Γ(Y,U) Γ(X, f ⁻¹ᵁ U)` — injectivity of `f.app U`.  This is
   `Scheme.Hom.app_injective`, which needs `IsSchemeTheoreticallyDominant f`; and
   `IsSchemeTheoreticallyDominant.of_isDominant` supplies it from `[IsDominant f]`
   together with `[IsReduced Y]`.  **This is the only use of dominance, and it is
   essential** — witnessed by the CLOSED IMMERSION OF THE ORIGIN
   `f : Spec k ⟶ Spec k[t]`, i.e. `Spec.map` of the `k`-algebra map
   `A := k[t] → B := k`, `t ↦ 0`.  Every hypothesis of this theorem except
   dominance holds for it: `B = k` is generated by `1` as an `A`-module, so `f` is
   FINITE; `Spec k` is integral; `Spec k[t]` is reduced; and `k[t]` is a PID, so it
   and all its localizations are integrally closed.  Dominance fails because the
   image is the single closed point `(t)`.  And the conclusion fails with it: on
   `U = ⊤` take the chain `(0) < (t)` in `A` and the prime `Q = (0)` of `B` — the
   unique prime of the field `k` — which lies over `(t)`.  Going down would demand
   a prime of `B` contained in `Q` lying over `(0)`, and `(0)` is the only prime of
   `B` there is, contracting to `(t) ≠ (0)`.  Equivalently, the generic point of
   `Spec k[t]` is a generalization of `f (0)` with no preimage at all, so
   `GeneralizingMap f.base` is outright false.

   **(Witness corrected 2026-07-27; the previous one was INVALID.)**  What stood
   here was `u : Spec k[t] ⟶ Spec k[t]` induced by `t ↦ 0`.  **That morphism is not
   finite**, so it says nothing about a theorem hypothesising `[IsFinite f]`:
   `k[t]` as a module over itself through `t ↦ 0` is `k[t]` with `t` acting as
   ZERO, i.e. a countably-infinite-dimensional `k`-vector space, not a finitely
   generated module.  The same invalid witness stood in the docstring of
   `isDominant_of_isFinite_endo` below, where it was corrected the same day; that
   correction is where the replacement above comes from.
4. `IsIntegrallyClosed Γ(Y,U)` — the hypothesis `hnormal`.

The EMPTY affine open is not an exception to be worried about: `Γ(X, ⊥)` is
subsingleton, so it has no prime ideals and going down holds vacuously.  That
branch is discharged explicitly rather than by a nonemptiness side condition,
because `iff_appLE` really does quantify over every affine open. -/
theorem generalizingMap_of_isFinite_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsReduced Y] [IsDominant f]
    (hnormal : ∀ (U : Y.affineOpens), Nonempty ↥U.1 → IsIntegrallyClosed Γ(Y, U.1)) :
    GeneralizingMap f.base := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  letI algUV : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 e).hom.toAlgebra
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  by_cases hV : Nonempty ↥V.1
  · haveI := hV
    have hW : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
    haveI hUne : Nonempty ↥U.1 := ⟨⟨f.base hV.some.1, e hV.some.2⟩⟩
    letI algW : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
    letI algWV : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, V.1) :=
      (X.presheaf.map (homOfLE (show V.1 ≤ f ⁻¹ᵁ U.1 from e)).op).hom.toAlgebra
    haveI : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, V.1) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsDomain Γ(X, f ⁻¹ᵁ U.1) :=
      @IsIntegral.component_integral _ _ _ ⟨⟨hV.some.1, e hV.some.2⟩⟩
    haveI : Module.Finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := f.finite_app U.1 U.2
    haveI : Algebra.IsIntegral Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := Algebra.IsIntegral.of_finite _ _
    haveI : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
    haveI : FaithfulSMul Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.app_injective U.1)
    haveI := hnormal U hUne
    haveI hgd1 : Algebra.HasGoingDown Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := inferInstance
    haveI : Module.Flat Γ(X, f ⁻¹ᵁ U.1) Γ(X, V.1) :=
      flat_presheafMap_of_isAffineOpen hW V.2 (show V.1 ≤ f ⁻¹ᵁ U.1 from e)
    haveI hgd2 : Algebra.HasGoingDown Γ(X, f ⁻¹ᵁ U.1) Γ(X, V.1) := Algebra.HasGoingDown.of_flat
    exact Algebra.HasGoingDown.trans Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, V.1)
  · have hbot : V.1 = ⊥ := by
      rw [← TopologicalSpace.Opens.not_nonempty_iff_eq_bot]
      exact fun hne => hV hne.to_subtype
    haveI : Subsingleton Γ(X, V.1) := by rw [hbot]; infer_instance
    constructor
    intro p _ Q hQ _
    exact absurd (Subsingleton.elim Q ⊤) hQ.ne_top

-- `exists_isOpen_specializes_of_min_generalization` (a noetherian sober space in
-- which `z` has a MINIMUM generalization `ζ` has an open `W ∋ z` generalized by
-- `ζ`) was DELETED on 2026-07-28, together with its two scheme-level corollaries
-- `exists_min_generalization_of_isDomain_stalk` and
-- `exists_isOpen_specializes_of_isDomain_stalk`.  They were the private cone of
-- `irreducibleSpace_of_connected_of_isDomain_stalk` below and had no other
-- consumer; that theorem is now the two-line composition of the shim lemmas
-- `irreducibleSpace_of_isOpen_isIrreducible_nhds` and
-- `exists_isOpen_isIrreducible_nhds_of_isDomain_stalk`
-- (`Fermat/FLT/Mathlib/AlgebraicGeometry/IrreducibleNhds.lean`), which prove
-- the same theorem by the irreducible-neighbourhood route.  Recover the
-- minimum-generalization proof from git history if it is ever wanted: it is
-- genuinely different — it uses no `T0`/antisymmetry, only specialization
-- chasing — but a second proof of a theorem this development already had three
-- copies of is exactly what the shim exists to stop.

/-- **A CONNECTED LOCALLY NOETHERIAN SCHEME WITH DOMAIN STALKS IS IRREDUCIBLE**
(**PROVEN 2026-07-27**; **REPROVED 2026-07-28** as a two-line composition of the
shim module `Fermat/FLT/Mathlib/AlgebraicGeometry/IrreducibleNhds.lean` —
general scheme theory, no field and no smoothness; this is the statement the pin
does not have, and it is what
`irreducibleSpace_of_smooth_geometricallyConnected` below is a corollary of).

**THE PROOF.**  `exists_isOpen_isIrreducible_nhds_of_isDomain_stalk` gives every
point an irreducible OPEN neighbourhood (on an affine chart the domain stalk
pins a unique minimal prime below the point, and removing the finitely many
other minimal primes leaves an open subset of the irreducible `V(q)`), and
`irreducibleSpace_of_isOpen_isIrreducible_nhds` upgrades that to
global irreducibility by a clopen argument on `irreducibleComponent x₀`.  Both
live in the shim because this development had written the same theorem THREE
times; see that module's header.

**A SECOND, GENUINELY DIFFERENT PROOF LIVED HERE UNTIL 2026-07-28** and is
recoverable from git history: writing `ζ x` for the *minimum* generalization of
`x` (which a domain stalk supplies through `Scheme.range_fromSpecStalk`), the
set `S := {y | ∃ ξ, ξ ⤳ x₀ ∧ ξ ⤳ y}` of points sharing a generalization with
`x₀` is clopen, so `X = closure {ζ x₀}`.  It uses NO `T0`/antisymmetry — only
specialization chasing — which is why it is worth naming even though it is
deleted.  It was written because `MoretBailly.lean`, which already held the
argument below, is strictly DOWNSTREAM of this file; hoisting removed that
reason. -/
theorem irreducibleSpace_of_connected_of_isDomain_stalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    [ConnectedSpace X] (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    IrreducibleSpace X :=
  _root_.irreducibleSpace_of_isOpen_isIrreducible_nhds
    (fun x => _root_.AlgebraicGeometry.exists_isOpen_isIrreducible_nhds_of_isDomain_stalk
      x (hdom x))

/-- **A SMOOTH GEOMETRICALLY CONNECTED SCHEME OVER A FIELD IS IRREDUCIBLE**
(**PROVEN 2026-07-27** over the general scheme-theoretic
`irreducibleSpace_of_connected_of_isDomain_stalk` immediately above; created as
a sorry leaf earlier the same day — step 1 of the route recorded on
`ringKrullDim_stalk_eq_of_isFinite_endo` below.  General scheme theory over a
field, NO abelian varieties.)

`Smooth g` makes every stalk of `X` regular local
(`isRegularLocalRing_stalk_of_smooth` above) hence a DOMAIN
(`GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`), and locally
noetherian because a smooth morphism is locally of finite type and
`Spec K` is noetherian (`LocallyOfFiniteType.isLocallyNoetherian`).
`GeometricallyConnected g` makes `X` CONNECTED, via
`GeometricallyConnected.connectedSpace_of_subsingleton` — `Spec K` for `K` a
field is a ONE-POINT space, so no openness hypothesis is needed.

**WHY THIS IS NOT ALREADY IN THE PIN** (checked 2026-07-27, and each check is
what would refute the claim).  `grep -rn "IrreducibleSpace"
Mathlib/AlgebraicGeometry/ | grep -iE "connected|stalk|domain|normal"` returns
only `instance {R} [IsDomain R] : IrreducibleSpace (Spec R)` and unrelated
`FunctionField`/`Birational` uses — there is no "connected + locally irreducible
⟹ irreducible".  Mathlib DOES have the two conversions on either side of it:
`isIntegral_of_irreducibleSpace_of_isReduced` and
`isReduced_of_isReduced_stalk`, which is why reducedness is proven outright in
`isIntegral_of_smooth_geometricallyConnected` below.

**THE `GeometricallyIrreducible` ROUTE WAS A DEAD END, and it is worth saying
why so that nobody retries it.**  The note that stood here suggested
`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`, since `Spec K` is a
one-point space.  But its hypothesis `GeometricallyIrreducible g` asks for
`X ×_K L` to be irreducible for EVERY field `L` over `K` — strictly more than
the conclusion wanted here, and each of those base changes is smooth and
geometrically connected over `L`, i.e. an instance of this very lemma.  The
route is circular, not cheaper.  What actually closed the leaf is the
minimum-generalization argument on the lemma above.

**ONLY ORDINARY CONNECTEDNESS IS USED**, so `GeometricallyConnected` may be
weakened freely; it appears because that is what the caller has in hand
(`AbelianSchemeStruct.connected`). -/
theorem irreducibleSpace_of_smooth_geometricallyConnected {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [GeometricallyConnected g] :
    IrreducibleSpace X := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := by
    rw [isLocallyNoetherian_Spec]; infer_instance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton g
  exact irreducibleSpace_of_connected_of_isDomain_stalk X (fun x => by
    haveI := isRegularLocalRing_stalk_of_smooth g x
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _)

/-- **A SMOOTH GEOMETRICALLY CONNECTED SCHEME OVER A FIELD IS INTEGRAL**
(**PROVEN 2026-07-27** over the single leaf
`irreducibleSpace_of_smooth_geometricallyConnected` immediately above).

Reducedness is discharged here and is NOT a leaf: the stalks are regular local
(`isRegularLocalRing_stalk_of_smooth`), hence domains
(`GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`), hence
reduced, and `isReduced_of_isReduced_stalk` lifts that to the scheme.  Note this
route is `sorryAx`-free, whereas the project's own
`AlgebraicGeometry.isReduced_of_smooth_over_field`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`) is built
over the still-open `Algebra.Smooth.isReduced_of_isField`; using the stalks
avoids importing that leaf's sorry into this cone. -/
theorem isIntegral_of_smooth_geometricallyConnected {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [GeometricallyConnected g] :
    AlgebraicGeometry.IsIntegral X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := isRegularLocalRing_stalk_of_smooth g x
    haveI := GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing
      (X.presheaf.stalk x)
    infer_instance
  haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
  haveI := irreducibleSpace_of_smooth_geometricallyConnected g
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- **A FINITELY GENERATED ALGEBRA OVER A FIELD HAS FINITE KRULL DIMENSION**
(**PROVEN 2026-07-27**, four lines — the ring-theoretic half of
`topologicalKrullDim_lt_top_of_isProper` below.)

`A` is a quotient of `K[X₁, …, Xₙ]` for some `n`
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`); a surjection cannot raise
Krull dimension (`ringKrullDim_le_of_surjective`); and
`dim K[X₁, …, Xₙ] = dim K + n = n` by
`MvPolynomial.ringKrullDim_of_isNoetherianRing` (a field is noetherian) together
with `ringKrullDim_eq_zero_of_field`.

**THE PREVIOUS NOTE ON THE LEAF BELOW SAID THIS WAS MISSING FROM THE PIN.  IT
IS NOT, AND THE RECORD IS CORRECTED HERE** (2026-07-27, each item re-checked
against `.lake/packages/mathlib` at our pin `a3364fa`):

* `Mathlib/RingTheory/KrullDimension/Polynomial.lean` does **not** stop at
  `dim R[X] = dim R + 1`.  It ends with
  `MvPolynomial.ringKrullDim_of_isNoetherianRing :
  ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι` for `[Finite ι]`
  and `[IsNoetherianRing R]` — the multivariate statement, in full.
* The quotient step is `ringKrullDim_le_of_surjective` /
  `ringKrullDim_quotient_le`, both in `KrullDimension/Basic.lean`, three lines
  above the `proof_wanted` that the old note quoted.  The `proof_wanted`
  `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` really is open, but
  it is a `Fin n`-indexed *restatement* of a theorem that is already there, so
  its openness says nothing about availability.
* **Noether normalisation is in the pin too**, as
  `Mathlib/RingTheory/NoetherNormalization.lean`
  (`exists_integral_inj_algHom_of_fg`, `exists_finite_inj_algHom_of_fg`), and it
  is already used by this project in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.  It is not
  needed for the bound proved here — a surjection from a polynomial ring
  suffices when only FINITENESS, not the exact value, is wanted — but the claim
  that a grep "returns nothing" was simply wrong.

The moral is the standing one: a "this is absent from the pin" note is a
hypothesis to re-run, not a fact. -/
theorem exists_ringKrullDim_le_of_finiteType (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A ≤ (n : WithBot ℕ∞) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine ⟨n, ?_⟩
  refine (ringKrullDim_le_of_surjective f.toRingHom hf).trans (le_of_eq ?_)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K]
  simp

/-- **COHEIGHT IS LOCALLY BOUNDED ON A SCHEME LOCALLY OF FINITE TYPE OVER A
FIELD** (**PROVEN 2026-07-27** — the local half of
`topologicalKrullDim_lt_top_of_isProper` below; no properness, no
quasi-compactness, so the two halves are cleanly separated).

Every point has an open neighbourhood on which `Order.coheight` is bounded by a
single natural number.  Properness contributes nothing here; it is used only in
the assembly, to turn "locally bounded" into "bounded" by compactness.

THE PROOF.  Take an affine open immersion `f : Spec R ⟶ X` whose range contains
`x` (`Scheme.exists_affine_mem_range_and_range_subset`).  Then `R` is a finitely
generated `K`-algebra — `HasRingHomProperty.appTop` applied to `f ≫ g`,
conjugated by the two `Scheme.ΓSpecIso`s, with `RingHom.FiniteType` surviving
the conjugation by `RingHom.finiteType_respectsIso`; this is the same step as in
`AlgebraicGeometry.exists_coheight_le_of_isOpenImmersion_of_irreducible`.  For a
point of the range, `coheight` is computed in the chart
(`coheight_eq_of_isOpenImmersion`), where it is the height of the corresponding
prime (`idealHeight_eq_coheight`), and every prime's height is at most
`ringKrullDim R` (`Ideal.height_le_ringKrullDim_of_isPrime`), which is finite by
`exists_ringKrullDim_le_of_finiteType` above. -/
theorem exists_coheight_le_of_locallyOfFiniteType {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g] (x : ↥X) :
    ∃ V : Set ↥X, IsOpen V ∧ x ∈ V ∧ ∃ n : ℕ, ∀ y ∈ V, Order.coheight y ≤ (n : ℕ∞) := by
  obtain ⟨R, f, hfimm, hxmem, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := X) (x := x) (U := ⊤) trivial
  haveI := hfimm
  refine ⟨Set.range f.base, f.isOpenEmbedding.isOpen_range, hxmem, ?_⟩
  haveI : LocallyOfFiniteType (f ≫ g) := inferInstance
  have hQ : RingHom.FiniteType (f ≫ g).appTop.hom :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (f ≫ g) ‹_›
  letI : Algebra K R := RingHom.toAlgebra (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (f ≫ g).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
  haveI : Algebra.FiniteType K R := by
    have hfin : RingHom.FiniteType (algebraMap K R) := by
      show RingHom.FiniteType (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (f ≫ g).appTop ≫ (Scheme.ΓSpecIso R).hom).hom)
      rw [CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_left_isIso,
        CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_right_isIso]
      exact hQ
    exact RingHom.finiteType_algebraMap.mp hfin
  obtain ⟨n, hn⟩ := exists_ringKrullDim_le_of_finiteType K R
  refine ⟨n, ?_⟩
  rintro y ⟨z, rfl⟩
  haveI : z.asIdeal.IsPrime := z.isPrime
  have h2 : (z.asIdeal.height : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
    Ideal.height_le_ringKrullDim_of_isPrime.trans hn
  have h3 : z.asIdeal.height ≤ (n : ℕ∞) := by exact_mod_cast h2
  rw [coheight_eq_of_isOpenImmersion f, ← idealHeight_eq_coheight R z]
  exact h3

/-- **A PROPER SCHEME OVER A FIELD IS FINITE-DIMENSIONAL** (**PROVEN
2026-07-27**, over the two statements immediately above; created as a sorry leaf
earlier the same day, as the FIRST of the two sub-leaves of
`isDominant_of_isFinite_endo` below.  Pure dimension theory: no smoothness, no
connectedness, no endomorphism.)

`topologicalKrullDim X` is the Krull dimension of the poset
`TopologicalSpace.IrreducibleCloseds X` — the length of the longest chain of
irreducible closed subsets.  For `X` proper over a field it is finite.

THE PROOF, in three moves, none of which needed a theory build:

1. **`X` is quasi-compact as a space.**  `IsProper g` extends
   `UniversallyClosed g`, and mathlib has
   `instance (priority := 900) [UniversallyClosed f] : QuasiCompact f`
   (`@[stacks 04XU]`); `Spec K` is compact, so
   `QuasiCompact.compactSpace_of_compactSpace` gives `CompactSpace ↥X`.  This is
   the ONLY use of properness — everything else needs just
   `LocallyOfFiniteType g`.
2. **Coheight is locally bounded** — `exists_coheight_le_of_locallyOfFiniteType`
   above, whose ring-theoretic input is `exists_ringKrullDim_le_of_finiteType`.
3. **Assembly.**  Compactness turns the pointwise neighbourhoods of (2) into a
   finite subcover, so a single `N := s.sup n` bounds every coheight; and
   `AlgebraicGeometry.topologicalKrullDim_eq_iSup_coheight` (in
   `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`, proven
   there from sobriety) rewrites `topologicalKrullDim X` as `⨆ x, coheight x`,
   which is therefore `≤ N < ⊤`.

**THE OLD "WHY THIS IS THE MISSING PIECE" NOTE WAS WRONG AND HAS BEEN DELETED.**
It asserted that the statement reduces to Noether normalisation and that the pin
has neither Noether normalisation nor the Krull dimension of a multivariate
polynomial ring.  Both halves are false; see the corrected record on
`exists_ringKrullDim_le_of_finiteType` above.  The note also missed that the
scheme-level bridge it despaired of was already PROVEN inside this project.
Nothing about this leaf was hard once the three greps it prescribed were
actually re-run — which is exactly what it invited a reader to do, so it failed
in its conclusion rather than in its method.

**THE EMPTY SCHEME IS NOT AN EXCEPTION**: `topologicalKrullDim` of an empty
space is `⊥ : WithBot ℕ∞`, which is `< ⊤`, and the proof below never assumes a
point exists. -/
theorem topologicalKrullDim_lt_top_of_isProper {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [IsProper g] :
    topologicalKrullDim X < ⊤ := by
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace g
  choose V hVo hxV n hn using exists_coheight_le_of_locallyOfFiniteType g
  obtain ⟨s, hs⟩ := CompactSpace.isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  have hbound : ∀ y : ↥X, Order.coheight y ≤ ((s.sup n : ℕ) : ℕ∞) := by
    intro y
    obtain ⟨x, hxs, hyV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
    exact (hn x y hyV).trans (by exact_mod_cast Finset.le_sup hxs)
  have hle : (⨆ x : ↥X, (Order.coheight x : WithBot ℕ∞)) ≤ ((((s.sup n : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    iSup_le fun x => WithBot.coe_le_coe.mpr (hbound x)
  have htop : ((((s.sup n : ℕ) : ℕ∞)) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (by simp)
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_coheight X]
  exact lt_of_le_of_lt hle htop

/-- **THE CLOSURE OF THE IMAGE OF A SET WITH A GENERIC POINT** (**PROVEN
2026-07-27**, pure point-set topology, no schemes).

If `closure {x} = S` then `closure (f '' S) = closure {f x}` for `f` continuous:
one inclusion is `image_closure_subset_closure_image`, the other is monotonicity
of `closure` along `{f x} ⊆ f '' S`.  Extracted as a standalone step of
`height_map_le_of_isFinite` below because rewriting `↑W` inside
`W.isIrreducible.genericPoint` is not motive-correct — the generic point has to
be abstracted BEFORE the underlying set is rewritten. -/
theorem closure_image_of_closure_singleton_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {S : Set X} {x : X}
    (hx : closure ({x} : Set X) = S) :
    closure (f '' S) = closure {f x} := by
  subst hx
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · refine (image_closure_subset_closure_image hf).trans ?_
    simp
  · exact Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩

/-- **A QUASI-FINITE MORPHISM SEPARATES SPECIALIZATIONS INSIDE A FIBRE**
(**PROVEN 2026-07-27**, the incomparability half of Cohen–Seidenberg in its
topological form — `@[stacks 00OY]`).

If `x ⤳ y` and `f x = f y` then `x = y`.  Both points lie in the fibre
`f ⁻¹' {f x}`, which is DISCRETE for a quasi-finite morphism
(`Scheme.Hom.isDiscrete_preimage_singleton`, mathlib); `Subtype.val` is inducing,
so the specialization transports into the fibre, and a discrete space is `T1`,
where specialization is equality.

Note this needs only `LocallyQuasiFinite`, not `IsFinite`. -/
theorem eq_of_specializes_of_base_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (h : x ⤳ y) (he : f.base x = f.base y) : x = y := by
  have hd : _root_.IsDiscrete (⇑f ⁻¹' {f.base x}) := f.isDiscrete_preimage_singleton _
  haveI : DiscreteTopology ↥(⇑f ⁻¹' {f.base x}) := hd.to_subtype
  have hx : x ∈ (⇑f ⁻¹' {f.base x}) := rfl
  have hy : y ∈ (⇑f ⁻¹' {f.base x}) := he.symm
  have hs : (⟨x, hx⟩ : ↥(⇑f ⁻¹' {f.base x})) ⤳ ⟨y, hy⟩ :=
    (_root_.Topology.IsInducing.subtypeVal).specializes_iff.mp h
  simpa using specializes_iff_eq.mp hs

/-- **`IrreducibleCloseds.map` ALONG A QUASI-FINITE MORPHISM IS STRICTLY
MONOTONE** (**PROVEN 2026-07-27**; this is the whole mathematical content of
`height_map_le_of_isFinite` below, and it holds GLOBALLY, not merely below a
fixed `Z`).

Given `A < B` irreducible closed, monotonicity gives `map A ≤ map B`; the
inclusion is strict.  Schemes are sober, so `A = closure {ξA}` and
`B = closure {ξB}`; by `closure_image_of_closure_singleton_eq` the images are
`closure {f ξA}` and `closure {f ξB}`, so equality of the images gives
`f ξA ⤳ f ξB` and `f ξB ⤳ f ξA`, hence `f ξA = f ξB` because a scheme is `T0`.
And `A ≤ B` puts `ξA ∈ B = closure {ξB}`, i.e. `ξB ⤳ ξA`.  The two points are
therefore a specialization pair inside one fibre, so they are EQUAL
(`eq_of_specializes_of_base_eq`), whence `A = B` — contradicting `A < B`.

**INJECTIVITY IS FALSE AND IS NOT USED**: `Spec (k × k) ⟶ Spec k` sends the two
points to the one point, so `map` is not injective, and the standard
`Monotone.strictMono_of_injective` route is unavailable.  Strict monotonicity
survives precisely because the two points there are INCOMPARABLE. -/
theorem strictMono_irreducibleCloseds_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] :
    StrictMono (TopologicalSpace.IrreducibleCloseds.map (⇑f.base) f.base.hom.continuous) := by
  have hcont : Continuous (⇑f.base) := f.base.hom.continuous
  intro A B hAB
  refine lt_of_le_of_ne (TopologicalSpace.IrreducibleCloseds.map_mono hcont hAB.le) ?_
  intro heq
  obtain ⟨ξA, hA⟩ : ∃ x, closure ({x} : Set X) = (A : Set X) :=
    ⟨A.isIrreducible.genericPoint, A.isIrreducible.closure_genericPoint A.isClosed⟩
  obtain ⟨ξB, hB⟩ : ∃ x, closure ({x} : Set X) = (B : Set X) :=
    ⟨B.isIrreducible.genericPoint, B.isIrreducible.closure_genericPoint B.isClosed⟩
  have hco : closure (⇑f.base '' (A : Set X)) = closure (⇑f.base '' (B : Set X)) := by
    have h := congrArg (fun W : TopologicalSpace.IrreducibleCloseds Y => (W : Set Y)) heq
    simpa using h
  have hcl : closure ({f.base ξA} : Set Y) = closure {f.base ξB} := by
    rw [← closure_image_of_closure_singleton_eq hcont hA,
      ← closure_image_of_closure_singleton_eq hcont hB]
    exact hco
  have h1 : f.base ξA ⤳ f.base ξB := by
    rw [specializes_iff_mem_closure, hcl]; exact subset_closure rfl
  have h2 : f.base ξB ⤳ f.base ξA := by
    rw [specializes_iff_mem_closure, ← hcl]; exact subset_closure rfl
  have hfe : f.base ξA = f.base ξB := (h1.antisymm h2).eq
  have hmemA : ξA ∈ (A : Set X) := by
    have hmem : ξA ∈ closure ({ξA} : Set X) := subset_closure rfl
    rwa [hA] at hmem
  have hspec : ξB ⤳ ξA := by
    rw [specializes_iff_mem_closure, hB]
    exact hAB.le hmemA
  have hξ : ξB = ξA := eq_of_specializes_of_base_eq f hspec hfe.symm
  exact absurd (TopologicalSpace.IrreducibleCloseds.ext (by rw [← hA, ← hB, hξ])) hAB.ne

/-- **A FINITE MORPHISM DOES NOT DROP THE HEIGHT OF AN IRREDUCIBLE CLOSED SET**
(**PROVEN 2026-07-27** over the three general lemmas immediately above; created
as a sorry leaf earlier the same day as the SECOND sub-leaf of
`isDominant_of_isFinite_endo` below.  General scheme theory: no field, no
smoothness, no properness, and `X`, `Y` arbitrary.)

For `f : X ⟶ Y` finite and `Z` an irreducible closed subset of `X`, the height
of `Z` in `TopologicalSpace.IrreducibleCloseds X` is at most the height of
`closure (f '' Z)` in `TopologicalSpace.IrreducibleCloseds Y`.  This is the
Cohen–Seidenberg content of Krull dimension theory — "an integral extension does
not lower dimension", `@[stacks 00OK]` — in the shape the assembly below needs
it, and it is a statement about ONE `Z` rather than about whole dimensions, so
no subspace-dimension API is required.

**THE PROOF, and it is quasi-finiteness rather than finiteness that carries it.**
Given a strict chain `Z₀ < Z₁ ≤ Z` of irreducible closeds, the images satisfy
`closure (f '' Z₀) ⊆ closure (f '' Z₁)`, and the inclusion is STRICT: writing
`ξᵢ` for the generic point of `Zᵢ` (schemes are sober), one has
`closure (f '' Zᵢ) = closure {f ξᵢ}`, so equality of the images would give
`f ξ₀ = f ξ₁` by `T0`, while `ξ₁ ⤳ ξ₀` puts the two points in the SAME FIBRE.
A finite morphism is quasi-finite and its fibres are discrete, so a fibre carries
no nontrivial specialization and `ξ₀ = ξ₁`, contradicting `Z₀ < Z₁`.  Hence
`IrreducibleCloseds.map` is strictly monotone below `Z`, which is exactly the
height inequality.

*Refute with:* a finite morphism, an irreducible closed `Z`, and a chain below it
whose image chain collapses — by the argument above there is none.

**THE WEAKENING PREDICTED HERE IS CONFIRMED, AND FOR FREE.**  The note that
stood here said `IsFinite` "may be weakened to `QuasiFinite`"; it is, and by more
than expected.  Nothing in the proof uses finiteness or quasi-compactness — only
`LocallyQuasiFinite`, through the DISCRETENESS of the fibres — so the real
theorem is `strictMono_irreducibleCloseds_map` above, stated with
`[LocallyQuasiFinite f]`, and it is strictly monotone GLOBALLY rather than merely
below `Z`.  This statement keeps `[IsFinite f]` because that is what the consumer
`isDominant_of_isFinite_endo` has in hand, and mathlib's
`IsFinite f → LocallyQuasiFinite f` instance bridges the two silently.  A
consumer wanting the weaker hypothesis should call
`strictMono_irreducibleCloseds_map` and
`Order.height_le_height_apply_of_strictMono` directly. -/
theorem height_map_le_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (Z : TopologicalSpace.IrreducibleCloseds X) :
    Order.height Z ≤ Order.height
      (TopologicalSpace.IrreducibleCloseds.map (⇑f.base) f.base.hom.continuous Z) :=
  Order.height_le_height_apply_of_strictMono _ (strictMono_irreducibleCloseds_map f) Z

/-- **A FINITE ENDOMORPHISM OF A PROPER GEOMETRICALLY CONNECTED SMOOTH SCHEME
OVER A FIELD IS DOMINANT** (**PROVEN 2026-07-27** over
`topologicalKrullDim_lt_top_of_isProper` (itself PROVEN later the same day) and
the single remaining leaf `height_map_le_of_isFinite`
immediately above; created as a single sorry leaf earlier the same day — step 2
of the route recorded on `ringKrullDim_stalk_eq_of_isFinite_endo` below.
General scheme theory over a field, NO abelian varieties, no group law, no
`[n]`.)

**THE ARGUMENT, once `X` is IRREDUCIBLE** (which is
`irreducibleSpace_of_smooth_geometricallyConnected` above, now proven).  Let
`T := ⊤` and `Z := closure (u '' T) = closure (range u)`, both irreducible
closed.  If `u` is NOT dominant then `Z < T`, so `height Z + 1 ≤ height T`
(`Order.height_add_one_le`); but `height T ≤ height Z` because a finite morphism
does not drop heights (`height_map_le_of_isFinite`); and `height T < ⊤` because
`X` is finite-dimensional (`topologicalKrullDim_lt_top_of_isProper`, through
`Order.height_le_krullDim`).  `n + 1 ≤ n` with `n ≠ ⊤` is false in `ℕ∞`.

Note the proof never constructs the image as a SUBSCHEME and never uses the
dimension of a subspace: everything happens inside the single poset
`TopologicalSpace.IrreducibleCloseds X`, where `Order.height` already measures
"the dimension of `Z`".  That is what removes the scheme-level dimension theory
the earlier route note despaired of, leaving only the two leaves above.

**PROPERNESS IS USED — BUT ONLY THROUGH FINITE-DIMENSIONALITY, AND THE
COUNTEREXAMPLE PREVIOUSLY RECORDED HERE IS WRONG.**  The note that stood here
said the statement is FALSE without `IsProper g`, witnessed by
`u : Spec k[t] ⟶ Spec k[t]` "induced by `t ↦ 0`", asserted to be finite because
"`k[t]` is a finite `k[t]`-module through `t ↦ 0`, being `k`".  **That morphism
is not finite.**  A morphism `Spec B ⟶ Spec A` with image the single closed
point `(t)` comes from the ring map `A = k[t] → B = k[t]` sending `t ↦ 0`; `B`
as an `A`-module through it is `k[t]` with `t` acting as ZERO, i.e. a
countably-infinite-dimensional `k`-vector space — not a finitely generated
`A`-module.  So no conclusion about dropping properness follows from it.

What properness IS used for is exactly `topologicalKrullDim X < ⊤`: closedness
of `u` is free (every finite morphism is closed, proper or not), and
`height_map_le_of_isFinite` uses no properness either.  Whether the leaf survives
dropping `IsProper g` therefore reduces to whether an IRREDUCIBLE scheme locally
of finite type over a field is finite-dimensional — false in general for
non-quasi-compact schemes — so properness (or just quasi-compactness) is
plausibly still needed, but that is an OPEN question here and not a settled one.

The same invalid witness appeared in item 3 of the docstring of
`generalizingMap_of_isFinite_of_isIntegral` above, where dominance really is
essential; **that occurrence has now been corrected in place** (2026-07-27) to
the closed immersion of the origin `Spec k ⟶ Spec k[t]` (`k[t] → k`,
module-finite, not dominant): the chain `(0) < (t)` in `k[t]` has `Q = (0)` of
`k` lying over `(t)`, and `k` has no other prime to lie over `(0)`, so going
down fails.  The file has been swept: no further occurrence remains. -/
theorem isDominant_of_isFinite_endo {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsFinite u] :
    IsDominant u := by
  haveI : IrreducibleSpace X := irreducibleSpace_of_smooth_geometricallyConnected g
  by_contra hnd
  have hne : closure (Set.range (⇑u.base)) ≠ Set.univ := by
    intro h
    exact hnd ⟨by rw [DenseRange, dense_iff_closure_eq]; exact h⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let Z : TopologicalSpace.IrreducibleCloseds X :=
    TopologicalSpace.IrreducibleCloseds.map (⇑u.base) u.base.hom.continuous T
  have hZcoe : (Z : Set X) = closure (Set.range (⇑u.base)) := by
    show closure (⇑u.base '' (Set.univ : Set X)) = _
    rw [Set.image_univ]
  have hZT : Z < T := by
    refine lt_of_le_of_ne (fun x _ => trivial) ?_
    intro h
    exact hne (hZcoe ▸ SetLike.coe_set_eq.mpr h)
  have h1 : Order.height Z + 1 ≤ Order.height T := Order.height_add_one_le hZT
  have h2 : Order.height T ≤ Order.height Z := height_map_le_of_isFinite u T
  have h3 : Order.height T < ⊤ :=
    WithBot.coe_lt_coe.mp
      (lt_of_le_of_lt (Order.height_le_krullDim T) (topologicalKrullDim_lt_top_of_isProper g))
  have h4 : Order.height Z ≠ ⊤ := ne_top_of_le_ne_top h3.ne (Order.height_mono hZT.le)
  exact absurd ((ENat.add_one_le_iff h4).mp (h1.trans h2)) (lt_irrefl _)

/-- **A REGULAR LOCAL RING IS INTEGRALLY CLOSED, IN THE FORM THIS DEVELOPMENT
NEEDS IT** (sorry leaf, created 2026-07-27 — **this is the one genuinely missing
piece of COMMUTATIVE ALGEBRA under `flat_of_finite_fibres_endo`**, and it is
absent from mathlib, from this project, and from `~/cs/FLT`).

`Γ(X, U)` is integrally closed for every nonempty affine open `U` of a scheme
smooth over a field.

**WHY IT IS STATED GEOMETRICALLY RATHER THAN AS "regular ⟹ normal".**  The
abstract statement

> a regular local ring is integrally closed

is TRUE but its standard proofs need machinery the pin does not have: Serre's
criterion (`R1` + `S2`), which needs Cohen–Macaulayness — `ls
Mathlib/RingTheory/` has no `CohenMacaulay*` and `grep -rln "Serre"
Mathlib/RingTheory/` returns only `DiscreteValuationRing/Basic.lean`,
`Valuation/Discrete/Basic.lean` and `Polynomial/Morse.lean`, none of them this
criterion — or Auslander–Buchsbaum (regular ⟹ UFD).  There is no `IsNormalRing`
class in the pin at all, and `Mathlib/RingTheory/RegularLocalRing/` contains only
`Defs.lean` and `Polynomial.lean`.

The induction that DOES work here needs to know that the localisations of the
ring at all its primes are again regular local — which for an ABSTRACT regular
local ring is Serre's theorem (localisation of regular is regular, via finite
global dimension) and is missing, but which HERE IS FREE: the localisations of
`Γ(X,U)` at its primes are the stalks of `X`, and every stalk of a smooth `X` is
regular local by `isRegularLocalRing_stalk_of_smooth` above.  So stating the leaf
over `Γ(X,U)` rather than over an abstract regular local ring converts an
apparent dependence on Serre's theorem into a hypothesis the caller already has.

**THE INDUCTION, on `dim Γ(X,U)_p`, and the mathlib pieces it uses.**
`IsIntegrallyClosed` is a local property (`Mathlib/RingTheory/LocalProperties/
IntegrallyClosed.lean`), so it suffices to treat a regular local `R` all of whose
localisations at primes are regular local.
* `dim R = 0`: `R` is a field, integrally closed.
* `dim R ≥ 1`: `𝔪 ≠ 𝔪²` by Nakayama, so pick `x ∈ 𝔪 ∖ 𝔪²`.  Then `R ⧸ (x)` is
  regular local (`isRegularLocalRing_quotient_span_singleton`, PROVEN in
  `Modularity/RegularStalks.lean`) hence a domain, so `(x)` is PRIME; it has
  height `1` (Krull's principal ideal theorem for `≤`, and `≥` because `R` is a
  domain), so `R_(x)` is a one-dimensional noetherian local domain whose maximal
  ideal is principal — a DVR, hence integrally closed.  And
  `R = R[1/x] ∩ R_(x)` inside `Frac R`: if `a = r/xⁿ` with `n` minimal and
  `a ∈ R_(x)` then `x ∣ r` because `x` is prime, contradicting minimality.  An
  intersection of two integrally closed subrings of `Frac R` is integrally
  closed, and `R[1/x]` is integrally closed because each of its localisations is
  `R_p` for a prime `p` not containing `x`, which has `ht p < ht 𝔪 = dim R` and
  is regular local, so the induction applies.

*Refute with:* `grep -rn "IsIntegrallyClosed" .lake/packages/mathlib/Mathlib/ |
grep -iE "regular|smooth|normal"` returning a THEOREM rather than prose, or a
hit for `IsNormalRing`, or a `Serre`/`CohenMacaulay` file appearing under
`Mathlib/RingTheory/`.  Any of those means this note has gone stale.

**Nonemptiness is a hypothesis and not decoration**: `Γ(X, ⊥)` is the zero ring,
whose `FractionRing` is also zero, and the consumer never needs the empty case —
`generalizingMap_of_isFinite_of_isIntegral` discharges it separately by the fact
that a subsingleton ring has no primes.

**STATUS 2026-07-27 — CUT.**  The geometry is now discharged
(`isRegularRing_sections_of_smooth` below), and everything above survives as the
route for the single ring-theoretic leaf `isIntegrallyClosed_of_isRegularRing`,
which is where the induction actually belongs.  What the cut BUYS is exactly the
paragraph above: `IsRegularRing` is mathlib's own class for "noetherian, and
every localisation at a prime is regular local", so the hypothesis "all the
localisations are regular" — the thing that replaces Serre's theorem — is
carried by the STATEMENT of the leaf rather than having to be threaded through
the induction by hand.

**STATUS 2026-07-27 — PROVEN**, over the seven-declaration tower immediately
below.  Two corrections to the route note above, both load-bearing:

1. **STACKS 030C IS NOT NEEDED.**  The warning recorded on
   `isIntegrallyClosed_sections_of_smooth` below — that `Γ(X,U)` need not be a
   domain, that every mathlib local-property tool for `IsIntegrallyClosed`
   carries `[IsDomain R]`, and that this leaf must therefore ALSO prove "a
   noetherian normal ring is a finite product of normal domains" — was right
   about the obstruction and wrong about the repair.  The finite-product
   decomposition is never used.  What replaces it is
   `isIntegrallyClosed_of_isIntegrallyClosed_localization_maximal` below, the
   ordinary Stacks 037C argument run with bare hands: for `x` integral over `R`
   the DENOMINATOR IDEAL `{r : r·x ∈ R}` is an ideal of `R` whatever `R` is, and
   it escapes every maximal ideal `m` because `R_m` is an integrally closed
   DOMAIN.  Only the LOCALIZATIONS are ever required to be domains — which they
   are here, being regular local — and `R` itself is never assumed to be one.
   That lemma is stated for an arbitrary `CommRing` and is reusable.
2. **THE INDUCTION IS ON THE EMBEDDING DIMENSION, and `A[1/x]` is what needs
   `IsRegularRing` rather than `IsRegularLocalRing`.**  In the inductive step the
   induction hypothesis is applied to `A_q` for primes `q` with `x ∉ q`, which
   are NOT quotients or sub-objects of `A` — so the class carrying "every
   localisation at a prime is regular local" has to travel with the ring.  It
   does: `isRegularRing_localization_of_isRegularRing` below is the prime
   correspondence and nothing more.

The tower, bottom-up:

* `isRegularRing_localization_of_isRegularRing` — a localization of a regular
  ring is regular.
* `exists_denominator_notMem_of_isIntegrallyClosed_atPrime` and
  `isIntegrallyClosed_of_isIntegrallyClosed_localization_maximal` — the
  domain-free local-to-global step (item 1).
* `isIntegrallyClosed_localization_atPrime_span_singleton` — `A_(x)` is
  integrally closed, because its maximal ideal is principal.
* `isIntegrallyClosed_localization_away_of_forall_atPrime` — `A[1/x]` is
  integrally closed as soon as every `A_q` with `x ∉ q` is.
* `exists_eq_of_pow_denominator` and
  `isIntegrallyClosed_of_away_of_atPrime_span_singleton` — `A = A[1/x] ∩ A_(x)`,
  by minimality of the exponent (`x` prime, `s ∉ (x)`).
* `isIntegrallyClosed_of_isRegularRing_of_isLocalRing_aux` — the induction. -/
theorem isRegularRing_localization_of_isRegularRing {R : Type u} [CommRing R]
    [IsRegularRing R] (M : Submonoid R) : IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro p hp
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl
      (Localization.AtPrime (p.comap (algebraMap R (Localization M))))
      (Localization.AtPrime p)).toRingEquiv

/-- **THE DENOMINATOR ESCAPES ONE MAXIMAL IDEAL** (**PROVEN 2026-07-27**), the
local half of the domain-free local-to-global step for `IsIntegrallyClosed`.

For `x` in the TOTAL RING OF FRACTIONS `K` of an arbitrary commutative ring `R`
and `m` maximal with `R_m` an integrally closed DOMAIN, some `r ∉ m` has
`r · x ∈ R`.  `R` itself is not assumed to be a domain anywhere.

THE PROOF is Stacks 037C.  `R⁰` lands in the nonzero elements of `R_m` — if
`s ∈ R⁰` died in `R_m` then `t·s = 0` for some `t ∉ m`, forcing `t = 0 ∈ m` —
so `K` maps to `Frac(R_m)`, and `x` maps to something integral over `R_m`,
hence into `R_m`.  Clearing that denominator inside `R_m` and then in `R`
(`IsLocalization.eq_iff_exists`) produces the witness. -/
theorem exists_denominator_notMem_of_isIntegrallyClosed_atPrime {R : Type u} [CommRing R]
    {K : Type u} [CommRing K] [Algebra R K] [IsFractionRing R K] (m : Ideal R)
    [hm : m.IsMaximal] [IsDomain (Localization.AtPrime m)]
    [IsIntegrallyClosed (Localization.AtPrime m)] {x : K} (hx : IsIntegral R x) :
    ∃ r : R, r ∉ m ∧ ∃ b : R, algebraMap R K b = algebraMap R K r * x := by
  classical
  set A := Localization.AtPrime m with hA
  set L := FractionRing A with hL
  set f : R →+* A := algebraMap R A with hf
  set g : A →+* L := algebraMap A L with hg
  have hginj : Function.Injective g := IsFractionRing.injective A L
  have hunits : ∀ y : nonZeroDivisors R, IsUnit ((g.comp f) y) := by
    rintro ⟨s, hs⟩
    have hne : f s ≠ 0 := by
      intro h
      rw [hf, IsLocalization.map_eq_zero_iff m.primeCompl] at h
      obtain ⟨⟨t, ht⟩, hts⟩ := h
      have h0 : t = 0 := (mem_nonZeroDivisors_iff.mp hs).2 t hts
      subst h0
      exact ht m.zero_mem
    exact IsLocalization.map_units L
      (⟨f s, mem_nonZeroDivisors_of_ne_zero hne⟩ : nonZeroDivisors A)
  set φ : K →+* L := IsLocalization.lift hunits with hφ
  have hφcomp : φ.comp (algebraMap R K) = g.comp f := IsLocalization.lift_comp hunits
  have hint : IsIntegral A (φ x) := by
    obtain ⟨p, hpm, hpx⟩ := hx
    refine ⟨p.map f, hpm.map f, ?_⟩
    rw [Polynomial.eval₂_map, ← hφcomp, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed A› hint
  obtain ⟨a, ⟨t, ht⟩, hyat⟩ := IsLocalization.exists_mk'_eq m.primeCompl y
  obtain ⟨c, ⟨s, hs⟩, hxcs⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  have h1 : φ x * (g.comp f) s = (g.comp f) c := by
    have hspec := IsLocalization.mk'_spec K c ⟨s, hs⟩
    rw [hxcs] at hspec
    calc φ x * (g.comp f) s = φ x * φ (algebraMap R K s) := by
          rw [← RingHom.comp_apply, hφcomp]
      _ = φ (x * algebraMap R K s) := by rw [map_mul]
      _ = φ (algebraMap R K c) := by rw [hspec]
      _ = (g.comp f) c := by rw [← RingHom.comp_apply, hφcomp]
  have h2 : g y * (g.comp f) t = (g.comp f) a := by
    have hspec := IsLocalization.mk'_spec A a ⟨t, ht⟩
    rw [hyat] at hspec
    calc g y * (g.comp f) t = g (y * algebraMap R A t) := by
          simp [RingHom.comp_apply, hg, hf]
      _ = g (algebraMap R A a) := by rw [hspec]
      _ = (g.comp f) a := rfl
  have h3 : (g.comp f) (a * s) = (g.comp f) (c * t) := by
    rw [map_mul, map_mul, ← h2, ← h1, hy]
    ring
  have h4 : f (a * s) = f (c * t) := hginj (by simpa [RingHom.comp_apply] using h3)
  obtain ⟨⟨u, hu⟩, hueq⟩ := (IsLocalization.eq_iff_exists m.primeCompl A).mp h4
  have hmp : m.IsPrime := hm.isPrime
  refine ⟨u * t, ?_, ⟨u * a, ?_⟩⟩
  · exact fun h => ((hmp.mem_or_mem h).elim hu ht)
  · have hsu : IsUnit (algebraMap R K s) := IsLocalization.map_units K ⟨s, hs⟩
    refine hsu.mul_left_cancel ?_
    have hR : u * (a * s) = u * (c * t) := by simpa using hueq
    have hxs : x * algebraMap R K s = algebraMap R K c := by
      rw [← hxcs]; exact IsLocalization.mk'_spec K c ⟨s, hs⟩
    calc algebraMap R K s * algebraMap R K (u * a)
        = algebraMap R K (u * (a * s)) := by rw [← map_mul]; ring_nf
      _ = algebraMap R K (u * (c * t)) := by rw [hR]
      _ = algebraMap R K (u * t) * algebraMap R K c := by rw [← map_mul]; ring_nf
      _ = algebraMap R K (u * t) * (x * algebraMap R K s) := by rw [hxs]
      _ = algebraMap R K s * (algebraMap R K (u * t) * x) := by ring

/-- **`IsIntegrallyClosed` IS LOCAL — WITHOUT A DOMAIN HYPOTHESIS ON `R`**
(**PROVEN 2026-07-27**; Stacks 034M/037C).

If `R_m` is an integrally closed DOMAIN for every maximal `m`, then `R` is
integrally closed in its total ring of fractions.  Mathlib's
`IsIntegrallyClosed.of_localization_maximal` needs `[IsDomain R]`; this does
not, and that is what removes the finite-product reduction (Stacks 030C) from
the route note above.

The whole content is that the denominator ideal `{r : r·x ∈ R}` is an ideal of
`R` with no hypotheses at all, and
`exists_denominator_notMem_of_isIntegrallyClosed_atPrime` says it is contained
in no maximal ideal. -/
theorem isIntegrallyClosed_of_isIntegrallyClosed_localization_maximal {R : Type u} [CommRing R]
    (hdom : ∀ (m : Ideal R) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    (hic : ∀ (m : Ideal R) [m.IsMaximal], IsIntegrallyClosed (Localization.AtPrime m)) :
    IsIntegrallyClosed R := by
  classical
  have main : ∀ x : FractionRing R, IsIntegral R x →
      ∃ y : R, algebraMap R (FractionRing R) y = x := by
    intro x hx
    let K := FractionRing R
    let I : Ideal R :=
      { carrier := {r : R | ∃ b : R, algebraMap R K b = algebraMap R K r * x}
        add_mem' := by
          rintro p q ⟨u, hu⟩ ⟨v, hv⟩
          exact ⟨u + v, by rw [map_add, hu, hv, map_add]; ring⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c p ⟨u, hu⟩
          exact ⟨c * u, by rw [map_mul, hu, smul_eq_mul, map_mul]; ring⟩ }
    have hItop : I = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
      haveI := hm
      haveI := hdom m
      haveI := hic m
      obtain ⟨r, hrm, b, hb⟩ :=
        exists_denominator_notMem_of_isIntegrallyClosed_atPrime (K := K) m hx
      exact hrm (hIm (show r ∈ I from ⟨b, hb⟩))
    obtain ⟨b, hb⟩ : (1 : R) ∈ I := hItop ▸ Submodule.mem_top
    exact ⟨b, by simpa using hb⟩
  exact (isIntegrallyClosedIn_iff (R := R) (A := FractionRing R)).mpr
    ⟨IsLocalization.injective _ le_rfl, fun {x} hx => main x hx⟩

/-- **`A_(x)` IS INTEGRALLY CLOSED WHEN `(x)` IS PRIME** (**PROVEN 2026-07-27**).

A noetherian local domain whose maximal ideal is PRINCIPAL is integrally closed
— mathlib's `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, items 4 ⟹ 3.
Note this needs no dimension count: the `IsField` case is covered by the same
TFAE, so `x = 0` is allowed and no `x ≠ 0` hypothesis appears. -/
theorem isIntegrallyClosed_localization_atPrime_span_singleton {A : Type u} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] {x : A} [hP : (Ideal.span {x} : Ideal A).IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime (Ideal.span {x} : Ideal A)) := by
  haveI : IsDomain (Localization.AtPrime (Ideal.span {x} : Ideal A)) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have hprinc :
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {x} : Ideal A))).IsPrincipal := by
    refine ⟨⟨algebraMap A _ x, ?_⟩⟩
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have key : IsIntegrallyClosed (Localization.AtPrime (Ideal.span {x} : Ideal A)) ∧
      ∀ P : Ideal (Localization.AtPrime (Ideal.span {x} : Ideal A)), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {x} : Ideal A)) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime (Ideal.span {x} : Ideal A))).out 4 3).mp hprinc
  exact key.1

/-- **`A[1/x]` IS INTEGRALLY CLOSED IF EVERY `A_q` WITH `x ∉ q` IS**
(**PROVEN 2026-07-27**).

`A[1/x]` IS a domain, so mathlib's `IsIntegrallyClosed.of_localization_maximal`
applies to it; and its primes are exactly the primes of `A` missing `x`, by
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`. -/
theorem isIntegrallyClosed_localization_away_of_forall_atPrime {A : Type u} [CommRing A]
    [IsDomain A] {x : A} (hx0 : x ≠ 0)
    (h : ∀ (q : Ideal A) [q.IsPrime], x ∉ q → IsIntegrallyClosed (Localization.AtPrime q)) :
    IsIntegrallyClosed (Localization.Away x) := by
  classical
  have hpow : Submonoid.powers x ≤ nonZeroDivisors A := by
    rintro y ⟨k, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_of_ne_zero hx0) k
  haveI : IsDomain (Localization.Away x) := IsLocalization.isDomain_localization hpow
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p hp0 hpmax
  haveI : (p.comap (algebraMap A (Localization.Away x))).IsPrime := Ideal.IsPrime.comap _
  have hxq : x ∉ p.comap (algebraMap A (Localization.Away x)) := by
    intro hmem
    have hunit : IsUnit (algebraMap A (Localization.Away x) x) :=
      IsLocalization.map_units _ (⟨x, Submonoid.mem_powers x⟩ : Submonoid.powers x)
    exact hpmax.ne_top (p.eq_top_of_isUnit_mem hmem hunit)
  exact (h _ hxq).of_equiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers x) p).toRingEquiv

/-- **CLEARING A POWER OF A PRIME `x` AGAINST A DENOMINATOR PRIME TO IT**
(**PROVEN 2026-07-27**) — the arithmetic core of `A = A[1/x] ∩ A_(x)`.

If `z = a/s` with `s ∉ (x)` and also `z = b/xᵏ`, then `b·s = xᵏ·a`, so `x ∣ b`
whenever `k ≥ 1`, and the exponent drops.  Induction on `k` ends at `z = b ∈ A`.
This is exactly the "`n` minimal" step of the classical proof, written as a
descent rather than as a well-ordering argument. -/
theorem exists_eq_of_pow_denominator {A : Type u} [CommRing A] [IsDomain A] {K : Type u}
    [Field K] [Algebra A K] [IsFractionRing A K] {x : A} (hx : Prime x) {z : K} {a s : A}
    (hs : s ∉ Ideal.span {x}) (hzs : algebraMap A K a = z * algebraMap A K s) :
    ∀ (k : ℕ) (b : A), algebraMap A K b = z * algebraMap A K (x ^ k) →
      ∃ y : A, algebraMap A K y = z := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  intro k
  induction k with
  | zero => intro b hb; exact ⟨b, by simpa using hb⟩
  | succ k ihk =>
      intro b hb
      have key : b * s = x ^ (k + 1) * a := by
        apply hinj
        rw [map_mul, map_mul, hb, hzs]
        ring
      have hxb : x ∣ b := by
        have hdvd : x ∣ b * s := ⟨x ^ k * a, by rw [key]; ring⟩
        rcases hx.dvd_mul.mp hdvd with hh | hh
        · exact hh
        · exact absurd (Ideal.mem_span_singleton.mpr hh) hs
      obtain ⟨b', rfl⟩ := hxb
      refine ihk b' ?_
      have hxne : algebraMap A K x ≠ 0 := fun hcon =>
        hx.ne_zero (hinj (by rw [hcon, map_zero]))
      refine mul_left_cancel₀ hxne ?_
      calc algebraMap A K x * algebraMap A K b' = algebraMap A K (x * b') := (map_mul _ _ _).symm
        _ = z * algebraMap A K (x ^ (k + 1)) := hb
        _ = algebraMap A K x * (z * algebraMap A K (x ^ k)) := by rw [map_pow, map_pow]; ring

/-- **`A = A[1/x] ∩ A_(x)` FOR A PRIME ELEMENT `x`** (**PROVEN 2026-07-27**).

Both halves are integrally closed with the SAME fraction field `Frac A`
(`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`), so an element
integral over `A` lands in both, and `exists_eq_of_pow_denominator` intersects
them. -/
theorem isIntegrallyClosed_of_away_of_atPrime_span_singleton {A : Type u} [CommRing A]
    [IsDomain A] {x : A} (hx0 : x ≠ 0) [hP : (Ideal.span {x} : Ideal A).IsPrime]
    (h1 : IsIntegrallyClosed (Localization.Away x))
    (h2 : IsIntegrallyClosed (Localization.AtPrime (Ideal.span {x} : Ideal A))) :
    IsIntegrallyClosed A := by
  classical
  have hxprime : Prime x := (Ideal.span_singleton_prime hx0).mp hP
  have hpow : Submonoid.powers x ≤ nonZeroDivisors A := by
    rintro y ⟨k, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_of_ne_zero hx0) k
  letI : Algebra (Localization.Away x) (FractionRing A) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _
      (Submonoid.powers x) (nonZeroDivisors A) hpow
  haveI : IsScalarTower A (Localization.Away x) (FractionRing A) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _
      (Submonoid.powers x) (nonZeroDivisors A) hpow
  haveI : IsFractionRing (Localization.Away x) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers x) _ _
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr ?_
  intro z hz
  obtain ⟨yB, hyB⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp h2
    (hz.tower_top (A := Localization.AtPrime (Ideal.span {x} : Ideal A)))
  obtain ⟨a, ⟨s, hs⟩, hyB'⟩ :=
    IsLocalization.exists_mk'_eq (Ideal.span {x} : Ideal A).primeCompl yB
  have hBrel : algebraMap A (FractionRing A) a = z * algebraMap A (FractionRing A) s := by
    have hspec := IsLocalization.mk'_spec
      (Localization.AtPrime (Ideal.span {x} : Ideal A)) a ⟨s, hs⟩
    rw [hyB'] at hspec
    have hmap := congrArg (algebraMap (Localization.AtPrime (Ideal.span {x} : Ideal A))
      (FractionRing A)) hspec
    rw [map_mul, hyB, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply] at hmap
    exact hmap.symm
  obtain ⟨w, hw⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp h1
    (hz.tower_top (A := Localization.Away x))
  obtain ⟨b, t, hw'⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) w
  obtain ⟨k, hk⟩ := t.2
  have hCrel : algebraMap A (FractionRing A) b = z * algebraMap A (FractionRing A) (x ^ k) := by
    have hspec := IsLocalization.mk'_spec (Localization.Away x) b t
    rw [hw'] at hspec
    have hmap := congrArg (algebraMap (Localization.Away x) (FractionRing A)) hspec
    rw [map_mul, hw, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply] at hmap
    rw [← hk] at hmap
    exact hmap.symm
  exact exists_eq_of_pow_denominator hxprime hs hBrel k b hCrel

/-- **A REGULAR LOCAL RING IS INTEGRALLY CLOSED, BY INDUCTION ON THE EMBEDDING
DIMENSION** (**PROVEN 2026-07-27**) — the Serre-free induction the route note
above describes, and the one place `IsRegularRing` (rather than
`IsRegularLocalRing`) is genuinely needed.

`d = 0`: `A` is a field.  `d = m+1`: `𝔪 ⊄ 𝔪²` by Nakayama, so pick
`x ∈ 𝔪 ∖ 𝔪²`; `A ⧸ (x)` is regular local
(`isRegularLocalRing_quotient_span_singleton`) hence a domain
(`isDomain_of_isRegularLocalRing`), so `(x)` is PRIME.  Then `A_(x)` is
integrally closed because its maximal ideal is principal, and `A[1/x]` because
every `A_q` with `x ∉ q` has `ht q < ht 𝔪` — `Ideal.height_strict_mono_of_isPrime_of_isPrime`
against `IsLocalization.AtPrime.ringKrullDim_eq_height` and
`IsRegularLocalRing.spanFinrank_maximalIdeal` — so the induction hypothesis
applies to it.  `A = A[1/x] ∩ A_(x)` finishes.

NOTE the induction quantifies over the RING, like
`isDomain_of_isRegularLocalRing_aux`, because `A_q` is a different ring; and it
is `≤ n` rather than `= n` so that the final instantiation is `le_rfl`. -/
theorem isIntegrallyClosed_of_isRegularRing_of_isLocalRing_aux (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsRegularRing A],
      (IsLocalRing.maximalIdeal A).spanFinrank ≤ n → IsIntegrallyClosed A := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ _ hle
    haveI : IsRegularLocalRing A := IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
    haveI : IsDomain A := GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing A
    by_cases hfield : IsField A
    · letI := hfield.toField
      infer_instance
    · have hbot : IsLocalRing.maximalIdeal A ≠ ⊥ := fun hb =>
        hfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)
      have hm2 : ¬ (IsLocalRing.maximalIdeal A ≤ (IsLocalRing.maximalIdeal A) ^ 2) := by
        intro hsub
        refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal A) _ (IsNoetherian.noetherian _) ?_ ?_)
        · rwa [smul_eq_mul, ← pow_two]
        · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      obtain ⟨x, hxm, hx2⟩ := SetLike.not_le_iff_exists.mp hm2
      have hx0 : x ≠ 0 := fun hz => hx2 (by rw [hz]; exact Submodule.zero_mem _)
      haveI : IsRegularLocalRing (A ⧸ Ideal.span {x}) :=
        GaloisRepresentation.Modularity.isRegularLocalRing_quotient_span_singleton hxm hx2
      haveI : IsDomain (A ⧸ Ideal.span {x}) :=
        GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
      haveI hPprime : (Ideal.span {x} : Ideal A).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
      have h2 : IsIntegrallyClosed (Localization.AtPrime (Ideal.span {x} : Ideal A)) :=
        isIntegrallyClosed_localization_atPrime_span_singleton
      have h1 : IsIntegrallyClosed (Localization.Away x) := by
        refine isIntegrallyClosed_localization_away_of_forall_atPrime hx0 ?_
        intro q _ hxq
        have hqlt : q < IsLocalRing.maximalIdeal A := by
          refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') ?_
          rintro rfl
          exact hxq hxm
        haveI : IsRegularRing (Localization.AtPrime q) :=
          isRegularRing_localization_of_isRegularRing q.primeCompl
        haveI : IsRegularLocalRing (Localization.AtPrime q) :=
          IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
        have he : (((IsLocalRing.maximalIdeal A).spanFinrank : ℕ) : WithBot ℕ∞)
            = (((IsLocalRing.maximalIdeal A).height : ℕ∞) : WithBot ℕ∞) := by
          rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
            IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
        have hdq : (((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : ℕ) :
              WithBot ℕ∞) = ((q.height : ℕ∞) : WithBot ℕ∞) := by
          rw [IsRegularLocalRing.spanFinrank_maximalIdeal,
            IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
        have hlt : q.height < (IsLocalRing.maximalIdeal A).height :=
          Ideal.height_strict_mono_of_isPrime_of_isPrime hqlt
        have hcast : (((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : ℕ) :
              WithBot ℕ∞)
            < (((IsLocalRing.maximalIdeal A).spanFinrank : ℕ) : WithBot ℕ∞) := by
          rw [hdq, he]
          exact_mod_cast hlt
        have hnat : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank
            < (IsLocalRing.maximalIdeal A).spanFinrank := by exact_mod_cast hcast
        exact ih _ (lt_of_lt_of_le hnat hle) (Localization.AtPrime q) le_rfl
      exact isIntegrallyClosed_of_away_of_atPrime_span_singleton hx0 h1 h2

theorem isIntegrallyClosed_of_isRegularRing (R : Type u) [CommRing R] [IsRegularRing R] :
    IsIntegrallyClosed R := by
  refine isIntegrallyClosed_of_isIntegrallyClosed_localization_maximal ?_ ?_
  · intro m _
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
  · intro m _
    haveI : IsRegularRing (Localization.AtPrime m) :=
      isRegularRing_localization_of_isRegularRing m.primeCompl
    exact isIntegrallyClosed_of_isRegularRing_of_isLocalRing_aux
      (IsLocalRing.maximalIdeal (Localization.AtPrime m)).spanFinrank _ le_rfl

/-- **THE SECTIONS OVER AN AFFINE OPEN OF A SMOOTH SCHEME OVER A FIELD FORM A
REGULAR RING** (**PROVEN 2026-07-27** — this is the whole GEOMETRIC content of
`isIntegrallyClosed_sections_of_smooth` below, and it is four lines).

`IsRegularRing R` is mathlib's class (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`)
for "`R` is noetherian and `Localization.AtPrime p` is regular local for every
prime `p`".  Both halves come for free here:

* noetherian, because `Smooth g` is locally of finite type and `Spec K` is
  noetherian (`LocallyOfFiniteType.isLocallyNoetherian`, then
  `IsLocallyNoetherian.component_noetherian`);
* regular local, because the localisation of `Γ(X,U)` at a prime `P` IS the
  stalk of `X` at the corresponding point `hU.fromSpec ⟨P, hP⟩`
  (`IsAffineOpen.isLocalization_stalk'`), and every stalk of a smooth scheme over
  a field is regular local (`isRegularLocalRing_stalk_of_smooth` above).
  `IsRegularLocalRing.of_ringEquiv` transports along the uniqueness-of-localisation
  equivalence `IsLocalization.algEquiv`.

**THIS IS WHY THE GEOMETRIC STATEMENT OF THE LEAF WAS THE RIGHT ONE.**  The route
note on `isIntegrallyClosed_of_isRegularRing` above explains that the induction
must know the localisations are regular, which for an ABSTRACT regular local ring
is Serre's theorem and is absent from the pin.  Stating the leaf over `Γ(X,U)`
made that hypothesis free — and `IsRegularRing` is precisely the class that
packages it, so the geometry and the algebra separate cleanly here and nowhere
else. -/
theorem isRegularRing_sections_of_smooth {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] (U : X.affineOpens) :
    IsRegularRing Γ(X, U.1) := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) := by
    rw [isLocallyNoetherian_Spec]; infer_instance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  rw [isRegularRing_iff]
  intro P hP
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk (U.2.fromSpec ⟨P, hP⟩)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec ⟨P, hP⟩)) P :=
    U.2.isLocalization_stalk' ⟨P, hP⟩ (U.2.isoSpec.inv _).2
  haveI := isRegularLocalRing_stalk_of_smooth g (U.2.fromSpec ⟨P, hP⟩)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (U.2.fromSpec ⟨P, hP⟩)) (Localization.AtPrime P)).toRingEquiv

/-- **A REGULAR LOCAL RING IS INTEGRALLY CLOSED, IN THE FORM THIS DEVELOPMENT
NEEDS IT** (**PROVEN 2026-07-27** over the single ring-theoretic leaf
`isIntegrallyClosed_of_isRegularRing` above, via
`isRegularRing_sections_of_smooth` immediately above; created as a sorry leaf
earlier the same day).

`Γ(X, U)` is integrally closed for every nonempty affine open `U` of a scheme
smooth over a field.

**`_hU` IS NOW UNUSED, and that is not an oversight.**  The nonemptiness
hypothesis was recorded because `Γ(X, ⊥)` is the zero ring; but the zero ring is
integrally closed in its (zero) fraction ring, and `IsRegularRing` of it holds
vacuously — it has no primes — so the empty case needs no exception.  The
hypothesis is kept in the signature because the consumer
`hasGoingDown_stalkMap_of_isFinite_endo` supplies it and removing it would be a
gratuitous signature change; it is underscore-prefixed so the emptiness of its
role is mechanically visible.

**WHERE THE REMAINING DIFFICULTY LIVES, and it is NOT only the induction.**
`Γ(X,U)` need NOT be a domain: nothing here assumes `X` connected, and `U` may be
a disjoint union of affines, making `Γ(X,U)` a finite PRODUCT of normal domains.
Mathlib's local-property machinery for `IsIntegrallyClosed`
(`IsIntegrallyClosed.of_isLocalization_maximal`,
`Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean`) all carries
`[IsDomain R]`, so `isIntegrallyClosed_of_isRegularRing` must ALSO handle the
product case (Stacks 030C: a noetherian normal ring is a finite product of normal
domains, and such a ring is integrally closed in its total ring of fractions).
Whoever proves that leaf should plan for two halves — the domain induction, and
the reduction of the general case to it — rather than only the first.

**CORRECTION 2026-07-27, when that leaf was PROVEN: the OBSTRUCTION above is
real, the PROPOSED REPAIR is not.**  `Γ(X,U)` really need not be a domain and
mathlib's local-property tools for `IsIntegrallyClosed` really do all carry
`[IsDomain R]` — but STACKS 030C IS NOT NEEDED, and no finite-product
decomposition appears anywhere in the finished proof.  The reduction is instead
`isIntegrallyClosed_of_isIntegrallyClosed_localization_maximal` above: the
DENOMINATOR IDEAL `{r : r·x ∈ R}` of an element `x` integral over `R` is an
ideal for an arbitrary commutative `R`, and it escapes every maximal ideal `m`
purely because `R_m` is an integrally closed DOMAIN.  Only the localizations
have to be domains; `R` never does.  So the two halves are "the domain
induction" and "one twenty-line local-to-global lemma", not "the domain
induction" and "Stacks 030C" — an estimate that was wrong by about an order of
magnitude, in the direction of pessimism. -/
theorem isIntegrallyClosed_sections_of_smooth {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] (U : X.affineOpens) (_hU : Nonempty ↥U.1) :
    IsIntegrallyClosed Γ(X, U.1) :=
  haveI := isRegularRing_sections_of_smooth g U
  isIntegrallyClosed_of_isRegularRing _

/-- **GOING-DOWN FOR THE STALK MAP OF A FINITE ENDOMORPHISM OF A SMOOTH
PROPER GEOMETRICALLY CONNECTED SCHEME OVER A FIELD** (**PROVEN 2026-07-27** over
the three leaves in the block immediately above; created as a sorry leaf earlier
the same day.  Its consumer is `ringKrullDim_stalk_eq_of_isFinite_endo` below,
which is proven over it.  General scheme theory, NO abelian varieties, no group
law, no `[n]`.)

`u.stalkMap x : 𝒪_{X,u x} ⟶ 𝒪_{X,x}` satisfies going-down: every chain of
primes below `𝔪_{u x}` lifts to a chain below `𝔪_x`.

**WHY THIS IS THE RIGHT CUT.**  Its consumer needs the two-sided height
identity across a `LiesOver` pair.  The `≤` half of that identity —
`dim 𝒪_{X,x} ≤ dim 𝒪_{X,u x}` — is Stacks 00OM
(`Ideal.height_le_height_add_of_liesOver`) and costs nothing, given that the
fibre is zero-dimensional (`ringKrullDim_quotient_map_maximalIdeal_stalkMap`,
already proven).  Going-down is the ONLY hypothesis that upgrades it to the
equality (Stacks 00ON, Matsumura 13.B Th. 19(2)), so it carries the whole of
the remaining mathematics and nothing else does.

**THE ROUTE, and it does NOT use flatness** — using flatness would be
circular, since the node this whole block serves
(`flat_of_finite_fibres_endo`) exists to PROVE flatness.  Krull's going-down
theorem for integrally closed domains is in the pin as an INSTANCE,
`Mathlib/RingTheory/IntegralClosure/GoingDown.lean` (`@[stacks 00H8]`):

    [IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R]
      → Algebra.HasGoingDown R S

so the proof must supply those four for a suitable pair, and then transport
going-down to the stalks.  **The transport is why the pair cannot be the
stalks themselves**: `Algebra.IsIntegral 𝒪_{X,u x} 𝒪_{X,x}` is FALSE in
general — the stalk map of a finite morphism is not even module-finite, see
the counterexample `Spec ℤ[i] ⟶ Spec ℤ` at `(5)` written out on
`ringKrullDim_quotient_map_maximalIdeal_stalkMap` above.  The four hypotheses
hold on an AFFINE CHART: choose affine `V ∋ u x`; `u` finite is affine, so
`U = u ⁻¹ᵁ V` is affine and `B = Γ(U)` is a finite — hence integral —
`A = Γ(V)`-algebra, and `𝒪_{X,x} = B_q`, `𝒪_{X,u x} = A_p` by
`IsAffineOpen.isLocalization_stalk`.  Going-down then descends to the
localisations, because it is a statement about chains of primes below `q` and
below `p`, which the localisation maps identify.

**THE FOUR INPUTS, and what each hypothesis of this leaf is for.**

1. `Algebra.IsIntegral A B` — from `[IsFinite u]`, on the chart.
2. `IsDomain B` and `FaithfulSMul A B` — from `X` being INTEGRAL and `u`
   DOMINANT.  Integrality is steps 1–2 of the survey on the consumer below:
   `Smooth g` over a field makes every stalk regular local hence a domain
   (`isRegularLocalRing_stalk_of_smooth` above, now PROVEN, plus
   `GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`), so `X`
   is locally irreducible; `GeometricallyConnected g` makes it connected; and
   a connected, locally noetherian, locally irreducible scheme is
   irreducible.  Dominance of `u` is where `IsProper g` is used: `X` is then
   quasi-compact and of finite type over `K`, hence finite-dimensional, and a
   finite morphism preserves the dimension of a closed subset, so `u '' X`
   closed irreducible of full dimension forces `u '' X = X`.
3. `IsIntegrallyClosed A` — **the one piece of commutative algebra that is
   absent everywhere** (mathlib, this project and `~/cs/FLT`): *a regular
   local ring is integrally closed*, applied at every localisation of `A` via
   `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean`.  There is no
   `IsNormalRing` class in the pin at all.
   *Refute with:* `grep -rn "IsIntegrallyClosed" .lake/packages/mathlib/Mathlib/
   | grep -i "regular\|smooth\|normal"` returning a theorem rather than prose.

**STATUS 2026-07-27 — PROVEN, AND THE ROUTE ABOVE IS CORRECTED IN ONE PLACE.**
The plan above is what was carried out, except that the step it called the
hardest — "and then transport going-down to the stalks" — is NOT done by
transporting `Algebra.HasGoingDown A B` along the localisations `A → A_p`,
`B → B_q`.  It is done by restating going down TOPOLOGICALLY.  Mathlib's
`Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap` (`@[stacks 00HW]`)
identifies going down with `GeneralizingMap` on `Spec`, and `GeneralizingMap` is
local on source and target for free, because opens are stable under
generalization — `topologically GeneralizingMap` carries
`IsZariskiLocalAtSource` and `IsZariskiLocalAtTarget` instances in
`Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean`.  So the affine-chart
statement IS the local statement, and no localisation bookkeeping arises at all.
The two halves are:

* `generalizingMap_of_isFinite_of_isIntegral` above — Krull's theorem descended
  to schemes, giving `GeneralizingMap u.base`;
* `hasGoingDown_stalkMap_of_generalizingMap` above — the converse transport, from
  `GeneralizingMap f.base` back to going down for EVERY stalk map, via
  `Scheme.range_fromSpecStalk` (`@[stacks 01J7]`) and the fact that
  `Spec 𝒪_{X,x} ⟶ X` is a preimmersion.

The `A WEAKER STATEMENT THAT WOULD ALSO SERVE` paragraph that stood here — a
fallback through `ringKrullDim_stalk_eq_coheight` — is therefore RETIRED, and it
is worth saying why, because it was recorded as the escape hatch if the main
route stalled.  It is not an escape hatch: it turns both sides into
`Order.coheight` and the statement into "`u` lifts chains of generalisations",
which is going down again, topologically.  The topological restatement is
genuinely the right move, but it BUYS THE LOCALITY, not the mathematics: the
mathematical content stays exactly where it was, in Krull's theorem, and hence
in normality.

**WHAT REMAINS OPEN, and it is all in the leaves above, none of it here.**
Normality of the charts (`isIntegrallyClosed_sections_of_smooth`) is the only
commutative algebra; irreducibility of `X`
(`irreducibleSpace_of_smooth_geometricallyConnected`) and dominance of `u`
(`isDominant_of_isFinite_endo`) are the two geometric inputs, and they are steps
1 and 2 of the survey on the consumer below, stated as their own leaves so that
they can be attacked independently.

**UPDATE 2026-07-27 (second pass): ALL THREE OF THOSE ARE NOW PROVEN**, and the
open frontier under this declaration is instead the leaves they were cut
over — `height_map_le_of_isFinite` and `isIntegrallyClosed_of_isRegularRing`
(the third, `topologicalKrullDim_lt_top_of_isProper`, was PROVEN later the same
day).  Read the block header above for what
each of them is.  Note in particular that irreducibility turned out NOT to need
the disjoint-components argument predicted here: see
`irreducibleSpace_of_connected_of_isDomain_stalk`. -/
theorem hasGoingDown_stalkMap_of_isFinite_endo {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsFinite u] (x : X) :
    @Algebra.HasGoingDown (X.presheaf.stalk (u x)) (X.presheaf.stalk x) _ _
      (u.stalkMap x).hom.toAlgebra := by
  haveI : AlgebraicGeometry.IsIntegral X := isIntegral_of_smooth_geometricallyConnected g
  haveI : IsDominant u := isDominant_of_isFinite_endo g u
  exact hasGoingDown_stalkMap_of_generalizingMap u
    (generalizingMap_of_isFinite_of_isIntegral u
      (fun U hU => isIntegrallyClosed_sections_of_smooth g U hU)) x

/-- **A FINITE ENDOMORPHISM PRESERVES THE DIMENSION OF EVERY LOCAL RING**
(**PROVEN 2026-07-27** over the single leaf
`hasGoingDown_stalkMap_of_isFinite_endo` immediately above — general scheme
theory over a field, NO abelian varieties, no group law, no `[n]`.)

**SIGNATURE REPAIRED 2026-07-27 — this leaf was FALSE AS STATED until then.**
It used to bind `{K : CommRingCat.{u}} [Field K]` with `(g : X ⟶ Spec K)`,
which constrains the ring structure `Spec K` is built from **not at all**; the
`ZMod 4` counterexample in the FALSITY AUDIT of
`isRegularLocalRing_stalk_of_smooth` above refutes it verbatim, since with
`X = Spec K` and `u = 𝟙` step 1 of the route below already fails (the stalk
`ZMod 4` is not a domain, so `X` is not irreducible).  The statement now binds
`{K : Type u} [Field K]` with `Spec (CommRingCat.of K)`, so `g` really is a
morphism to the spectrum of a FIELD and the route below is sound.  Everything
that follows describes the repaired statement.

For `X` smooth, proper and geometrically connected over a field and `u` a
FINITE endomorphism of `X`, `dim 𝒪_{X,x} = dim 𝒪_{X,u x}` for every `x`.

**ROUTE, in the order the hypotheses are used.**

1. *`X` is irreducible.*  `Smooth g` over a field makes every stalk regular
   local, hence a domain, so `X` is locally irreducible;
   `GeometricallyConnected g` makes it connected; a connected, locally
   noetherian, locally irreducible scheme is irreducible.  Only ORDINARY
   connectedness is used, so this hypothesis may be weakened freely — it is
   `GeometricallyConnected` merely because that is what the caller has in hand
   (`AbelianSchemeStruct.connected`).
2. *`u` is surjective.*  `IsProper g` makes `X` quasi-compact and of finite
   type over the field, hence finite-dimensional.  A finite morphism preserves
   the dimension of a closed subset, so `u '' X` is a closed irreducible subset
   of `X` of the full dimension `dim X`; in an irreducible finite-dimensional
   scheme of finite type over a field the only such subset is `X`.
3. *The dimension formula.*  On an irreducible scheme of finite type over a
   field, `dim 𝒪_{X,x} = dim X - dim (closure {x})`.  Since `u` is finite,
   `dim (closure {x}) = dim (closure {u x})`, and the two local dimensions
   agree.

**WHAT IS MISSING, with the greps that would refute it** (re-run 2026-07-27
against `.lake/packages/mathlib`).  Mathlib has the RING-level dimension
theory — `ringKrullDim`, `Ideal.height`, `Module.supportDim`,
`topologicalKrullDim`, and the dimension-drop lemmas in
`RingTheory/KrullDimension/Regular.lean` — but essentially NO scheme-level
dimension theory: `ls Mathlib/AlgebraicGeometry/` shows no `Dimension.lean`,
and `grep -rn "dim" Mathlib/AlgebraicGeometry/` turns up nothing that proves
step 3.  Step 3 is the classical `dim 𝒪_{X,x} + dim closure{x} = dim X`
(Matsumura 5.6 / EGA IV 5.2.3) and it, not steps 1–2, is the real content of
this leaf.  A hit on a scheme-dimension file means this note has gone stale
and the leaf is far cheaper than it looks.

**THAT SURVEY IS NOW REFUTED, ON EXACTLY THE TERMS IT SET (2026-07-27).  STEP 3
IS NOT NEEDED AT ALL, AND THE ROUTE BELOW USES NO SCHEME DIMENSION THEORY.**
The grep that missed it was `grep -rn "dim" Mathlib/AlgebraicGeometry/`: the
scheme-level statement is stated in terms of `Order.coheight`, and `coheight`
does not contain the substring `dim`.  Every name below was located and read on
2026-07-27; each line ends with the check that would refute it.

1. **`ringKrullDim (X.presheaf.stalk x) = Order.coheight x`** — this exists, as
   `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, `@[stacks 02IZ]`, in
   `Mathlib/AlgebraicGeometry/Properties.lean` (with the affine case
   `idealHeight_eq_coheight` just above it).  So both sides of this leaf are
   ideal HEIGHTS, and the whole question is a statement about heights of primes
   under a module-finite ring extension.
   *Refute with:* `grep -n ringKrullDim_stalk_eq_coheight
   .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Properties.lean`.
2. **`height q ≤ height p + height (q in the fibre)`** is FREE — no going-down,
   no normality: `Ideal.height_le_height_add_of_liesOver`, `@[stacks 00OM]`,
   `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`.  Combined with the fibre
   being zero-dimensional — which is now PROVEN, as
   `ringKrullDim_quotient_map_maximalIdeal_stalkMap` above — this gives
   `dim 𝒪_{X,x} ≤ dim 𝒪_{X,u x}` outright.  **Half of this leaf costs nothing.**
3. **The reverse inequality is `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`**,
   `@[stacks 00ON]`, Matsumura 13.B Th. 19(2), same file, which upgrades step 2
   to an EQUALITY given `[Algebra.HasGoingDown A B]`.
4. **Going-down is available from NORMALITY, not from flatness** (using flatness
   would be circular — this leaf exists to prove flatness).  Krull's going-down
   theorem is in the pin as an INSTANCE:
   `Mathlib/RingTheory/IntegralClosure/GoingDown.lean:48`, `@[stacks 00H8]`,
   `[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R] →
   Algebra.HasGoingDown R S`.  `u` finite gives `Algebra.IsIntegral`; `X`
   integral gives `IsDomain` and injectivity.
   *Refute with:* `grep -n "stacks 00H8"
   .lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/GoingDown.lean`.

**SO THE WHOLE LEAF NOW RESTS ON ONE PIECE OF COMMUTATIVE ALGEBRA:**

> **a regular local ring is integrally closed** (regular ⟹ normal),

which is what supplies `[IsIntegrallyClosed A]` for `A = Γ(V)` on an affine
chart of the smooth `X`.  That is absent from mathlib — `grep -rn
IsIntegrallyClosed Mathlib/ | grep -i "regular\|smooth\|normal"` returns only
prose in `IntegralClosure/IntegrallyClosed.lean`, and there is no `IsNormalRing`
class at all — and absent from this project and from `~/cs/FLT`.  But it is a
STANDARD, SELF-CONTAINED, MATHLIB-SHAPED statement, and it is enormously smaller
than "a dimension theory of schemes".  Mathlib even provides the localisation
step for it: `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` lets
`IsIntegrallyClosed A` be checked at the localisations of `A`.

**UPDATE 2026-07-27: it is now a NAMED LEAF, `isIntegrallyClosed_sections_of_smooth`
above**, stated geometrically (`IsIntegrallyClosed Γ(X,U)` for `U` a nonempty
affine open) rather than as the abstract "regular local ⟹ integrally closed".
That is not cosmetic: the abstract form's induction needs *localisation of a
regular local ring is regular local*, which is Serre's theorem and is missing
from the pin, whereas the geometric form gets it free from
`isRegularLocalRing_stalk_of_smooth`.  Its docstring carries the induction in
full.  Steps 1 and 2 of the survey above are likewise now named leaves
(`irreducibleSpace_of_smooth_geometricallyConnected`,
`isDominant_of_isFinite_endo`), and everything else between them and this
theorem is proven.

**FURTHER UPDATE, same day: all three of those leaves are PROVEN.**  The
commutative algebra now sits in `isIntegrallyClosed_of_isRegularRing` (a REGULAR
RING — mathlib's `IsRegularRing`, i.e. noetherian with all localisations regular
local — is integrally closed), reached from the geometry by the proven
`isRegularRing_sections_of_smooth`.  Moving the hypothesis into the class is what
keeps the Serre-free character of the geometric statement while restoring a
mathlib-shaped leaf.  The dimension theory that step 2 needed did NOT go away: it
is `topologicalKrullDim_lt_top_of_isProper` together with
`height_map_le_of_isFinite` (Cohen–Seidenberg), which is far less than "a
dimension theory of schemes" but is not nothing.  (The first of those is now
PROVEN, 2026-07-27, and NOT over Noether normalisation as this sentence
originally said — a surjection from a polynomial ring plus
`MvPolynomial.ringKrullDim_of_isNoetherianRing` is enough when only finiteness
is wanted.)

Note this route ALSO discards steps 1–3 of the survey above: irreducibility is
still wanted (to make the charts domains), but SURJECTIVITY of `u` is not used,
and neither is `dim 𝒪_{X,x} + dim closure{x} = dim X`.

**STATUS 2026-07-27 — PROVEN, over the SINGLE leaf
`hasGoingDown_stalkMap_of_isFinite_endo` immediately above, and the signature
is REPAIRED.**  Two changes landed together:

* The binder is now `{K : Type u} [Field K]` with base
  `Spec (CommRingCat.of K)`.  Under the old `{K : CommRingCat.{u}} [Field K]`
  the field structure was a class on the CARRIER TYPE and constrained `K.str`
  not at all, so `Smooth g` carried no regularity and this leaf was not
  provable — see the FALSITY AUDIT on `isRegularLocalRing_stalk_of_smooth`
  above, together with the correction recorded there of its claim that that
  audit's counterexample refutes THIS leaf (it does not: its `X` is a single
  point, so its only endomorphism is `𝟙` and the conclusion is `a = a`).
* Every step of the route above except going-down is now discharged here.
  The two heights are the heights of the two maximal ideals
  (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`), `𝔪_x` lies over
  `𝔪_{u x}` because a stalk map is a LOCAL homomorphism
  (`IsLocalRing.maximalIdeal_comap`), the fibre is zero-dimensional by the
  already-proven `ringKrullDim_quotient_map_maximalIdeal_stalkMap`, and
  Noetherianness of both stalks comes free from `IsRegularLocalRing`, which
  mathlib defines as extending `IsNoetherianRing`.  The height algebra is
  packaged as `ringKrullDim_eq_of_hasGoingDown_of_ringKrullDim_quotient_eq_zero`
  above.

**No affine cover is descended to, and no scheme dimension theory is used.**
The route's steps 1 and 2 (irreducibility of `X`, surjectivity of `u`) are NOT
consumed by this assembly; they survive only as the natural way to prove the
one remaining leaf. -/
theorem ringKrullDim_stalk_eq_of_isFinite_endo {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsFinite u] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk (u x)) := by
  letI : Algebra (X.presheaf.stalk (u x)) (X.presheaf.stalk x) := (u.stalkMap x).hom.toAlgebra
  have halg : algebraMap (X.presheaf.stalk (u x)) (X.presheaf.stalk x)
      = (u.stalkMap x).hom := rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk x) := isRegularLocalRing_stalk_of_smooth g x
  haveI : IsRegularLocalRing (X.presheaf.stalk (u x)) :=
    isRegularLocalRing_stalk_of_smooth g (u x)
  haveI := hasGoingDown_stalkMap_of_isFinite_endo g u x
  haveI : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).LiesOver
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (u x))) :=
    ⟨(IsLocalRing.maximalIdeal_comap (u.stalkMap x).hom).symm⟩
  refine ringKrullDim_eq_of_hasGoingDown_of_ringKrullDim_quotient_eq_zero ?_
  rw [halg]
  exact ringKrullDim_quotient_map_maximalIdeal_stalkMap u x

/-! ### The three sub-leaves of miracle flatness at the ring level

`flat_of_isRegularLocalRing_of_ringKrullDim_eq` below is PROVEN over the three
statements in this block.  See its docstring for why the previously recorded
"`Tor`-free affine route" is NOT a route to it. -/

/-- **THE EMBEDDING DIMENSION DROPS BY EXACTLY ONE ON QUOTIENTING BY
`x ∈ 𝔪 ∖ 𝔪²`** (**PROVEN 2026-07-27**).

`isRegularLocalRing_quotient_span_singleton` (in `Modularity/RegularStalks.lean`)
says `R ⧸ (x)` is again regular local; this records the numerical half its
statement drops, namely that its embedding dimension is `m` when that of `R` is
`m + 1`.  That is what lets the induction of
`exists_isWeaklyRegular_span_eq_maximalIdeal_aux` below descend.

The `≤` half is the exchange lemma `exists_finset_card_span_insert_eq_maximalIdeal`
(a generating set of `𝔪` of size `m + 1` containing `x`, whose image without `x`
generates `𝔪 (R ⧸ (x))`).  The `≥` half is Krull's height theorem in the form
`ringKrullDim_le_ringKrullDim_quotient_add_encard`, transported across
regularity of `R ⧸ (x)` — which is exactly why that instance is a hypothesis
here rather than being derived: the caller already has it in hand. -/
theorem spanFinrank_maximalIdeal_quotient_span_singleton {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) (m : ℕ)
    (hn : (IsLocalRing.maximalIdeal R).spanFinrank = m + 1)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] :
    (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = m := by
  classical
  have hdim : ringKrullDim R = ((m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
  obtain ⟨T, hTcard, hTspan⟩ :=
    GaloisRepresentation.Modularity.exists_finset_card_span_insert_eq_maximalIdeal hxm hx2 hn
  set I : Ideal R := Ideal.span {x} with hI
  have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
  have hInt : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
  have hmapmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)
      = IsLocalRing.maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hsr : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank ≤ m := by
    have himg : IsLocalRing.maximalIdeal (R ⧸ I)
        = Ideal.span ((Ideal.Quotient.mk I) '' (T : Set R)) := by
      rw [← hmapmax, ← hTspan, Ideal.map_span, Set.image_insert_eq]
      have hx0 : (Ideal.Quotient.mk I) x = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
      rw [hx0, Ideal.span_insert_zero]
    rw [himg]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      ((T : Set R).toFinite.image _)) ?_
    exact le_trans (Set.ncard_image_le (T : Set R).toFinite) (by simp [hTcard])
  have hjac : ({x} : Set R) ⊆ Ring.jacobson R := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show y ∈ Ring.jacobson R
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hxm
  have hkey : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + 1 := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard ({x} : Set R) hjac
    simpa [hI] using h
  have hdimq : ((m : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hdim] at hkey
    push_cast at hkey
    exact ENat.WithBot.add_le_add_one_right_iff.mp hkey
  refine le_antisymm hsr ?_
  have hfr := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)
  have h2 : ((m : ℕ) : WithBot ℕ∞)
      ≤ (((IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank : ℕ) : WithBot ℕ∞) := by
    rw [hfr]; exact hdimq
  exact_mod_cast h2

/-- **THE INDUCTION CARRIER OF `exists_isWeaklyRegular_span_eq_maximalIdeal`**
(**PROVEN 2026-07-27**) — the same statement with the length measured against
the embedding dimension `n` rather than against `ringKrullDim R`, so that the
strong induction on `n` can be stated at all.  The two agree by
`IsRegularLocalRing.spanFinrank_maximalIdeal`, which is the DEFINITION of
`IsRegularLocalRing`. -/
theorem exists_isWeaklyRegular_span_eq_maximalIdeal_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n →
      ∃ rs : List R, Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R ∧
        rs.length = n ∧ RingTheory.Sequence.IsWeaklyRegular R rs := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    match n, hn, ih with
    | 0, hn, _ =>
      refine ⟨[], ?_, rfl, RingTheory.Sequence.IsWeaklyRegular.nil R R⟩
      have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 hn
      rw [hbot]
      simp
    | (m + 1), hn, ih =>
      -- `𝔪 ⊄ 𝔪²`, else Nakayama forces `𝔪 = ⊥` and the embedding dimension is `0`.
      have hm2 : ¬ (IsLocalRing.maximalIdeal R ≤ (IsLocalRing.maximalIdeal R) ^ 2) := by
        intro hle
        have hb : IsLocalRing.maximalIdeal R = ⊥ := by
          refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
            (IsNoetherian.noetherian _) ?_ ?_
          · rwa [smul_eq_mul, ← pow_two]
          · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
        rw [hb] at hn
        simp at hn
      obtain ⟨x, hxm, hx2⟩ := Set.not_subset.1 hm2
      set I : Ideal R := Ideal.span {x} with hI
      have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
      have hInt : I ≠ ⊤ := fun h =>
        (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
      haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
      haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      haveI hreg : IsRegularLocalRing (R ⧸ I) :=
        GaloisRepresentation.Modularity.isRegularLocalRing_quotient_span_singleton hxm hx2
      have hsrq : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank = m :=
        spanFinrank_maximalIdeal_quotient_span_singleton hxm hx2 m hn
      obtain ⟨rs', hspan', hlen', hreg'⟩ := ih m (Nat.lt_succ_self m) (R ⧸ I) hsrq
      -- lift `rs'` along the surjection `R → R ⧸ I`
      obtain ⟨rs, hrs⟩ : ∃ rs : List R, rs.map (Ideal.Quotient.mk I) = rs' := by
        clear hspan' hlen' hreg'
        induction rs' with
        | nil => exact ⟨[], rfl⟩
        | cons a l ihl =>
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨l', hl'⟩ := ihl
          exact ⟨b :: l', by simp [hb, hl']⟩
      refine ⟨x :: rs, ?_, ?_, ?_⟩
      · -- `(x) + (rs) = 𝔪`, read off by taking `comap` of the corresponding
        -- identity in `R ⧸ (x)`, where `ker (mk) = (x) ≤ 𝔪` absorbs the join.
        have hmapofl : (Ideal.span {r | r ∈ rs}).map (Ideal.Quotient.mk I)
            = IsLocalRing.maximalIdeal (R ⧸ I) := by
          rw [show (Ideal.span {r | r ∈ rs}) = Ideal.ofList rs from rfl,
            Ideal.map_ofList, hrs]
          exact hspan'
        have hcm : Ideal.comap (Ideal.Quotient.mk I)
            (IsLocalRing.maximalIdeal (R ⧸ I)) = IsLocalRing.maximalIdeal R := by
          rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
            Ideal.Quotient.mk_surjective,
            Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_eq_left.2 hIm
        have hsup : Ideal.span {r | r ∈ rs} ⊔ I = IsLocalRing.maximalIdeal R := by
          rw [← hcm, ← hmapofl,
            Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [show (Ideal.span {r | r ∈ (x :: rs)}) =
            Ideal.ofList (x :: rs) from rfl,
          Ideal.ofList_cons, ← hI, sup_comm]
        exact hsup
      · have hlrs : rs.length = m := by rw [← hlen', ← hrs, List.length_map]
        simp [hlrs]
      · -- `x` is a nonzerodivisor because `R` is a DOMAIN; the tail is the
        -- induction hypothesis transported along `R ⧸ (x) ≃ₗ QuotSMulTop x R`.
        have hx0 : x ≠ 0 := by
          intro h
          exact hx2 (h ▸ Ideal.zero_mem _)
        haveI : IsDomain R := GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing R
        have hxreg : IsSMulRegular R x := mul_right_injective₀ hx0
        have hstep : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop x R) rs := by
          have hquot : RingTheory.Sequence.IsWeaklyRegular (R := R) (R ⧸ I) rs := by
            rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) (R ⧸ I) rs]
            rw [show (rs.map (algebraMap R (R ⧸ I))) = rs' from hrs]
            exact hreg'
          have he : (R ⧸ I) ≃ₗ[R] QuotSMulTop x R :=
            Submodule.quotEquivOfEq _ _ (by
              rw [hI, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
          exact (he.isWeaklyRegular_congr rs).1 hquot
        exact (RingTheory.Sequence.isWeaklyRegular_cons_iff R x rs).2 ⟨hxreg, hstep⟩

/-- **A REGULAR LOCAL RING HAS A REGULAR SYSTEM OF PARAMETERS, AND IT IS A
REGULAR SEQUENCE** (**PROVEN 2026-07-27** — pure commutative algebra; would be
at home in `Mathlib/RingTheory/RegularLocalRing/`).

`𝔪_R` is generated by `dim R` elements *by the definition of
`IsRegularLocalRing`* (`spanFinrank_maximalIdeal`); the CONTENT of this leaf is
that some such generating list is a weakly regular sequence.

**IT WAS BLOCKED BY DECLARATION ORDER, NOT BY MATHEMATICS, AND THE HOIST THAT
UNBLOCKED IT LANDED ON 2026-07-27.**  The induction is on `n = (𝔪_R).spanFinrank`
and lives in `exists_isWeaklyRegular_span_eq_maximalIdeal_aux` above:

* `n = 0`: `𝔪_R = ⊥`, so `R` is a field and `rs = []` works
  (`IsWeaklyRegular R []` is vacuous).
* `n + 1`: take `t ∈ 𝔪_R \ 𝔪_R²`.  Then `R ⧸ (t)` is regular local of dimension
  `n`, and `t` is a nonzerodivisor because a regular local ring is a DOMAIN and
  `t ≠ 0`.  Recurse in `R ⧸ (t)`, lift the resulting list along
  `Ideal.Quotient.mk`, and prepend `t`; `isWeaklyRegular_cons_iff` plus the
  identification `QuotSMulTop t R ≃ₗ R ⧸ (t)` and
  `isWeaklyRegular_map_algebraMap_iff` assemble the two halves.

All three non-trivial inputs now live in `Modularity/RegularStalks.lean`, which
is UPSTREAM of this module and which this file `public import`s:
`isRegularLocalRing_quotient_span_singleton` and the exchange lemma
`exists_finset_card_span_insert_eq_maximalIdeal` were hoisted there out of
`Modularity/KhareWintenberger.lean` with the cone of
`isRegularLocalRing_stalk_of_smooth_over_field`, and
`isDomain_of_isRegularLocalRing` — which that hoist deliberately left behind, as
a sibling consumer of the exchange lemma rather than a member of the cone — was
hoisted after it on 2026-07-27, byte-identical, precisely for this leaf.

The check that would refute this note:

    grep -n 'theorem isDomain_of_isRegularLocalRing\b' \
         Fermat/FLT/Modularity/RegularStalks.lean
    grep -n 'theorem isRegularLocalRing_quotient_span_singleton' \
         Fermat/FLT/Modularity/RegularStalks.lean

Mathlib itself has neither: its entire `IsRegularLocalRing` API is three lemmas
in `RingTheory/RegularLocalRing/Defs.lean` (`of_ringEquiv`,
`of_spanFinrank_maximalIdeal_le`, `iff_finrank_cotangentSpace`) plus the PID
instance — re-checked 2026-07-27 with
`grep -rn IsRegularLocalRing .lake/packages/mathlib/Mathlib/`. -/
theorem exists_isWeaklyRegular_span_eq_maximalIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    ∃ rs : List R, Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim R ∧
      RingTheory.Sequence.IsWeaklyRegular R rs := by
  obtain ⟨rs, hspan, hlen, hreg⟩ := exists_isWeaklyRegular_span_eq_maximalIdeal_aux _ R rfl
  exact ⟨rs, hspan, by rw [hlen, IsRegularLocalRing.spanFinrank_maximalIdeal], hreg⟩

/-- **THE DIMENSION OF `T ⧸ p` IS THE COHEIGHT OF `p` IN `Spec T`**
(**PROVEN 2026-07-27**; pure order theory over `ringKrullDim_quotient`).

`Spec (T ⧸ p) ≃o V(p)` (`ringKrullDim_quotient`), and for `p` PRIME the closed
set `V(p)` is literally the up-set `Set.Ici ⟨p⟩`, whose Krull dimension is the
coheight of `⟨p⟩` by `Order.coheight_eq_krullDim_Ici`.  Mathlib has no
`Ideal.coheight`, so this bridge has to be written by hand; it is the only
thing needed to get at `Order.coheight_add_one_le`, which is where the
dimension drop below actually comes from. -/
theorem ringKrullDim_quotient_eq_coheight {T : Type u} [CommRing T] (r : Ideal T)
    (hr : r.IsPrime) :
    ringKrullDim (T ⧸ r) = ((Order.coheight (⟨r, hr⟩ : PrimeSpectrum T) : ℕ∞) : WithBot ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (R := T) (r : Set T)
      = Set.Ici (⟨r, hr⟩ : PrimeSpectrum T) := by
    ext x
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    exact SetLike.coe_subset_coe
  rw [ringKrullDim_quotient, hset]
  exact (Order.coheight_eq_krullDim_Ici _).symm

/-- **A STRICTLY LARGER PRIME DROPS THE DIMENSION OF THE QUOTIENT BY AT LEAST
ONE** (**PROVEN 2026-07-27**).

`dim (T ⧸ q) + 1 ≤ dim (T ⧸ p)` whenever `p < q` are primes: prepending `p` to
a chain out of `q` lengthens it by one.  In coheight form that is exactly
`Order.coheight_add_one_le`, which — unlike `Order.coheight_strictAnti` —
carries NO finiteness side condition, so no Noetherian or local hypothesis is
needed here. -/
theorem ringKrullDim_quotient_succ_le_of_lt {T : Type u} [CommRing T] {p q : Ideal T}
    (hp : p.IsPrime) (hq : q.IsPrime) (hlt : p < q) :
    ringKrullDim (T ⧸ q) + 1 ≤ ringKrullDim (T ⧸ p) := by
  rw [ringKrullDim_quotient_eq_coheight q hq, ringKrullDim_quotient_eq_coheight p hp]
  have hlt' : (⟨p, hp⟩ : PrimeSpectrum T) < ⟨q, hq⟩ := hlt
  exact_mod_cast Order.coheight_add_one_le hlt'

/-- **ISCHEBECK'S INEQUALITY `depth T ≤ dim (T ⧸ p)`, BY INDUCTION ON THE LENGTH
OF THE REGULAR SEQUENCE** (**PROVEN 2026-07-27**; this is the whole content of
`ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime` below).

The induction is over `n`, the length of a weakly regular sequence lying in
`𝔪_T` — the RING varies, so `T` is universally quantified INSIDE the statement
and the step instantiates it at `T ⧸ xT`.

* `n = 0`: `T ⧸ p` is nontrivial because `p` is prime, so `0 ≤ dim (T ⧸ p)`.
* `n + 1`, sequence `x :: rest`.  `x` is `T`-regular
  (`isWeaklyRegular_cons_iff`), so `x ∉ p`: the union of the associated primes
  is exactly the set of zerodivisors
  (`biUnion_associatedPrimes_eq_compl_regular`).  Write `N = (0 : p)` for the
  annihilator of `p`, i.e. `Submodule.colon ⊥ ↑p`.

  **The one genuinely missing step was `Ass (T ⧸ xT) ∩ V(p + (x)) ≠ ∅`, and
  NAKAYAMA is what supplies it.**  `N ≠ 0`, since `p = (0 : y)` for some `y`
  (`isAssociatedPrime_iff`, using Noetherianness) and that `y` lies in `N`.  If
  `N ⊆ (x)` then every `z = wx ∈ N` has `w ∈ N` — because `x(ws) = (wx)s = 0`
  for `s ∈ p` and `x` is regular — so `N ⊆ (x) • N`, whence `N = 0` by
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` (`x ∈ 𝔪 = jacobson ⊥`).
  Contradiction.  So pick `z ∈ N \ (x)`; its image in `T ⧸ xT` is nonzero, and
  `exists_le_isAssociatedPrime_of_isNoetherianRing` gives an associated prime
  `P` of `T ⧸ xT` containing `(0 : z̄) ⊇ p·(T ⧸ xT)`.

  Pull `P` back to `q ⊆ T`.  Then `p ≤ q` and `x ∈ q`, so `p < q`.  The
  induction hypothesis at `T ⧸ xT` (Noetherian local, with the tail sequence
  `rest.map (mk (x))` of length `n` inside its maximal ideal, by
  `isWeaklyRegular_map_algebraMap_iff`) gives
  `n ≤ dim ((T ⧸ xT) ⧸ P) = dim (T ⧸ q)` (`DoubleQuot.quotQuotEquivQuotOfLE`),
  and `ringKrullDim_quotient_succ_le_of_lt` adds the missing `+ 1`. -/
theorem ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime_aux (n : ℕ) :
    ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (zs : List T), zs.length = n → (∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal T) →
    RingTheory.Sequence.IsWeaklyRegular T zs →
    ∀ {p : Ideal T}, IsAssociatedPrime p T → (n : WithBot ℕ∞) ≤ ringKrullDim (T ⧸ p) := by
  induction n with
  | zero =>
    intro T _ _ _ zs _ _ _ p hp
    haveI : Nontrivial (T ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.isPrime.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial (R := T ⧸ p)
  | succ n ih =>
    intro T _ _ _ zs hlen hmem hreg p hp
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, zs = x :: rest := by
      cases zs with
      | nil => simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    have hlen' : rest.length = n := by simpa using hlen
    obtain ⟨hxreg, hstep⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff T x rest).1 hreg
    have hxmem : x ∈ IsLocalRing.maximalIdeal T := hmem x (List.mem_cons_self)
    haveI hpp : p.IsPrime := hp.isPrime
    -- `x` is a nonzerodivisor, so it escapes every associated prime
    have hxnp : x ∉ p := by
      intro hxp
      have hmem2 : x ∈ ⋃ P ∈ associatedPrimes T T, (P : Set T) := Set.mem_biUnion hp hxp
      rw [biUnion_associatedPrimes_eq_compl_regular T T] at hmem2
      exact hmem2 hxreg
    have hspanle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal T :=
      (Ideal.span_singleton_le_iff_mem _).2 hxmem
    have hIne : Ideal.span {x} ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.1 (h ▸ hspanle))
    -- `N = (0 : p)`, the annihilator of `p`
    set N : Ideal T := Submodule.colon (⊥ : Submodule T T) (p : Set T) with hN
    obtain ⟨y, hy⟩ : ∃ y : T, p = Submodule.colon (⊥ : Submodule T T) {y} :=
      (isAssociatedPrime_iff.1 hp).2
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hpp.ne_top (hy.trans Submodule.colon_singleton_zero)
    have hyN : y ∈ N := by
      rw [hN, Submodule.mem_colon]
      intro s hs
      rw [SetLike.mem_coe, hy, Submodule.mem_colon_singleton, Submodule.mem_bot] at hs
      simpa [smul_eq_mul, mul_comm] using hs
    -- NAKAYAMA: `N` is not contained in `(x)`
    have hNnotle : ¬ N ≤ Ideal.span {x} := by
      intro hsub
      have hFG : N.FG := IsNoetherian.noetherian N
      have hle : N ≤ Ideal.span {x} • N := by
        intro z hz
        obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 (hsub hz)
        have hwN : w ∈ N := by
          rw [hN, Submodule.mem_colon]
          intro s hs
          rw [Submodule.mem_bot, smul_eq_mul]
          have hzs : w * x * s = 0 := by
            have h1 := (Submodule.mem_colon.1 hz) s hs
            rw [Submodule.mem_bot, smul_eq_mul] at h1
            exact h1
          have h0 : x • (w * s) = x • (0 : T) := by
            simp only [smul_eq_mul, mul_zero]
            linear_combination hzs
          exact hxreg h0
        have hmul : x • w ∈ Ideal.span {x} • N :=
          Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hwN
        simpa [smul_eq_mul, mul_comm] using hmul
      have hjac : Ideal.span {x} ≤ Ideal.jacobson (⊥ : Ideal T) := by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal T) bot_ne_top]
        exact hspanle
      have hbot : N = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ N hFG hle hjac
      exact hy0 (by simpa [hbot] using hyN)
    obtain ⟨z, hzN, hzI⟩ := SetLike.not_le_iff_exists.1 hNnotle
    -- pass to `T ⧸ xT`
    haveI : Nontrivial (T ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hIne
    haveI : IsLocalRing (T ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hzne : (Ideal.Quotient.mk (Ideal.span {x})) z ≠ 0 := fun h =>
      hzI (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨P, hP, hPle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
      (T ⧸ Ideal.span {x}) ((Ideal.Quotient.mk (Ideal.span {x})) z) hzne
    haveI hPp : P.IsPrime := hP.isPrime
    have hpP : p.map (Ideal.Quotient.mk (Ideal.span {x})) ≤ P := by
      refine le_trans ?_ hPle
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot,
        smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have haz := (Submodule.mem_colon.1 hzN) a ha
      rw [Submodule.mem_bot, smul_eq_mul] at haz
      rw [show a * z = z * a from mul_comm _ _, haz]
      exact Ideal.zero_mem _
    set q : Ideal T := P.comap (Ideal.Quotient.mk (Ideal.span {x})) with hq
    haveI hqp : q.IsPrime := Ideal.IsPrime.comap _
    have hpq : p ≤ q := Ideal.map_le_iff_le_comap.1 hpP
    have hxq : x ∈ q := by
      have hx0 : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self x)
      rw [hq, Ideal.mem_comap, hx0]
      exact P.zero_mem
    have hpqlt : p < q := lt_of_le_of_ne hpq (fun h => hxnp (h ▸ hxq))
    -- the tail is a weakly regular sequence inside `𝔪_{T ⧸ xT}`
    have hstep' : RingTheory.Sequence.IsWeaklyRegular (R := T) (T ⧸ Ideal.span {x}) rest := by
      have he : QuotSMulTop x T ≃ₗ[T] (T ⧸ Ideal.span {x}) :=
        Submodule.quotEquivOfEq _ _ (by
          rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
      exact (he.isWeaklyRegular_congr rest).1 hstep
    have hreg' : RingTheory.Sequence.IsWeaklyRegular (R := T ⧸ Ideal.span {x})
        (T ⧸ Ideal.span {x}) (rest.map (algebraMap T (T ⧸ Ideal.span {x}))) :=
      (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (T ⧸ Ideal.span {x})
        (T ⧸ Ideal.span {x}) rest).2 hstep'
    have hmem' : ∀ w ∈ rest.map (algebraMap T (T ⧸ Ideal.span {x})),
        w ∈ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {x}) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective, Ideal.Quotient.algebraMap_eq]
      exact Ideal.mem_map_of_mem _ (hmem v (List.mem_cons_of_mem _ hv))
    have hIH := ih (T ⧸ Ideal.span {x}) (rest.map (algebraMap T (T ⧸ Ideal.span {x})))
      (by simpa using hlen') hmem' hreg' hP
    -- identify `(T ⧸ xT) ⧸ P` with `T ⧸ q`
    have hPeq : P = q.map (Ideal.Quotient.mk (Ideal.span {x})) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm
    have hxle : Ideal.span {x} ≤ q := (Ideal.span_singleton_le_iff_mem _).2 hxq
    have hiso : ringKrullDim ((T ⧸ Ideal.span {x}) ⧸ P) = ringKrullDim (T ⧸ q) := by
      rw [hPeq]
      exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hxle)
    rw [hiso] at hIH
    calc ((n + 1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) + 1 := by push_cast; ring
      _ ≤ ringKrullDim (T ⧸ q) + 1 := by gcongr
      _ ≤ ringKrullDim (T ⧸ p) := ringKrullDim_quotient_succ_le_of_lt hpp hqp hpqlt

/-- **ISCHEBECK: IN A COHEN–MACAULAY LOCAL RING EVERY ASSOCIATED PRIME HAS A
FULL-DIMENSIONAL QUOTIENT** (**PROVEN 2026-07-27** — pure commutative algebra;
Matsumura *Commutative Ring Theory* 17.2 (Ischebeck) together with 17.3,
Bruns–Herzog 1.2.13 / 2.1.2, Stacks 00N6.)

Read `depth T ≥ dim T` for the hypothesis: `hCM` says some weakly regular
sequence of length `dim T` lies in `𝔪_T`.  The conclusion says every associated
prime of `T` is as large-dimensional as `T` itself — equivalently (with the
trivial `dim T ⧸ p ≤ dim T`) that `T` has no embedded and no low-dimensional
associated primes, which is UNMIXEDNESS in its primary-decomposition form.

**THE CLASSICAL PROOF, and it is an induction on `depth`, not on `dim`.**
Ischebeck's inequality is `depth T ≤ dim (T ⧸ p)` for every `p ∈ Ass T`.  With
`t = depth T`: for `t = 0` there is nothing to prove.  For `t > 0` pick a
`T`-regular `x ∈ 𝔪`; since `p ∈ Ass T` consists of zerodivisors, `x ∉ p`, so
`dim T ⧸ (p + (x)) = dim T ⧸ p - 1`; choose `q ∈ Ass (T ⧸ xT)` containing
`p + (x)`, and apply the induction hypothesis to `T ⧸ xT`, whose depth is
`t - 1`.

**THE MATHLIB PIECES ARE PRESENT — this is not a from-scratch depth theory.**
The corrected inventory (checked 2026-07-27, and it CONTRADICTS what the
previous version of this block asserted, see the correction in
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` below):

* `Mathlib/RingTheory/Depth/Rees.lean` (184 lines) — **the Rees theorem**,
  `ModuleCat.exists_isRegular_tfae`, plus the two halves
  `ModuleCat.subsingleton_ext_of_exists_isRegular` and
  `ModuleCat.exists_isRegular_of_exists_subsingleton_ext`.  That is exactly the
  `Ext`-vs-regular-sequence dictionary this induction needs, and it is what
  `exists_isWeaklyRegular_quotSMulTop_of_isSMulRegular` below is proven from.
* `Mathlib/RingTheory/Ideal/AssociatedPrime/{Basic,Finiteness}.lean` —
  `associatedPrimes`, `IsAssociatedPrime`, finiteness, nonemptiness, and
  `biUnion_associatedPrimes_eq_compl_regular` (the union of the associated
  primes is the set of zerodivisors).
* `Mathlib/RingTheory/KrullDimension/Regular.lean` — the dimension bookkeeping,
  including `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` and
  `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`.

The step that was recorded here as "genuinely missing" — "`Ass (T ⧸ xT)` meets
`V(p + (x))`" — is supplied by NAKAYAMA applied to the annihilator `(0 : p)`;
see `ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime_aux` above,
which carries the whole induction.  All this wrapper does is feed it
`n = dim T`. -/
theorem ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T]
    (hCM : ∃ zs : List T, (∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal T) ∧
      (zs.length : WithBot ℕ∞) = ringKrullDim T ∧ RingTheory.Sequence.IsWeaklyRegular T zs)
    {p : Ideal T} (hp : IsAssociatedPrime p T) :
    ringKrullDim T ≤ ringKrullDim (T ⧸ p) := by
  obtain ⟨zs, hzm, hzlen, hzreg⟩ := hCM
  rw [← hzlen]
  exact ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime_aux zs.length T zs rfl
    hzm hzreg hp

/-- **THE HEAD OF A SYSTEM OF PARAMETERS OF A COHEN–MACAULAY LOCAL RING IS A
NONZERODIVISOR** (**PROVEN 2026-07-27** over
`ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime` above).

The zerodivisors of `T` are the union of the associated primes
(`biUnion_associatedPrimes_eq_compl_regular`), so it suffices to rule out
`y ∈ p` for `p ∈ Ass T`.  If `y ∈ p` then `p ⊔ (ys)` contains `(y :: ys)`, so
`T ⧸ (p ⊔ (ys))` is a quotient of the zero-dimensional `T ⧸ (y :: ys)`; Krull's
height theorem in `T ⧸ p` (`ringKrullDim_le_ringKrullDim_quotient_add_encard`,
with the `n` remaining generators) then gives `dim T ⧸ p ≤ n`, while
unmixedness gives `dim T ⧸ p ≥ dim T = n + 1`. -/
theorem isSMulRegular_head_of_ringKrullDim_quotient_eq_zero {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] (n : ℕ) (y : T) (ys : List T)
    (hCM : ∃ zs : List T, (∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal T) ∧ zs.length = n + 1 ∧
      RingTheory.Sequence.IsWeaklyRegular T zs)
    (hdim : ((n + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim T)
    (hlen : ys.length = n)
    (hfib : ringKrullDim (T ⧸ Ideal.span {z | z ∈ y :: ys}) = 0) :
    IsSMulRegular T y := by
  classical
  by_contra hcon
  have hmem : y ∈ ⋃ q ∈ associatedPrimes T T, (q : Set T) := by
    rw [biUnion_associatedPrimes_eq_compl_regular T T]
    exact hcon
  obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hmem
  haveI hpp : p.IsPrime := hp.isPrime
  -- the system of parameters generates a proper ideal, so all its entries lie in `𝔪`
  have hInt : Ideal.span {z | z ∈ y :: ys} ≠ ⊤ := by
    intro h
    rw [h] at hfib
    haveI : Subsingleton (T ⧸ (⊤ : Ideal T)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at hfib
    simp at hfib
  have hmemm : ∀ z ∈ y :: ys, z ∈ IsLocalRing.maximalIdeal T := fun z hz =>
    IsLocalRing.le_maximalIdeal hInt (Ideal.subset_span hz)
  haveI : Nontrivial (T ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hpp.ne_top
  haveI : IsLocalRing (T ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  set s : Set (T ⧸ p) := {z | z ∈ ys.map (Ideal.Quotient.mk p)} with hs
  have hsj : s ⊆ Ring.jacobson (T ⧸ p) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ (hmemm w (List.mem_cons_of_mem _ hw))
  have hmap : Ideal.span s = Ideal.map (Ideal.Quotient.mk p) (Ideal.span {z | z ∈ ys}) := by
    show Ideal.ofList (ys.map (Ideal.Quotient.mk p)) = _
    rw [← Ideal.map_ofList]
  have hle2 : Ideal.span {z | z ∈ y :: ys} ≤ p ⊔ Ideal.span {z | z ∈ ys} := by
    show Ideal.ofList (y :: ys) ≤ _
    rw [Ideal.ofList_cons]
    exact sup_le_sup (Ideal.span_le.mpr (by simpa using hyp)) le_rfl
  have hq0 : ringKrullDim ((T ⧸ p) ⧸ Ideal.span s) ≤ 0 := by
    rw [hmap, ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {z | z ∈ ys}))]
    calc ringKrullDim (T ⧸ (p ⊔ Ideal.span {z | z ∈ ys}))
        ≤ ringKrullDim (T ⧸ Ideal.span {z | z ∈ y :: ys}) :=
          ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle2)
      _ = 0 := hfib
  have hsfin : s = ((ys.map (Ideal.Quotient.mk p)).toFinset : Set (T ⧸ p)) := by
    rw [hs, List.coe_toFinset]
  have hsc : s.encard ≤ (n : ℕ∞) := by
    rw [hsfin, Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (List.toFinset_card_le _).trans (by simp [hlen])
  have hfinal : ringKrullDim (T ⧸ p) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_encard s hsj).trans ?_
    have h1 : ((s.encard : ℕ∞) : WithBot ℕ∞) ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr (by exact_mod_cast hsc)
    calc ringKrullDim ((T ⧸ p) ⧸ Ideal.span s) + (s.encard : WithBot ℕ∞)
        ≤ 0 + (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := add_le_add hq0 h1
      _ = ((n : ℕ) : WithBot ℕ∞) := by simp
  obtain ⟨zs, hzm, hzlen, hzreg⟩ := hCM
  have hcontra : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by
    refine hdim.le.trans
      ((ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime ⟨zs, hzm, ?_, hzreg⟩ hp).trans
        hfinal)
    rw [hzlen, ← hdim]
  have : (n + 1 : ℕ) ≤ n := by exact_mod_cast hcontra
  omega

/-- **COHEN–MACAULAYNESS DESCENDS ALONG A NONZERODIVISOR: `depth (T ⧸ yT) =
depth T - 1`** (**PROVEN 2026-07-27**, from mathlib's Rees theorem).

Given a weakly regular sequence of length `n + 1` inside `𝔪_T` and a
`T`-regular `y ∈ 𝔪_T`, this produces a weakly regular sequence of length `n`
inside `𝔪_T` acting on `T ⧸ yT` (written `QuotSMulTop y T`, which is the shape
`RingTheory.Sequence.isWeaklyRegular_cons_iff` consumes).

**THIS IS WHAT MAKES THE INDUCTION OF
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero_aux` DESCEND**, and it is the
step for which a depth predicate is normally introduced.  The proof is three
applications of material already in the pin:

1. `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal` turns
   `hzreg` into an `IsRegular` sequence, and
   `ModuleCat.subsingleton_ext_of_exists_isRegular` (Rees, `(4) → (1)`) converts
   it into `Ext^i (T ⧸ 𝔪) T = 0` for `i < n + 1`.
2. The covariant long exact sequence of `0 → T →ʸ T → T ⧸ yT → 0`
   (`IsSMulRegular.smulShortComplex_shortExact` and
   `CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'`) drops that to
   `Ext^i (T ⧸ 𝔪) (T ⧸ yT) = 0` for `i < n`.
3. `ModuleCat.exists_isRegular_of_exists_subsingleton_ext` (Rees, `(3) → (4)`)
   converts it back into a regular sequence of length `n` in `𝔪` on `T ⧸ yT`.

Nakayama supplies the two `𝔪 • ⊤ < ⊤` side conditions
(`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`), and
`nontrivial_quotSMulTop_of_mem_maximalIdeal` the nontriviality of `T ⧸ yT`. -/
theorem exists_isWeaklyRegular_quotSMulTop_of_isSMulRegular {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T]
    {y : T} (hy : y ∈ IsLocalRing.maximalIdeal T) (hyreg : IsSMulRegular T y)
    (n : ℕ) (zs : List T) (hzm : ∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal T)
    (hzlen : zs.length = n + 1) (hzreg : RingTheory.Sequence.IsWeaklyRegular T zs) :
    ∃ ws : List T, (∀ w ∈ ws, w ∈ IsLocalRing.maximalIdeal T) ∧ ws.length = n ∧
      RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop y T) ws := by
  classical
  let N : ModuleCat.{u} T := ModuleCat.of T (T ⧸ IsLocalRing.maximalIdeal T)
  have hNsupp : Module.support T N
      = PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal T : Set T) := by
    show Module.support T (T ⧸ IsLocalRing.maximalIdeal T) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hsmulT : IsLocalRing.maximalIdeal T • (⊤ : Submodule T (ModuleCat.of T T)) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)))
  have hzregT : RingTheory.Sequence.IsRegular (ModuleCat.of T T) zs :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hzm hzreg
  have h_ext : ∀ i < n + 1,
      Subsingleton (_root_.CategoryTheory.Abelian.Ext N (ModuleCat.of T T) i) := by
    intro i hi
    refine ModuleCat.subsingleton_ext_of_exists_isRegular (IsLocalRing.maximalIdeal T) N
      hNsupp.le (ModuleCat.of T T) hsmulT zs hzm hzregT i ?_
    omega
  have h_ext' : ∀ i < n,
      Subsingleton (_root_.CategoryTheory.Abelian.Ext N
        (ModuleCat.of T (QuotSMulTop y T)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((_root_.CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' N
        (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of T T) hyreg)) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have hntQ : Nontrivial (QuotSMulTop y T) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal T hy
  have hsmulQ : IsLocalRing.maximalIdeal T •
      (⊤ : Submodule T (ModuleCat.of T (QuotSMulTop y T))) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)))
  obtain ⟨ws, hwlen, hwm, hwreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (IsLocalRing.maximalIdeal T) n (ModuleCat.of T (QuotSMulTop y T)) hsmulQ N hNsupp h_ext'
  exact ⟨ws, hwm, hwlen, hwreg.toIsWeaklyRegular⟩

/-- **THE INDUCTION CARRIER OF THE UNMIXEDNESS LEAF** (**PROVEN 2026-07-27**) —
the same statement with `dim T` replaced by a natural number `n`, so that the
induction on `n` can be stated at all, and with Cohen–Macaulayness in its
HONEST form (`∀ z ∈ zs, z ∈ 𝔪_T`) rather than the form `span zs = 𝔪_T` which
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` below carries.

**THAT WEAKENING IS THE WHOLE POINT AND IT IS NOT COSMETIC** — see the
correction in the docstring below.  `span zs = 𝔪_T` does not survive a
quotient; `∀ z ∈ zs, z ∈ 𝔪_T` does, and it is what the two steps of the
induction hand back and forth:

* `isSMulRegular_head_of_ringKrullDim_quotient_eq_zero` makes the head `y` a
  nonzerodivisor (this is where unmixedness is consumed);
* `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` drops the
  dimension by exactly one;
* `exists_isWeaklyRegular_quotSMulTop_of_isSMulRegular` drops the depth witness
  by exactly one, so the induction hypothesis applies to `T ⧸ (y)`;
* `DoubleQuot.quotQuotEquivQuotSup` identifies `(T ⧸ (y)) ⧸ (ys')` with
  `T ⧸ (y :: ys')`, so the zero-dimensionality hypothesis transports;
* `RingTheory.Sequence.isWeaklyRegular_cons_iff` reassembles, across the
  identification `T ⧸ (y) ≃ₗ[T] QuotSMulTop y T`. -/
theorem isWeaklyRegular_of_ringKrullDim_quotient_eq_zero_aux (n : ℕ) :
    ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (ys : List T),
      ((n : ℕ) : WithBot ℕ∞) = ringKrullDim T →
      ys.length = n →
      (∃ zs : List T, (∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal T) ∧ zs.length = n ∧
        RingTheory.Sequence.IsWeaklyRegular T zs) →
      ringKrullDim (T ⧸ Ideal.span {z | z ∈ ys}) = 0 →
      RingTheory.Sequence.IsWeaklyRegular T ys := by
  induction n with
  | zero =>
    intro T _ _ _ ys _ hlen _ _
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    exact RingTheory.Sequence.IsWeaklyRegular.nil T T
  | succ m ih =>
    intro T _ _ _ ys hdim hlen hCM hfib
    obtain _ | ⟨y, ys'⟩ := ys
    · simp at hlen
    · have hlen' : ys'.length = m := by simpa using hlen
      obtain ⟨zs, hzm, hzlen, hzreg⟩ := hCM
      set J : Ideal T := Ideal.span {y} with hJ
      have hIeq : Ideal.span {z | z ∈ y :: ys'} = J ⊔ Ideal.span {z | z ∈ ys'} := by
        show Ideal.ofList (y :: ys') = _
        rw [Ideal.ofList_cons]
      have hInt : Ideal.span {z | z ∈ y :: ys'} ≠ ⊤ := by
        intro h
        rw [h] at hfib
        haveI : Subsingleton (T ⧸ (⊤ : Ideal T)) := Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hfib
        simp at hfib
      have hy : y ∈ IsLocalRing.maximalIdeal T :=
        IsLocalRing.le_maximalIdeal hInt (Ideal.subset_span (by simp))
      have hyreg : IsSMulRegular T y :=
        isSMulRegular_head_of_ringKrullDim_quotient_eq_zero m y ys'
          ⟨zs, hzm, hzlen, hzreg⟩ hdim hlen' hfib
      have hJle : J ≤ Ideal.span {z | z ∈ y :: ys'} := by rw [hIeq]; exact le_sup_left
      have hJnt : J ≠ ⊤ := fun h => hInt (top_le_iff.mp (h ▸ hJle))
      haveI : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJnt
      haveI : IsLocalRing (T ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      -- `dim (T ⧸ (y)) = m`
      have hdimJ : ((m : ℕ) : WithBot ℕ∞) = ringKrullDim (T ⧸ J) := by
        have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hyreg hy
        rw [← hdim] at h
        have h1 : ringKrullDim (T ⧸ J) + 1 = ((m : ℕ) : WithBot ℕ∞) + 1 := by
          rw [h]; push_cast; ring
        exact le_antisymm (ENat.WithBot.add_le_add_one_right_iff.mp h1.ge)
          (ENat.WithBot.add_le_add_one_right_iff.mp h1.le)
      -- the identification of `T ⧸ (y)` with `QuotSMulTop y T`
      have hequiv : (T ⧸ J) ≃ₗ[T] QuotSMulTop y T :=
        Submodule.quotEquivOfEq _ _ (by
          rw [hJ, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
      have transfer : ∀ l : List T, RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop y T) l ↔
          RingTheory.Sequence.IsWeaklyRegular (T ⧸ J) (l.map (Ideal.Quotient.mk J)) := by
        intro l
        rw [show (l.map (Ideal.Quotient.mk J)) = l.map (algebraMap T (T ⧸ J)) from rfl,
          RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := T) (S := T ⧸ J)
            (M := T ⧸ J) l]
        exact (hequiv.isWeaklyRegular_congr l).symm
      obtain ⟨ws, hwm, hwlen, hwreg⟩ :=
        exists_isWeaklyRegular_quotSMulTop_of_isSMulRegular hy hyreg m zs hzm hzlen hzreg
      have hfib' : ringKrullDim
          ((T ⧸ J) ⧸ Ideal.span {z | z ∈ ys'.map (Ideal.Quotient.mk J)}) = 0 := by
        have hmap : Ideal.span {z | z ∈ ys'.map (Ideal.Quotient.mk J)}
            = Ideal.map (Ideal.Quotient.mk J) (Ideal.span {z | z ∈ ys'}) := by
          show Ideal.ofList (ys'.map (Ideal.Quotient.mk J)) = _
          rw [← Ideal.map_ofList]
        rw [hmap, ringKrullDim_eq_of_ringEquiv
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {z | z ∈ ys'}))]
        exact hIeq ▸ hfib
      have hihres := ih (T ⧸ J) (ys'.map (Ideal.Quotient.mk J)) hdimJ (by simpa using hlen')
        ⟨ws.map (Ideal.Quotient.mk J), ?_, by simpa using hwlen, (transfer ws).mp hwreg⟩ hfib'
      · exact (RingTheory.Sequence.isWeaklyRegular_cons_iff T y ys').2
          ⟨hyreg, (transfer ys').mpr hihres⟩
      · intro w hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
        rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
          Ideal.Quotient.mk_surjective]
        exact Ideal.mem_map_of_mem _ (hwm w0 hw0)

/-- **UNMIXEDNESS: IN A COHEN–MACAULAY LOCAL RING EVERY SYSTEM OF PARAMETERS IS
A REGULAR SEQUENCE** (**PROVEN 2026-07-27** over the single remaining leaf
`ringKrullDim_le_ringKrullDim_quotient_of_isAssociatedPrime` above — Matsumura
*Commutative Ring Theory* 17.4 / Stacks 00N7).

`φ` and `R` have disappeared entirely: this is a statement about ONE local ring.

**CORRECTION (2026-07-27) — `hCM` AS WRITTEN IS NOT `depth T = dim T`; IT IS
`IsRegularLocalRing T`, AND THE PREVIOUS VERSION OF THIS DOCSTRING SAID
OTHERWISE.**  It claimed "`hCM` says verbatim: some weakly regular sequence of
length `dim T` generates `𝔪_T`.  That is `depth T = dim T` written without a
`depth` predicate", and then explained at length why the shape was chosen over
`[IsRegularLocalRing T]` because `hCM` "SURVIVES the quotient" while regularity
does not.  Both halves are wrong, and they are wrong for the same one-line
reason.  The refuting computation:

    span zs = 𝔪_T  and  zs.length = dim T
      ⟹ (𝔪_T).spanFinrank ≤ dim T
      ⟹ IsRegularLocalRing T          (`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`)

Cohen–Macaulayness asks for a regular sequence of length `dim T` *inside* `𝔪`;
asking it to GENERATE `𝔪` is regularity, since `dim T ≤ (𝔪_T).spanFinrank`
always (Krull).  So the cut did not in fact move off `[IsRegularLocalRing T]`,
and the induction its own docstring prescribed cannot be run on `hCM`: the
hypothesis it names as the one that survives the quotient is exactly the one
that does not.  (`T = k⟦x⟧`, `t = x²` remains a correct illustration — of why
regularity fails to survive, hence of why `hCM` fails to survive.)

The statement is nevertheless TRUE and is left EXACTLY AS IT STANDS, because it
is what `isWeaklyRegular_map_of_ringKrullDim_eq` below consumes.  The proof
simply weakens `hCM` to the honest Cohen–Macaulay form in its first step and
hands it to `isWeaklyRegular_of_ringKrullDim_quotient_eq_zero_aux` above, where
the induction really does descend.

**CORRECTION (2026-07-27) — THERE IS A DEPTH LAYER, AND IT IS IN MATHLIB.**
The previous version of this docstring said "there is no depth or
Cohen–Macaulay layer anywhere in this repository, and mathlib's
`RingTheory/Regular/Depth.lean` is a 10-line file with zero declarations", and
directed a prover to vendor `~/cs/FLT/FLT/Patching/Utils/Depth.lean`.  The
first clause is true of THIS repository and false of the pin.  The refuting
greps, both run on 2026-07-27:

    ls  .lake/packages/mathlib/Mathlib/RingTheory/Depth/          # Rees.lean, 184 lines
    cat .lake/packages/mathlib/Mathlib/RingTheory/Regular/Depth.lean

`Regular/Depth.lean` looks empty because it is a `deprecated_module` shim
(since 2026-04-28); the content moved to `Mathlib/RingTheory/Depth/Rees.lean`,
which proves **the Rees theorem** `ModuleCat.exists_isRegular_tfae` —
the equivalence between vanishing of `Ext^i (R ⧸ I) M` and the existence of an
`M`-regular sequence of length `i` in `I`.  That is precisely the well-definedness
of depth, and it is what makes `exists_isWeaklyRegular_quotSMulTop_of_isSMulRegular`
above provable rather than a leaf.  **Do not vendor a depth layer for this
node.**  (`~/cs/FLT`'s file is still unvendored, and is still the wrong tool: it
proves `depth ≤ dim`, and what is wanted here is `dim ≤ depth`.) -/
theorem isWeaklyRegular_of_ringKrullDim_quotient_eq_zero {T : Type u} [CommRing T]
    [IsLocalRing T] [IsNoetherianRing T] (ys : List T)
    (hCM : ∃ zs : List T, Ideal.span {z | z ∈ zs} = IsLocalRing.maximalIdeal T ∧
      (zs.length : WithBot ℕ∞) = ringKrullDim T ∧ RingTheory.Sequence.IsWeaklyRegular T zs)
    (hlen : (ys.length : WithBot ℕ∞) = ringKrullDim T)
    (hfib : ringKrullDim (T ⧸ Ideal.span {y | y ∈ ys}) = 0) :
    RingTheory.Sequence.IsWeaklyRegular T ys := by
  obtain ⟨zs, hspan, hzlen, hzreg⟩ := hCM
  refine isWeaklyRegular_of_ringKrullDim_quotient_eq_zero_aux ys.length T ys hlen rfl
    ⟨zs, ?_, ?_, hzreg⟩ hfib
  · intro z hz
    rw [← hspan]
    exact Ideal.subset_span hz
  · exact_mod_cast hzlen.trans hlen.symm

/-- **A SYSTEM OF PARAMETERS OF A REGULAR LOCAL RING IS A REGULAR SEQUENCE**
(**PROVEN 2026-07-27** over the unmixedness leaf
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` immediately above, into which
all of its remaining content has been moved).

The hypotheses say exactly that `rs.map φ` is a system of parameters of `T`:
`hspan` makes `Ideal.span (rs.map φ) = Ideal.map φ 𝔪_R`, `hfib` says that ideal
is `𝔪_T`-primary (dimension `0` quotient), and `hlen` with `hdim` says the list
has exactly `dim T` entries.  The classical chain is `T` regular ⟹ `T`
Cohen–Macaulay ⟹ every system of parameters is a regular sequence, and the CUT
made here is exactly at the arrow in the middle:

* `T` regular ⟹ `T` Cohen–Macaulay is **PROVEN**, as
  `exists_isWeaklyRegular_span_eq_maximalIdeal` above — the sequence it produces
  is precisely the `hCM` witness the unmixedness leaf asks for.
* Cohen–Macaulay ⟹ unmixedness is the open leaf
  `isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` above, where the discussion
  of why the naive induction fails now lives.

All this declaration still does is match the two up: `Ideal.map_ofList` turns
`Ideal.span (rs.map φ)` into `Ideal.map φ 𝔪_R`, so `hfib` is literally the
zero-dimensionality hypothesis, and `hlen` with `hdim` is literally the length
hypothesis.

**ABSENT EVERYWHERE, re-checked 2026-07-27 with the refuting greps.**
`grep -rl CohenMacaulay .lake/packages/mathlib/Mathlib/` is empty and
`Mathlib/RingTheory/Regular/Depth.lean` is a 10-line file with ZERO
declarations.

**CORRECTION (2026-07-27) — `Module.depth` IS NOT VENDORED INTO THIS PROJECT.**
The previous version of this paragraph said `~/cs/FLT`'s
`FLT/Patching/Utils/Depth.lean` was "already vendored into this project and
consumed by `Fermat/FLT/Modularity/PatchingVendored/System.lean`".  That is
FALSE, and a prover who believed it would go looking for an API that is not
there.  The refuting greps, both run on 2026-07-27:

    ls Fermat/FLT/Modularity/PatchingVendored/          # no Depth.lean
    grep -rn "Module.depth" Fermat/                     # only PROSE, no code

`PatchingVendored/System.lean:258-261` names `Module.depth` in a COMMENT
explaining what it did *instead* of vendoring it, and
`Modularity/Patching.lean:6749` says outright that the depth endgame was
"deliberately not vendored".  So there is **no depth layer anywhere in this
repository**, and `~/cs/FLT`'s file remains an unvendored external reference.

That file (259 lines) does contain `Module.depth`, `Module.length_le_depth`,
`Module.depth_le_dim`, `Module.depth_le_of_free` and
`RingTheory.Sequence.isWeaklyRegular_of_free`, and it is the natural thing to
vendor first — but note it proves only `depth ≤ dim`, which is the WRONG
inequality here.

**SO THE ROUTE, IN THE ORDER THE PIECES ARE NEEDED** — and this is why the cut
above is where it is.  What is required is `dim ≤ depth` for a regular local
ring, and that half is now **available, not missing**:
`exists_isWeaklyRegular_span_eq_maximalIdeal` above (**PROVEN 2026-07-27**)
produces a weakly regular sequence generating `𝔪_T` of length exactly `dim T`,
which is precisely a witness that `depth T ≥ dim T`, i.e. that a regular local
ring is Cohen–Macaulay.  What remained genuinely new was only the UNMIXEDNESS
half, and that is now the separate leaf
`isWeaklyRegular_of_ringKrullDim_quotient_eq_zero` above — stated WITHOUT a
depth predicate, by writing Cohen–Macaulayness out as "some weakly regular
sequence of length `dim` generates `𝔪`", so that no `Depth.lean` vendoring is
needed merely to state it.  Proving it is the real work, and it is all that is
left under this node. -/
theorem isWeaklyRegular_map_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim R)
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    RingTheory.Sequence.IsWeaklyRegular T (rs.map φ) := by
  -- the image list spans exactly the extended ideal, so `hfib` IS the
  -- zero-dimensionality hypothesis of the unmixedness leaf
  have himg : Ideal.span {y | y ∈ rs.map φ} = Ideal.map φ (IsLocalRing.maximalIdeal R) := by
    rw [show (Ideal.span {y | y ∈ rs.map φ}) = Ideal.ofList (rs.map φ) from rfl,
      ← Ideal.map_ofList]
    exact congrArg (Ideal.map φ) hspan
  refine isWeaklyRegular_of_ringKrullDim_quotient_eq_zero (rs.map φ)
    (exists_isWeaklyRegular_span_eq_maximalIdeal T) ?_ ?_
  · rw [List.length_map, hlen, hdim]
  · rw [himg]; exact hfib

section LocalCriterionOfFlatness

open scoped TensorProduct

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- **THE POWER STEP OF THE LOCAL CRITERION OF FLATNESS** (**PROVEN 2026-07-27**
over the single general leaf `Module.Flat.of_flat_quotient_of_pow_eq_bot` —
the local criterion of flatness for a NILPOTENT ideal — which now lives in the
shim tree at `Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`; Stacks
051C + 00MK in the NILPOTENT case, Matsumura *Commutative Ring Theory*
22.1/22.2).

`t` a nonzerodivisor on `R` and on `T` with `T ⧸ (φ t)` flat over `R ⧸ (t)`;
then `T ⧸ (φ t)^n` is flat over `R ⧸ (t)^n` for every `n`.

**WHY THIS IS ONE OF THE TWO HALVES.**  Together with
`mem_baseChange_sup_of_flat_quotientMap_pow` below it proves the atom
`flat_of_flat_quotient_isSMulRegular`.  It is the half that needs NO
separatedness and NO Artin–Rees: inside `A := R ⧸ (t^n)` the ideal
`(t)/(t^n)` is NILPOTENT, and for a nilpotent ideal the local criterion of
flatness is unconditional.

**THE ROUTE, AS ACTUALLY TAKEN — AND THERE IS NO INDUCTION ON `n`.**  The
previous version of this docstring said "induct on `n`"; that is unnecessary,
and noticing it is what made the reduction short.  The local criterion applies
ONCE, at the given `n`, with `A = R ⧸ (t^n)`, `J = (t)/(t^n)`,
`M = B = T ⧸ (φ t)^n`.  Its three inputs are discharged here as follows.

* `J ^ n = ⊥`, since `J = (t̄)` and `t̄^n = 0` in `A`.
* `B ⧸ JB` is flat over `A ⧸ J` — this is `hflat` transported along the THIRD
  ISOMORPHISM THEOREM.  `DoubleQuot.quotQuotEquivQuotOfLE` (applied twice,
  once over `R` and once over `T`, using `(t^n) ≤ (t)` and `(φt)^n ≤ (φt)`)
  identifies `A ⧸ J ≃+* R ⧸ (t)` and `B ⧸ JB ≃+* T ⧸ (φ t)`, and the induced
  map is `ψ` conjugated by those two isomorphisms — so the flatness transports
  by `RingHom.Flat.comp` and `RingHom.Flat.of_bijective`, no module theory
  needed.
* `Tor₁^A(A ⧸ J, B) = 0`, i.e. `J ⊗[A] B → B` is injective.  **This is the one
  place regularity is spent**, and it is elementary because `J` is PRINCIPAL:
  every element of `J ⊗[A] B` is `t̄ ⊗ b` for a single `b` (pull the scalar
  across the tensor), so injectivity says exactly `t̄ b = 0 → t̄ ⊗ b = 0`.  And
  `t̄ b = 0` means `(φ t) x ∈ ((φ t)^n)` for a lift `x`, whence `x ∈ ((φ t)^{n-1})`
  BY `hTt`; so `b = t̄^{n-1} b'` and
  `t̄ ⊗ b = t̄ ⊗ t̄^{n-1} b' = (t̄^{n-1} t̄) ⊗ b' = t̄^n ⊗ b' = 0 ⊗ b' = 0`.

**`hRt` IS NOT USED, AND THAT IS A CORRECTION, NOT AN OVERSIGHT** (2026-07-27).
The task that produced this proof was told that both `hRt` and `hTt` are
load-bearing, "checked by re-deriving the chase".  That is true of the chase the
docstring above used to prescribe — computing `Tor₁^A(A ⧸ J, B)` as the homology
of the PERIODIC PRESENTATION `A --(t^{n-1})--> A --t--> A → A ⧸ J → 0`, whose
exactness at the middle is precisely `ker(t̄ ·) = (t̄^{n-1})` on `A` and therefore
does need `t` regular on `R`.  Equivalently: in the form
"`Ann_B(t̄) = Ann_A(t̄) · B`", the right-hand side is `(t̄^{n-1}) B` only because of
`hRt`.  But the injectivity of `J ⊗[A] B → B` can be checked DIRECTLY, without
ever naming `Ann_A(t̄)` or a resolution of `A ⧸ J`, and then only `hTt` is
needed.  The hypothesis is kept in the signature (it costs the caller nothing —
`mem_pow_smul_of_lTensor_ideal_eq_zero` has it anyway) and is underscored so the
non-use is mechanically visible.

**NOTHING IS LEFT** (2026-07-27).  The one general statement consumed,
`Module.Flat.of_flat_quotient_of_pow_eq_bot` in
`Fermat/FLT/Mathlib/RingTheory/Flat/LocalCriterion.lean`, is now PROVEN.  The
measurement behind the cut still stands — **mathlib has no `Tor` long exact
sequence at this pin** (`CategoryTheory/Monoidal/Tor.lean` defines `Tor` but
proves only that higher `Tor` of a projective vanishes, and
`CategoryTheory/Abelian/LeftDerived.lean` has no connecting map at all) — but
neither of the two routes recorded there was the one taken: the criterion closed
over an elementary dévissage that never leaves the category of modules, needing
only right-exactness of `- ⊗ M` and a free presentation.  That is a THEORY
BUILD, which is exactly why it belongs in the shim tree and not inside this
7000-line module.

**FAITHFULNESS.**  `ψn` is passed as DATA together with its intertwining
`hψn`, for the same reason `ψ` is in the atom: the map is
`Ideal.quotientMap (Ideal.span {(algebraMap R T t)^n}) (algebraMap R T) _`, and
taking it as data keeps the (one-line) construction of its side condition at
the call site.  Since `Ideal.Quotient.mk` is surjective, `hψn` determines `ψn`
uniquely, so this is not a weakening. -/
theorem flat_quotientMap_pow_of_flat_quotientMap
    [IsNoetherianRing R] [IsNoetherianRing T]
    {t : R} (_hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (algebraMap R T t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {algebraMap R T t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {algebraMap R T t})).comp (algebraMap R T))
    (hflat : ψ.Flat) (n : ℕ)
    (ψn : R ⧸ Ideal.span {t ^ n} →+* T ⧸ Ideal.span {(algebraMap R T t) ^ n})
    (hψn : ψn.comp (Ideal.Quotient.mk (Ideal.span {t ^ n}))
      = (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ n})).comp (algebraMap R T)) :
    ψn.Flat := by
  rcases n with _ | m
  · -- `n = 0`: `(t^0) = (1) = ⊤`, so both quotients are the zero ring and every
    -- module over the zero ring is flat.
    have hR0 : Ideal.span {t ^ 0} = (⊤ : Ideal R) := by
      rw [pow_zero]; exact Ideal.span_singleton_one
    have hT0 : Ideal.span {(algebraMap R T t) ^ 0} = (⊤ : Ideal T) := by
      rw [pow_zero]; exact Ideal.span_singleton_one
    haveI : Subsingleton (R ⧸ Ideal.span {t ^ 0}) := Ideal.Quotient.subsingleton_iff.mpr hR0
    haveI : Subsingleton (T ⧸ Ideal.span {(algebraMap R T t) ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr hT0
    algebraize [ψn]
    exact Module.Flat.of_linearEquiv (M := R ⧸ Ideal.span {t ^ 0})
      { toFun := fun _ => 0
        map_add' := fun _ _ => Subsingleton.elim _ _
        map_smul' := fun _ _ => Subsingleton.elim _ _
        invFun := fun _ => 0
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  · algebraize [ψn]
    have hle : Ideal.span {t ^ (m + 1)} ≤ Ideal.span {t} := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      exact dvd_pow_self t (Nat.succ_ne_zero m)
    have hleT : Ideal.span {(algebraMap R T t) ^ (m + 1)}
        ≤ Ideal.span {algebraMap R T t} := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      exact dvd_pow_self _ (Nat.succ_ne_zero m)
    have hJspan : (Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}))
        = Ideal.span {(Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t)} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hθmem : (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t)
        ∈ (Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})) := by
      rw [hJspan]; exact Ideal.mem_span_singleton_self _
    have hψnt : (algebraMap (R ⧸ Ideal.span {t ^ (m + 1)})
          (T ⧸ Ideal.span {(algebraMap R T t) ^ (m + 1)}))
          (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t)
        = Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)}) (algebraMap R T t) := by
      rw [RingHom.algebraMap_toAlgebra]
      exact RingHom.congr_fun hψn t
    have hJT : Ideal.map (algebraMap (R ⧸ Ideal.span {t ^ (m + 1)})
          (T ⧸ Ideal.span {(algebraMap R T t) ^ (m + 1)}))
          ((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})))
        = (Ideal.span {algebraMap R T t}).map
            (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)})) := by
      rw [RingHom.algebraMap_toAlgebra, Ideal.map_map, hψn, ← Ideal.map_map, Ideal.map_span,
        Set.image_singleton]
    refine Module.Flat.of_flat_quotient_of_pow_eq_bot
      ((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}))) (m + 1) ?_ ?_ ?_
    · -- `J ^ n = ⊥`, because `J = (t̄)` and `t̄ ^ n = 0`.
      have h0 : (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})) (t ^ (m + 1)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hJspan, Ideal.span_singleton_pow, ← map_pow, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    · -- `B ⧸ JB` is flat over `A ⧸ J`: this is `hflat` conjugated by the two
      -- third-isomorphism-theorem identifications.
      rw [← RingHom.flat_algebraMap_iff]
      have heq : (algebraMap ((R ⧸ Ideal.span {t ^ (m + 1)}) ⧸
            (Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})))
          ((T ⧸ Ideal.span {(algebraMap R T t) ^ (m + 1)}) ⧸
            Ideal.map (algebraMap (R ⧸ Ideal.span {t ^ (m + 1)})
              (T ⧸ Ideal.span {(algebraMap R T t) ^ (m + 1)}))
              ((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}))))) =
          (Ideal.quotEquivOfEq hJT).symm.toRingHom.comp
            ((DoubleQuot.quotQuotEquivQuotOfLE hleT).symm.toRingHom.comp
              (ψ.comp (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom)) := by
        refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_))
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        have h1 : (DoubleQuot.quotQuotEquivQuotOfLE hle)
              ((Ideal.Quotient.mk
                  ((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}))))
                ((Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})) r))
            = Ideal.Quotient.mk (Ideal.span {t}) r :=
          DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hle
        have h2 : ψ (Ideal.Quotient.mk (Ideal.span {t}) r)
            = Ideal.Quotient.mk (Ideal.span {algebraMap R T t}) (algebraMap R T r) :=
          RingHom.congr_fun hψ r
        have h3 : (DoubleQuot.quotQuotEquivQuotOfLE hleT).symm
              (Ideal.Quotient.mk (Ideal.span {algebraMap R T t}) (algebraMap R T r))
            = Ideal.Quotient.mk
                ((Ideal.span {algebraMap R T t}).map
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)})))
                (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)})
                  (algebraMap R T r)) :=
          DoubleQuot.quotQuotEquivQuotOfLE_symm_mk _ hleT
        rw [h1, h2, h3, Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
        show Ideal.Quotient.mk _ (ψn ((Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})) r)) = _
        exact congrArg _ (RingHom.congr_fun hψn r)
      rw [heq]
      exact RingHom.Flat.comp
        (RingHom.Flat.comp
          (RingHom.Flat.comp
            (RingHom.Flat.of_bijective (f := (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom)
              (DoubleQuot.quotQuotEquivQuotOfLE hle).bijective)
            hflat)
          (RingHom.Flat.of_bijective
            (f := (DoubleQuot.quotQuotEquivQuotOfLE hleT).symm.toRingHom)
            (DoubleQuot.quotQuotEquivQuotOfLE hleT).symm.bijective))
        (RingHom.Flat.of_bijective (f := (Ideal.quotEquivOfEq hJT).symm.toRingHom)
          (Ideal.quotEquivOfEq hJT).symm.bijective)
    · -- `Tor₁^A(A ⧸ J, B) = 0`: `J ⊗[A] B → B` is injective.  This is the only
      -- step that uses regularity, and it uses only `hTt`.
      set θ := (⟨Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t, hθmem⟩ :
        ↥((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})))) with hθ
      -- `J` is principal, so every element of `J ⊗ B` is `t̄ ⊗ b` for a single `b`.
      have hgen : ∀ ξ : (↥((Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)})))
          ⊗[R ⧸ Ideal.span {t ^ (m + 1)}] (T ⧸ Ideal.span {(algebraMap R T t) ^ (m + 1)})),
          ∃ b, ξ = θ ⊗ₜ[R ⧸ Ideal.span {t ^ (m + 1)}] b := by
        intro ξ
        induction ξ using TensorProduct.induction_on with
        | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
        | tmul x b =>
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
              (show (x : R ⧸ Ideal.span {t ^ (m + 1)})
                ∈ Ideal.span {(Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t)} by
                rw [← hJspan]; exact x.2)
            refine ⟨c • b, ?_⟩
            have hx : x = c • θ := Subtype.ext (by rw [hθ]; exact hc.symm)
            rw [hx, TensorProduct.smul_tmul]
        | add x y hx hy =>
            obtain ⟨b₁, rfl⟩ := hx
            obtain ⟨b₂, rfl⟩ := hy
            exact ⟨b₁ + b₂, (TensorProduct.tmul_add _ _ _).symm⟩
      rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨b, rfl⟩ := hgen ξ
      rw [TensorProduct.lift.tmul] at hξ
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.lsmul_apply] at hξ
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hθ] at hξ
      rw [Algebra.smul_def, hψnt, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton'] at hξ
      obtain ⟨c, hc⟩ := hξ
      -- `(φ t) x ∈ ((φ t)^{m+1})` and `φ t` regular on `T` give `x ∈ ((φ t)^m)`.
      have hx : x = c * (algebraMap R T t) ^ m := by
        apply hTt
        show (algebraMap R T t) • x = (algebraMap R T t) • (c * (algebraMap R T t) ^ m)
        simp only [smul_eq_mul]
        rw [← hc]; ring
      subst hx
      have hb : (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)}))
            (c * (algebraMap R T t) ^ m)
          = ((Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t) ^ m) •
            (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)}) c) := by
        rw [Algebra.smul_def, map_pow, hψnt,
          ← map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ (m + 1)})), ← map_mul]
        congr 1
        ring
      rw [hb, ← TensorProduct.smul_tmul]
      have hzero : ((Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t) ^ m) • θ = 0 := by
        refine Subtype.ext ?_
        rw [hθ]
        show ((Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t) ^ m) •
          (Ideal.Quotient.mk (Ideal.span {t ^ (m + 1)}) t) = (0 : R ⧸ Ideal.span {t ^ (m + 1)})
        rw [smul_eq_mul, ← pow_succ, ← map_pow]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hzero, TensorProduct.zero_tmul]

/-- **THE DESCENT MODULO `t ^ n`** (**PROVEN 2026-07-27**; pure commutative
algebra, the elementwise core of Stacks 00MK / Matsumura 22.3).

Write `I = (t) ⊆ R`, `𝔞 ⊆ R` an ideal, and let `ξ ∈ T ⊗[R] 𝔞` map to `0` in
`T` under `𝔞 ⊗ T → T`.  Given only that `T ⧸ (φ t)^n` is FLAT over
`R ⧸ (t)^n`, this says

  `ξ ∈ baseChange T (𝔞 ⊓ (t^n)) + (φ t)^n · (T ⊗[R] 𝔞)`.

**WHY THIS IS THE OTHER HALF, AND WHY THE STATEMENT LOOKS LIKE THIS.**  The
consumer `mem_pow_smul_of_lTensor_ideal_eq_zero` below feeds Artin–Rees into
the first summand (`𝔞 ⊓ (t^n) ⊆ t^{n-k} 𝔞`) and `n ≥ m` into the second, and
then Krull's intersection theorem kills the kernel.  So this leaf is exactly
"the kernel dies modulo `t^n`, up to the Artin–Rees discrepancy", with the
discrepancy left explicit rather than estimated here — that is what makes the
two halves independent.

**THE ROUTE — a four-term chase, all four maps already in mathlib.**  Put
`J = (t^n) ⊆ R`, `J' = ((φ t)^n) ⊆ T`, `Rₙ = R ⧸ J`, `Tₙ = T ⧸ J'`,
`𝔞ₙ = 𝔞.map (Ideal.Quotient.mk J) ⊆ Rₙ`.  Consider

  `T ⊗[R] 𝔞  --a-->  Tₙ ⊗[R] 𝔞  --b-->  Tₙ ⊗[Rₙ] 𝔞ₙ  --c-->  Tₙ`.

* `c` is injective — this is `hpow` through `Module.Flat.iff_lTensor_injective`;
* `c ∘ b ∘ a` sends `ξ` to the image in `Tₙ` of `lTensor T 𝔞.subtype ξ = 0`,
  so `b (a ξ) = 0`;
* `ker b` is the image of `Tₙ ⊗[R] ↥(𝔞 ⊓ J)`, i.e.
  `Submodule.baseChange Tₙ (comap 𝔞.subtype J)`, by right-exactness of
  `Tₙ ⊗[R] -` applied to `(𝔞 ⊓ J) → 𝔞 → 𝔞ₙ → 0`
  (`Submodule.baseChange` IS that image: `Submodule.baseChange_eq_span`);
* `ker a = J' • ⊤`, by right-exactness of `- ⊗[R] 𝔞` on `J' → T → Tₙ → 0`;
* `a` is surjective and carries `baseChange T P` onto `baseChange Tₙ P`, so
  `a⁻¹ (baseChange Tₙ P) = baseChange T P ⊔ ker a`.  That is the conclusion.

**WHAT MATHLIB SUPPLIES** (all already in this file's import cone):
`Submodule.baseChange`, `baseChange_eq_span`, `baseChange_mono`,
`tmul_mem_baseChange_of_mem`, `toBaseChange_surjective`
(`Mathlib/LinearAlgebra/TensorProduct/Tower.lean`);
`TensorProduct.quotientTensorEquiv`, `tensorQuotientEquiv`,
`quotTensorEquivQuotSMul`, `Ideal.subtype_rTensor_range`
(`Mathlib/{LinearAlgebra,RingTheory}/TensorProduct/Quotient.lean`);
`LinearMap.lTensor_exact` / `rTensor_exact` and the right-exactness API in
`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`.

**NO HYPOTHESIS ON `R`, `T` BEYOND COMMUTATIVITY IS NEEDED HERE.**  Noetherian,
local and `IsLocalHom` are used only by the consumer (Artin–Rees needs
noetherian; Krull needs local).  Keeping them off this leaf is deliberate: it
makes clear that the separatedness input enters exactly once, in the
consumer.

**THE CONCRETE LEAN ATTACK — DO NOT TRY TO COMPUTE `ker b` DIRECTLY**
(worked out 2026-07-27; identifying `ker b` as an image is the step that turns
a two-page chase into a two-week one).  Write `N` for the target submodule
(the `⊔` in the conclusion) and `Q := (T ⊗[R] 𝔞) ⧸ N`.  Build TWO maps and
never mention a kernel:

* `F : T ⊗[R] 𝔞 → Tₙ ⊗[Rₙ] 𝔞ₙ`, `y ⊗ a ↦ (mk y) ⊗ (mk a)`.  This is
  `R`-balanced because `mk (r • y) = mk r • mk y` on both sides, so
  `TensorProduct.lift` builds it.
* `G : Tₙ ⊗[Rₙ] 𝔞ₙ → Q`, `ȳ ⊗ ā ↦ ⟦y ⊗ a⟧` for ANY lifts.  Well defined
  exactly because of the two summands of `N`, one each:
  changing the lift of `ȳ` moves the value by `(y - y') ⊗ a ∈ J' • ⊤`;
  changing the lift of `ā` moves it by `y ⊗ (a - a')` with
  `a - a' ∈ 𝔞 ⊓ J`, i.e. into `baseChange T (comap 𝔞.subtype J)`
  (`Submodule.tmul_mem_baseChange_of_mem`).  **This is where the shape of the
  conclusion comes from, and it is why the two summands are exactly these.**

Then `G ∘ F = Submodule.mkQ N` (check on `y ⊗ a`), so `F ξ = 0` gives `ξ ∈ N`
with no kernel computation at all.  And `F ξ = 0` is the only place flatness
is used: `c : Tₙ ⊗[Rₙ] 𝔞ₙ → Tₙ`, the `lift (lsmul ∘ 𝔞ₙ.subtype)` of
`Module.Flat.iff_lift_lsmul_comp_subtype_injective`, is INJECTIVE by `hpow`,
and `c (F ξ)` is the image in `Tₙ` of `lift (lsmul ∘ 𝔞.subtype) ξ`, which is
`0` by `hξ`.

**THE INSTANCE HAZARD ON THIS ROUTE**, since it is what will actually cost
time: `Q` is a `T`-module, and `G`'s source is an `Rₙ`-module, so a bare
`TensorProduct.lift` for `G` needs `Module Rₙ Q` — which is NOT an instance
(`Module Rₙ M` from `Module Tₙ M` and `Algebra Rₙ Tₙ` does not fire on its
own).  Either supply it explicitly from `ψn.toAlgebra` and note `J' • ⊤ ≤ N`
makes `Q` a `Tₙ`-module, or build `F` and `G` as bare `AddMonoidHom`s — only
additivity is used above.

**HOW IT WAS ACTUALLY PROVED (2026-07-27), and the two facts worth keeping.**
The plan above was executed VERBATIM, with `F` and `G` built as bare
`AddMonoidHom`s through `TensorProduct.liftAddHom` (which asks only for
additivity in each slot plus the `R`-balancing `f (r • m) n = f m (r • n)`).
Two concrete points that the plan leaves implicit and that are where the
Lean work actually sits:

* **`Module T (X →ₗ[R] Q)` does NOT synthesise, but `Module T (X →+ Q)`
  does.**  So the descent of `y ↦ (a ↦ ⟦y ⊗ a⟧)` along `T ↠ Tₙ` — done with
  `Submodule.liftQ` over `T` — must be valued in the ADDITIVE hom type.  It
  is then merely `y ↦ y • W` for the single `W : 𝔞ₙ →+ Q`, so `T`-linearity
  is `add_smul`/`mul_smul` and the vanishing on `J'` is
  `J' • ⊤ ≤ N`.
* **Mapping OUT of `↥𝔞ₙ` needs `↥𝔞ₙ` presented as a quotient.**
  `𝔞ₙ = 𝔞.map (Ideal.Quotient.mk J)` is a submodule, not a quotient, so `W`
  is built as `(P.liftQ … ) ∘ E.symm` for the `R`-linear equivalence
  `E : (↥𝔞 ⧸ P) ≃ₗ[R] ↥𝔞ₙ` obtained from `LinearEquiv.ofBijective`, where
  `P = comap 𝔞.subtype J` is exactly `ker (𝔞 → 𝔞ₙ)`.  That kernel
  computation is the FIRST summand of the conclusion, appearing here rather
  than in a right-exactness argument.

Flatness enters exactly once, as advertised: `Module.Flat`'s
`lTensor_preserves_injective_linearMap` applied to `𝔞ₙ.subtype`, composed
with `TensorProduct.rid`.  No `Tor`, no exact sequence, no Artin–Rees. -/
theorem mem_baseChange_sup_of_flat_quotientMap_pow
    {t : R} (n : ℕ)
    (hpow : ∀ ψn : R ⧸ Ideal.span {t ^ n} →+* T ⧸ Ideal.span {(algebraMap R T t) ^ n},
      ψn.comp (Ideal.Quotient.mk (Ideal.span {t ^ n}))
          = (Ideal.Quotient.mk (Ideal.span {(algebraMap R T t) ^ n})).comp (algebraMap R T) →
        ψn.Flat)
    {𝔞 : Ideal R} (ξ : T ⊗[R] ↥𝔞) (hξ : LinearMap.lTensor T 𝔞.subtype ξ = 0) :
    ξ ∈ (Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)).baseChange T
      ⊔ (Ideal.span {(algebraMap R T t) ^ n} • (⊤ : Submodule T (T ⊗[R] ↥𝔞))) := by
  classical
  set J : Ideal R := Ideal.span {t ^ n} with hJdef
  set J' : Ideal T := Ideal.span {(algebraMap R T t) ^ n} with hJ'def
  -- the induced map on the quotients, and its flatness
  have hcomap : J ≤ J'.comap (algebraMap R T) := by
    rw [hJdef, Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, hJ'def]
    exact Ideal.subset_span rfl
  set ψn : R ⧸ J →+* T ⧸ J' := Ideal.quotientMap J' (algebraMap R T) hcomap with hψndef
  have hψncomp : ψn.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp (algebraMap R T) :=
    Ideal.quotientMap_comp_mk hcomap
  have hflat : ψn.Flat := hpow ψn hψncomp
  letI : Algebra (R ⧸ J) (T ⧸ J') := ψn.toAlgebra
  haveI : Module.Flat (R ⧸ J) (T ⧸ J') := hflat
  have hsmulT : ∀ (s : R ⧸ J) (x : T ⧸ J'), s • x = ψn s * x := fun s x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hψnmk : ∀ r : R, ψn (Ideal.Quotient.mk J r) = Ideal.Quotient.mk J' (algebraMap R T r) :=
    fun r => by rw [hψndef]; exact Ideal.quotientMap_mk
  -- abbreviations
  set 𝔞n : Ideal (R ⧸ J) := 𝔞.map (Ideal.Quotient.mk J) with h𝔞ndef
  set P : Submodule R ↥𝔞 := Submodule.comap 𝔞.subtype J with hPdef
  set N : Submodule T (T ⊗[R] ↥𝔞) :=
    P.baseChange T ⊔ (J' • (⊤ : Submodule T (T ⊗[R] ↥𝔞))) with hNdef
  -- the surjection `𝔞 → 𝔞ₙ`, whose kernel is the first summand of the conclusion
  let qmap : ↥𝔞 →ₗ[R] ↥𝔞n :=
    { toFun := fun a => ⟨Ideal.Quotient.mk J (a : R), Ideal.mem_map_of_mem _ a.2⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by
        intro r a
        ext
        simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] }
  have hqmap : ∀ a : ↥𝔞, (qmap a : R ⧸ J) = Ideal.Quotient.mk J (a : R) := fun a => rfl
  have hqsurj : Function.Surjective qmap := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).1 hx
    exact ⟨⟨a, ha⟩, rfl⟩
  have hqker : LinearMap.ker qmap = P := by
    ext a
    rw [LinearMap.mem_ker, Subtype.ext_iff, hqmap]
    simp [hPdef, Ideal.Quotient.eq_zero_iff_mem]
  let ebar : (↥𝔞 ⧸ P) →ₗ[R] ↥𝔞n := P.liftQ qmap hqker.ge
  have hebij : Function.Bijective ebar := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot' P qmap hqker.symm
    · intro y
      obtain ⟨a, rfl⟩ := hqsurj y
      exact ⟨P.mkQ a, rfl⟩
  let E : (↥𝔞 ⧸ P) ≃ₗ[R] ↥𝔞n := LinearEquiv.ofBijective ebar hebij
  have hEsymm : ∀ a : ↥𝔞, E.symm (qmap a) = P.mkQ a := by
    intro a
    have h : E (P.mkQ a) = qmap a := rfl
    rw [← h, E.symm_apply_apply]
  -- `J'` annihilates `Q := (T ⊗[R] 𝔞) ⧸ N`: that is the second summand
  have hJQ : ∀ y ∈ J', ∀ q : (T ⊗[R] ↥𝔞) ⧸ N, y • q = 0 := by
    intro y hy q
    obtain ⟨w, rfl⟩ := N.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul hy Submodule.mem_top)
  -- `G : Tₙ ⊗[Rₙ] 𝔞ₙ → Q`
  let b1 : ↥𝔞 →ₗ[R] ((T ⊗[R] ↥𝔞) ⧸ N) :=
    (N.mkQ.restrictScalars R).comp (TensorProduct.mk R T ↥𝔞 1)
  have hb1 : P ≤ LinearMap.ker b1 := by
    intro a ha
    rw [LinearMap.mem_ker]
    show N.mkQ ((1 : T) ⊗ₜ[R] a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left (Submodule.tmul_mem_baseChange_of_mem 1 ha)
  let W : ↥𝔞n →+ ((T ⊗[R] ↥𝔞) ⧸ N) :=
    (P.liftQ b1 hb1).toAddMonoidHom.comp E.symm.toLinearMap.toAddMonoidHom
  have hW : ∀ a : ↥𝔞, W (qmap a) = N.mkQ ((1 : T) ⊗ₜ[R] a) := by
    intro a
    show (P.liftQ b1 hb1) (E.symm (qmap a)) = _
    rw [hEsymm, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  let bl0 : T →ₗ[T] (↥𝔞n →+ ((T ⊗[R] ↥𝔞) ⧸ N)) :=
    { toFun := fun y => y • W
      map_add' := fun y y' => add_smul y y' W
      map_smul' := fun c y => mul_smul c y W }
  have hbl0 : ∀ (y : T) (x : ↥𝔞n), bl0 y x = y • W x := fun y x => rfl
  have hbl0ker : J' ≤ LinearMap.ker bl0 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext x
    rw [hbl0]
    exact hJQ y hy _
  let g0 : (T ⧸ J') →ₗ[T] (↥𝔞n →+ ((T ⊗[R] ↥𝔞) ⧸ N)) := J'.liftQ bl0 hbl0ker
  let g' : (T ⧸ J') →+ (↥𝔞n →+ ((T ⊗[R] ↥𝔞) ⧸ N)) := g0.toAddMonoidHom
  have hg0val : ∀ (y : T) (a : ↥𝔞),
      g' (Ideal.Quotient.mk J' y) (qmap a) = N.mkQ (y ⊗ₜ[R] (a : ↥𝔞)) := by
    intro y a
    show g0 (Submodule.Quotient.mk y) (qmap a) = _
    rw [Submodule.liftQ_apply, hbl0, hW, ← map_smul]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hgbal : ∀ (s : R ⧸ J) (y : T ⧸ J') (x : ↥𝔞n), g' (s • y) x = g' y (s • x) := by
    intro s y x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hqsurj x
    have hs : (Ideal.Quotient.mk J r) • (Ideal.Quotient.mk J' y)
        = Ideal.Quotient.mk J' (algebraMap R T r * y) := by
      rw [hsmulT, hψnmk, map_mul]
    have hx : (Ideal.Quotient.mk J r) • qmap a = qmap (r • a) := by
      ext
      rw [hqmap]
      show (Ideal.Quotient.mk J r) * (qmap a : R ⧸ J) = _
      rw [hqmap, ← map_mul]
      rfl
    rw [hs, hx, hg0val, hg0val, ← Algebra.smul_def, TensorProduct.smul_tmul]
  let G : ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n) →+ ((T ⊗[R] ↥𝔞) ⧸ N) :=
    TensorProduct.liftAddHom (R := R ⧸ J) g' hgbal
  -- `F : T ⊗[R] 𝔞 → Tₙ ⊗[Rₙ] 𝔞ₙ`
  let mkAdd : (T ⧸ J') →+ (↥𝔞n →+ ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n)) :=
    LinearMap.toAddMonoidHom'.comp (TensorProduct.mk (R ⧸ J) (T ⧸ J') ↥𝔞n).toAddMonoidHom
  let precompQ : (↥𝔞n →+ ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n)) →+ (↥𝔞 →+ ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n)) :=
    AddMonoidHom.mk' (fun h => h.comp qmap.toAddMonoidHom) (fun _ _ => rfl)
  let f : T →+ (↥𝔞 →+ ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n)) :=
    precompQ.comp (mkAdd.comp (Ideal.Quotient.mk J' : T →+* T ⧸ J').toAddMonoidHom)
  have hfval : ∀ (y : T) (a : ↥𝔞),
      f y a = (Ideal.Quotient.mk J' y) ⊗ₜ[R ⧸ J] (qmap a) := fun y a => rfl
  have hfbal : ∀ (r : R) (y : T) (a : ↥𝔞), f (r • y) a = f y (r • a) := by
    intro r y a
    rw [hfval, hfval]
    have h1 : (Ideal.Quotient.mk J' (r • y))
        = (Ideal.Quotient.mk J r) • (Ideal.Quotient.mk J' y) := by
      rw [hsmulT, hψnmk, ← map_mul, Algebra.smul_def]
    have h2 : qmap (r • a) = (Ideal.Quotient.mk J r) • qmap a := by
      ext
      rw [hqmap]
      show _ = (Ideal.Quotient.mk J r) * (qmap a : R ⧸ J)
      rw [hqmap, ← map_mul]
      rfl
    rw [h1, h2, TensorProduct.smul_tmul]
  let F : (T ⊗[R] ↥𝔞) →+ ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n) := TensorProduct.liftAddHom f hfbal
  have hFval : ∀ (y : T) (a : ↥𝔞),
      F (y ⊗ₜ[R] a) = (Ideal.Quotient.mk J' y) ⊗ₜ[R ⧸ J] (qmap a) := fun y a => rfl
  -- `G ∘ F = mkQ N`, so `F ξ = 0` will give `ξ ∈ N` with no kernel computation
  have hGF : ∀ z : T ⊗[R] ↥𝔞, G (F z) = N.mkQ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul y a =>
      rw [hFval]
      show g' (Ideal.Quotient.mk J' y) (qmap a) = _
      exact hg0val y a
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
  -- the ONLY use of flatness: `c` is injective
  let c : ((T ⧸ J') ⊗[R ⧸ J] ↥𝔞n) →ₗ[R ⧸ J] (T ⧸ J') :=
    (TensorProduct.rid (R ⧸ J) (T ⧸ J')).toLinearMap.comp
      (LinearMap.lTensor (T ⧸ J') 𝔞n.subtype)
  have hcinj : Function.Injective c := by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := T ⧸ J') 𝔞n.subtype
      𝔞n.injective_subtype ((TensorProduct.rid (R ⧸ J) (T ⧸ J')).injective hxy)
  have hcF : ∀ z : T ⊗[R] ↥𝔞, c (F z)
      = Ideal.Quotient.mk J' ((TensorProduct.rid R T) (LinearMap.lTensor T 𝔞.subtype z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero]
    | tmul y a =>
      rw [hFval]
      show (TensorProduct.rid (R ⧸ J) (T ⧸ J'))
        (LinearMap.lTensor (T ⧸ J') 𝔞n.subtype
          ((Ideal.Quotient.mk J' y) ⊗ₜ[R ⧸ J] (qmap a))) = _
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul]
      show (qmap a : R ⧸ J) • (Ideal.Quotient.mk J' y) = _
      rw [hsmulT, hqmap, hψnmk, ← map_mul, Submodule.subtype_apply, Algebra.smul_def]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add, map_add]
  have hFxi : F ξ = 0 := by
    apply hcinj
    rw [hcF, hξ, map_zero, map_zero, map_zero]
  have hmk : N.mkQ ξ = 0 := by rw [← hGF, hFxi, map_zero]
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk

/-- The base change of `t ^ m · 𝔞` sits inside `(φ t)^m · (T ⊗[R] 𝔞)`
(**PROVEN 2026-07-27**).  Pure bookkeeping: `1 ⊗ (r • x) = φ r • (1 ⊗ x)`,
and `φ` carries `(t^m)` into `(φ t)^m`. -/
theorem baseChange_smul_top_le_pow_smul_top (t : R) (m : ℕ) (𝔞 : Ideal R) :
    ((Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞)).baseChange T
      ≤ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
        (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨q, hq, rfl⟩
  simp only [TensorProduct.mk_apply, SetLike.mem_coe]
  refine Submodule.smul_induction_on hq ?_ ?_
  · intro r hr x _
    have hr' : algebraMap R T r ∈ (Ideal.span {algebraMap R T t} : Ideal T) ^ m := by
      rw [Ideal.span_singleton_pow, ← map_pow]
      rw [Ideal.mem_span_singleton] at hr ⊢
      exact map_dvd _ hr
    have key : (1 : T) ⊗ₜ[R] (r • x) = algebraMap R T r • ((1 : T) ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
        Algebra.algebraMap_eq_smul_one]
    rw [key]
    exact Submodule.smul_mem_smul hr' Submodule.mem_top
  · intro x y hx hy
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- **THE KERNEL OF `𝔞 ⊗ T → T` LIES IN EVERY POWER OF `(φ t)`**
(**PROVEN 2026-07-27** over the two leaves above — this is the ARTIN–REES half
of the local criterion of flatness).

Given `ξ ∈ T ⊗[R] 𝔞` killed by `𝔞 ⊗ T → T`, and any `m`, we get
`ξ ∈ (φ t)^m · (T ⊗[R] 𝔞)`.  Together with Krull's intersection theorem (in
`flat_of_flat_quotient_isSMulRegular` below) this forces `ξ = 0`, which is
flatness.

**THE PROOF, and the two mathlib facts it turns on.**  Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`, `Mathlib/RingTheory/Filtration.lean` —
it IS in the pin, contrary to what one might expect) gives `k` with
`(t)^n ⊓ 𝔞 = (t)^{n-k} • ((t)^k ⊓ 𝔞)` for `n ≥ k`; take `n = m + k`, so
`𝔞 ⊓ (t^n) ⊆ t^m 𝔞`.  Feeding that into
`mem_baseChange_sup_of_flat_quotientMap_pow` at this `n`, the first summand
lands in `(φ t)^m · (T ⊗ 𝔞)` by `baseChange_smul_top_le_pow_smul_top`, and the
second does because `n ≥ m`.

`ψ`, `hψ`, `hflat`, `hRt`, `hTt` are threaded through only to supply
`flat_quotientMap_pow_of_flat_quotientMap`. -/
theorem mem_pow_smul_of_lTensor_ideal_eq_zero
    [IsNoetherianRing R] [IsNoetherianRing T]
    {t : R} (hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (algebraMap R T t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {algebraMap R T t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {algebraMap R T t})).comp (algebraMap R T))
    (hflat : ψ.Flat)
    {𝔞 : Ideal R} (ξ : T ⊗[R] ↥𝔞)
    (hξ : LinearMap.lTensor T 𝔞.subtype ξ = 0) (m : ℕ) :
    ξ ∈ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
      (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {t} : Ideal R) (M := R) 𝔞
  set n := m + k with hn
  have hAR : ((Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R) ⊓ (𝔞 : Submodule R R))
      ≤ Submodule.map 𝔞.subtype ((Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞)) := by
    rw [hk n (by omega), show n - k = m from by omega]
    refine Submodule.smul_le.2 fun r hr y hy => ?_
    refine Submodule.mem_map.2 ⟨r • ⟨y, hy.2⟩, ?_, rfl⟩
    exact Submodule.smul_mem_smul (by rwa [Ideal.span_singleton_pow] at hr) Submodule.mem_top
  have hcomap : Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)
      ≤ (Ideal.span {t ^ m} : Ideal R) • (⊤ : Submodule R ↥𝔞) := by
    intro x hx
    have h1 : (x : R) ∈ (Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R)
        ⊓ (𝔞 : Submodule R R) := by
      refine ⟨?_, x.2⟩
      have hsmul : (Ideal.span {t} : Ideal R) ^ n • (⊤ : Submodule R R)
          = ((Ideal.span {t} : Ideal R) ^ n : Submodule R R) := by
        rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
      rw [hsmul, Ideal.span_singleton_pow]
      exact hx
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 (hAR h1)
    have hxy' : y = x := Subtype.ext hxy
    exact hxy' ▸ hy
  have hmem := mem_baseChange_sup_of_flat_quotientMap_pow (T := T) (t := t) n
    (fun ψn hψn => flat_quotientMap_pow_of_flat_quotientMap hRt hTt ψ hψ hflat n ψn hψn) ξ hξ
  have hle : (Submodule.comap 𝔞.subtype (Ideal.span {t ^ n} : Ideal R)).baseChange T
      ⊔ (Ideal.span {(algebraMap R T t) ^ n} • (⊤ : Submodule T (T ⊗[R] ↥𝔞)))
      ≤ (Ideal.span {algebraMap R T t} : Ideal T) ^ m •
        (⊤ : Submodule T (T ⊗[R] ↥𝔞)) := by
    refine sup_le ?_ ?_
    · exact (Submodule.baseChange_mono T hcomap).trans
        (baseChange_smul_top_le_pow_smul_top t m 𝔞)
    · refine Submodule.smul_mono_left ?_
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_le_pow_right (by omega)
  exact hle hmem

end LocalCriterionOfFlatness

/-- **THE ONE-ELEMENT LOCAL CRITERION OF FLATNESS — THE ATOM**
(**PROVEN 2026-07-27** over the two leaves
`flat_quotientMap_pow_of_flat_quotientMap` and
`mem_baseChange_sup_of_flat_quotientMap_pow` stated immediately above —
pure commutative algebra; Matsumura *Commutative Ring Theory*
22.3 / Stacks 00MK in the length-one case.  Absent from mathlib, from
`~/cs/FLT` and from this project).

`R`, `T` noetherian local, `φ : R → T` a local homomorphism, `t ∈ 𝔪_R` a
nonzerodivisor on `R` and on `T`, and `T ⧸ tT` flat over `R ⧸ tR`.  Then `T` is
flat over `R`.

**THIS IS THE WHOLE CONTENT OF `flat_of_isWeaklyRegular_span_eq_maximalIdeal`
BELOW, WHICH IS NOW PROVEN OVER IT** (2026-07-27).  The list induction that
lemma's own docstring predicted to be "mechanical" is mechanical, and it is
written out in `flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` below: nothing
is left there but this statement.

**WHY THE INDUCED MAP IS PASSED AS DATA (`ψ`) RATHER THAN CONSTRUCTED.**  The
map `R ⧸ (t) → T ⧸ (φ t)` is `Ideal.quotientMap (Ideal.span {φ t}) φ h`, whose
`h : Ideal.span {t} ≤ (Ideal.span {φ t}).comap φ` would have to appear inside
this signature.  Taking `ψ` together with the intertwining `hψ` says exactly the
same thing, keeps the proof obligation at the call site where it is one line,
and lets a prover of this leaf use whichever description of `ψ` is convenient.

**FAITHFULNESS — the separatedness hypothesis is present, disguised as
`[IsNoetherianRing T] [IsLocalRing T] [IsLocalHom φ]`, and it is LOAD-BEARING.**
The classical criterion needs `T` to be `𝔪_R`-adically *ideally separated*; the
statement is false for an arbitrary `R`-module with a regular element acting
regularly.  Here it is automatic: `φ` local gives `𝔪_R T ⊆ 𝔪_T`, hence
`𝔪_R^n T ⊆ 𝔪_T^n`, so `⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` by Krull's intersection
theorem.  **A prover who weakens `T` to a bare `R`-module produces a FALSE
leaf.**

**WHAT MATHLIB HAS THAT A PROVER WILL WANT**, since there is no `Tor`:
`Module.Flat.iff_rTensor_injective` (`RingTheory/Flat/Basic.lean`) expresses
`Tor₁(R ⧸ I, M) = 0` as injectivity of `I ⊗ M → M`, which is enough to run the
argument without ever constructing derived functors;
`Module.Flat.of_isLocalized_maximal` and the equational criterion
(`RingTheory/Flat/EquationalCriterion.lean`) are the other two handles.
`RingHom.flat_algebraMap_iff` moves between `RingHom.Flat` and `Module.Flat`.

**THE CUT (2026-07-27), and what is still open.**  The classical proof splits
at exactly one place, and both halves are stated above:

1. `flat_quotientMap_pow_of_flat_quotientMap` — `T ⧸ (φ t)^n` is flat over
   `R ⧸ (t)^n` for all `n`.  This is the local criterion for a NILPOTENT
   ideal; no separatedness, no Artin–Rees.
2. `mem_baseChange_sup_of_flat_quotientMap_pow` — the elementwise descent of
   `ker(𝔞 ⊗ T → T)` modulo `t^n`, granted (1).  **PROVEN 2026-07-27**; (1) is
   the only half of the cut still open.

Everything else is now written out and PROVEN:
`mem_pow_smul_of_lTensor_ideal_eq_zero` feeds Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`) into (2), and this declaration closes with
Krull's intersection theorem
(`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) applied to the FINITE `T`-module
`T ⊗[R] 𝔞` — finite because `𝔞` is finitely generated, which is why
`Module.Flat.iff_lTensor_injective` (finitely generated ideals only) rather
than `iff_lTensor_injective'` is the right entry point.

**WHERE THE SEPARATEDNESS HYPOTHESIS IS ACTUALLY SPENT.**  Precisely twice in
this proof, and nowhere in leaf (2): `[IsLocalHom φ]` + `htm` give
`(φ t) ≠ ⊤`, and `[IsLocalRing T] [IsNoetherianRing T]` give Krull's theorem
for `T ⊗[R] 𝔞`.  That is the formal counterpart of the classical
`⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` remark above. -/
theorem flat_of_flat_quotient_isSMulRegular {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing T] [IsNoetherianRing T]
    (φ : R →+* T) [IsLocalHom φ] {t : R} (htm : t ∈ IsLocalRing.maximalIdeal R)
    (hRt : IsSMulRegular R t) (hTt : IsSMulRegular T (φ t))
    (ψ : R ⧸ Ideal.span {t} →+* T ⧸ Ideal.span {φ t})
    (hψ : ψ.comp (Ideal.Quotient.mk (Ideal.span {t}))
      = (Ideal.Quotient.mk (Ideal.span {φ t})).comp φ)
    (hflat : ψ.Flat) :
    φ.Flat := by
  letI : Algebra R T := φ.toAlgebra
  show Module.Flat R T
  rw [Module.Flat.iff_lTensor_injective]
  intro 𝔞 h𝔞
  haveI : Module.Finite R ↥𝔞 := Module.Finite.iff_fg.2 h𝔞
  haveI : Module.Finite T (TensorProduct R T ↥𝔞) := inferInstance
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  have hIne : (Ideal.span {φ t} : Ideal T) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact ((IsLocalRing.mem_maximalIdeal _).1 htm) (isUnit_of_map_unit φ t hu)
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
    (M := TensorProduct R T ↥𝔞) (Ideal.span {φ t}) hIne
  have hmem : ξ ∈ (⨅ i : ℕ, (Ideal.span {φ t} : Ideal T) ^ i •
      (⊤ : Submodule T (TensorProduct R T ↥𝔞))) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    exact mem_pow_smul_of_lTensor_ideal_eq_zero hRt hTt ψ hψ hflat ξ hξ i
  rw [hbot] at hmem
  simpa using hmem

/-- **THE INDUCTION CARRIER OF THE LOCAL CRITERION OF FLATNESS**
(**PROVEN 2026-07-27** over the one-element atom above).

Induction is on the LENGTH of the list rather than on the list itself, because
each step changes the pair of rings (`R, T` becomes `R ⧸ (t), T ⧸ (φ t)`) and a
`List R` cannot be recursed on across a change of `R`.

* Base: `rs = []` forces `𝔪_R = ⊥`, so `R` is a field and `RingHom.Flat.of_isField`
  applies — every ring is flat over a field, so **no hypothesis on `T` is used at
  the bottom of the induction**.
* Step: `isWeaklyRegular_cons_iff` splits both regularity hypotheses at the head;
  the tails transport to the quotient RINGS along `A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`
  followed by `isWeaklyRegular_map_algebraMap_iff`; the span hypothesis descends
  because `t ↦ 0`, so `Ideal.ofList` of the image of `t :: rs₀` is that of the
  image of `rs₀`; and `IsLocalHom ψ` follows from surjectivity of
  `Ideal.Quotient.mk` on the source. -/
theorem flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux (n : ℕ) :
    ∀ (R T : Type u) [CommRing R] [CommRing T] [IsLocalRing R] [IsNoetherianRing R]
      [IsLocalRing T] [IsNoetherianRing T] (φ : R →+* T) [IsLocalHom φ] (rs : List R),
      rs.length = n →
      Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R →
      RingTheory.Sequence.IsWeaklyRegular R rs →
      RingTheory.Sequence.IsWeaklyRegular T (rs.map φ) →
      φ.Flat := by
  classical
  induction n with
  | zero =>
    intro R T _ _ _ _ _ _ φ _ rs hlen hspan _ _
    -- `rs = []`, so `𝔪_R = ⊥` and `R` is a field; everything is flat over a field.
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hrs
    have hbot : IsLocalRing.maximalIdeal R = ⊥ := by
      rw [← hspan]; simp
    exact RingHom.Flat.of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot) φ
  | succ n ih =>
    intro R T _ _ _ _ _ _ φ _ rs hlen hspan hR hT
    obtain ⟨t, rs₀, rfl⟩ : ∃ t rs₀, rs = t :: rs₀ := by
      cases rs with
      | nil => simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    set I : Ideal R := Ideal.span {t} with hI
    set J : Ideal T := Ideal.span {φ t} with hJ
    have htm : t ∈ IsLocalRing.maximalIdeal R := by
      rw [← hspan]
      exact Ideal.subset_span (by simp)
    have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using htm
    have hJm : J ≤ IsLocalRing.maximalIdeal T := by
      rw [hJ, Ideal.span_le]
      have hnu : φ t ∈ IsLocalRing.maximalIdeal T :=
        (IsLocalRing.mem_maximalIdeal _).2 fun H =>
          ((IsLocalRing.mem_maximalIdeal _).1 htm) (isUnit_of_map_unit φ t H)
      simpa using hnu
    have hInt : I ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
    have hJnt : J ≠ ⊤ := fun h =>
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (h ▸ hJm))
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
    haveI : Nontrivial (T ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJnt
    haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalRing (T ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    -- the induced map on quotients
    have hIJ : I ≤ J.comap φ := by
      rw [hI, Ideal.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
    set ψ : R ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hIJ with hψdef
    have hψ : ψ.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp φ := by
      ext r; simp [hψdef, Ideal.quotientMap_mk]
    haveI : IsLocalHom ψ := by
      constructor
      intro a ha
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h1 : IsUnit ((Ideal.Quotient.mk J) (φ r)) := by
        rw [← RingHom.comp_apply, ← hψ, RingHom.comp_apply]; exact ha
      have h2 : IsUnit (φ r) :=
        IsLocalHom.map_nonunit (f := Ideal.Quotient.mk J) _ h1
      exact (IsLocalHom.map_nonunit (f := φ) r h2).map (Ideal.Quotient.mk I)
    -- split both regularity hypotheses at the head
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hR
    obtain ⟨hRt, hRtail⟩ := hR
    rw [List.map_cons, RingTheory.Sequence.isWeaklyRegular_cons_iff] at hT
    obtain ⟨hTt, hTtail⟩ := hT
    -- the identifications `A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`
    have heR : (R ⧸ I) ≃ₗ[R] QuotSMulTop t R :=
      Submodule.quotEquivOfEq _ _ (by
        rw [hI, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    have heT : (T ⧸ J) ≃ₗ[T] QuotSMulTop (φ t) T :=
      Submodule.quotEquivOfEq _ _ (by
        rw [hJ, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    -- transport the tails to the quotient rings
    have hRq : RingTheory.Sequence.IsWeaklyRegular (R ⧸ I)
        (rs₀.map (Ideal.Quotient.mk I)) := by
      rw [← Ideal.Quotient.algebraMap_eq I,
        RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) (R ⧸ I) rs₀]
      exact (heR.isWeaklyRegular_congr rs₀).2 hRtail
    have hTq : RingTheory.Sequence.IsWeaklyRegular (T ⧸ J)
        ((rs₀.map φ).map (Ideal.Quotient.mk J)) := by
      rw [← Ideal.Quotient.algebraMap_eq J,
        RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (T ⧸ J) (T ⧸ J) (rs₀.map φ)]
      exact (heT.isWeaklyRegular_congr (rs₀.map φ)).2 hTtail
    -- the two descriptions of the descended list agree
    have hlists : (rs₀.map (Ideal.Quotient.mk I)).map ψ
        = (rs₀.map φ).map (Ideal.Quotient.mk J) := by
      simp only [List.map_map]
      exact congrArg (fun f : R →+* T ⧸ J => rs₀.map f) hψ
    -- the span condition descends, because `t ↦ 0`
    have hspanq : Ideal.span {r | r ∈ rs₀.map (Ideal.Quotient.mk I)}
        = IsLocalRing.maximalIdeal (R ⧸ I) := by
      have h1 : (Ideal.span {r | r ∈ (t :: rs₀)}).map (Ideal.Quotient.mk I)
          = IsLocalRing.maximalIdeal (R ⧸ I) := by
        rw [hspan]
        exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
      rw [show (Ideal.span {r | r ∈ (t :: rs₀)}) = Ideal.ofList (t :: rs₀) from rfl,
        Ideal.map_ofList, List.map_cons] at h1
      have ht0 : (Ideal.Quotient.mk I) t = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
      rw [ht0, Ideal.ofList_cons, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at h1
      exact h1
    have hlenq : (rs₀.map (Ideal.Quotient.mk I)).length = n := by
      simp only [List.length_map]
      simpa using hlen
    have hTq' : RingTheory.Sequence.IsWeaklyRegular (T ⧸ J)
        ((rs₀.map (Ideal.Quotient.mk I)).map ψ) := by rw [hlists]; exact hTq
    have hflat : ψ.Flat :=
      ih (R ⧸ I) (T ⧸ J) ψ (rs₀.map (Ideal.Quotient.mk I)) hlenq hspanq hRq hTq'
    exact flat_of_flat_quotient_isSMulRegular φ htm hRt hTt ψ hψ hflat

/-- **THE LOCAL CRITERION OF FLATNESS** (**PROVEN 2026-07-27** over the ONE
atom `flat_of_flat_quotient_isSMulRegular` above — pure commutative algebra;
Matsumura *Commutative Ring Theory* 22.3, Stacks 00MK).

If `𝔪_R` is generated by an `R`-regular sequence `rs` — equivalently, `R` is
regular local with regular system of parameters `rs` — and the image of `rs` is
`T`-regular, then `T` is flat over `R`.

**THE CUT (2026-07-27).**  The previous version of this docstring predicted that
"the induction along `rs` is mechanical … so the whole content is the one-element
case", and named that case as "the statement to state and dispatch next if this
leaf is cut further.  That prediction was correct and has now been carried out:
the one-element case is
`flat_of_flat_quotient_isSMulRegular` above, the induction is
`flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux` above, and this declaration is
their composition.  **Nothing is open here any more — the open leaf is the atom.**

The induction really did need nothing beyond `isWeaklyRegular_cons_iff`,
`isWeaklyRegular_map_algebraMap_iff`, the identification
`A ⧸ (a) ≃ₗ[A] QuotSMulTop a A`, and the fact that quotients of noetherian local
rings are noetherian local.  The one thing worth recording that the prediction
did not mention: the base case is `𝔪_R = ⊥`, i.e. `R` a FIELD, and it discharges
by `RingHom.Flat.of_isField` **without using any hypothesis on `T` at all**.

**FAITHFULNESS — the separatedness hypothesis is present, disguised as
`[IsNoetherianRing T] [IsLocalRing T] [IsLocalHom φ]`, and it is LOAD-BEARING.**
The classical criterion needs `T` to be `𝔪_R`-adically *ideally separated*; the
statement is false for an arbitrary `R`-module with a regular sequence acting
regularly.  Here it is automatic and the derivation is short enough to record:
`φ` local gives `𝔪_R T ⊆ 𝔪_T`, hence `𝔪_R^n T ⊆ 𝔪_T^n`, so
`⋂ₙ 𝔪_R^n T ⊆ ⋂ₙ 𝔪_T^n = 0` by Krull's intersection theorem; and `T ⧸ I T` for
`I` finitely generated is again a noetherian local ring, so the same applies to
it.  **A prover who weakens `T` to a bare `R`-module produces a FALSE leaf.**
That hypothesis is carried, unweakened, into the atom. -/
theorem flat_of_isWeaklyRegular_span_eq_maximalIdeal {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing T] [IsNoetherianRing T]
    (φ : R →+* T) [IsLocalHom φ] (rs : List R)
    (hspan : Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R)
    (hR : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hT : RingTheory.Sequence.IsWeaklyRegular T (rs.map φ)) :
    φ.Flat :=
  flat_of_isWeaklyRegular_span_eq_maximalIdeal_aux rs.length R T φ rs rfl hspan hR hT

/-- **MIRACLE FLATNESS, RING LEVEL** (**PROVEN 2026-07-27** over the three
sub-leaves stated immediately above — PURE COMMUTATIVE ALGEBRA,
no schemes at all: Matsumura *Commutative Ring Theory* Theorem 23.1, in the
special case `M = T` of the source ring itself.  It would be at home in
mathlib, which has nothing of it.)

A local homomorphism `φ : R ⟶ T` of regular local rings whose fibre ring
`T ⧸ 𝔪_R T` is zero-dimensional and which does not change the Krull dimension
is FLAT.

**FAITHFULNESS.**  Matsumura 23.1 reads: *let `(A,𝔪) → (B,𝔫)` be a local
homomorphism of noetherian local rings and `M` a finite `B`-module with `A`
regular, `M` Cohen–Macaulay and `dim M = dim A + dim M/𝔪M`; then `M` is flat
over `A`.*  Instantiate `A = R`, `B = M = T`: `T` is a finite `T`-module, and
`T` regular makes it Cohen–Macaulay.  The dimension identity becomes
`hdim` together with `hfib`.  Note there is **no finiteness hypothesis
relating `R` and `T`** and there must not be — see the counterexample in the
docstring of `ringKrullDim_quotient_map_maximalIdeal_stalkMap` above, which is
exactly why this statement is the one that had to be cut here.

**WHAT MATHLIB HAS, AND ONE CLAIM OF THE OLD SURVEY THAT IS NOW REFUTED.**

* PRESENT: `IsRegularLocalRing` (`RingTheory/RegularLocalRing/Defs.lean`,
  defined by `(maximalIdeal R).spanFinrank = ringKrullDim R`), `ringKrullDim`,
  the regular-sequence theory in `RingTheory/Regular/RegularSequence.lean` —
  including the recursor `IsWeaklyRegular.ndrecWithRing`, which does induction
  along a regular sequence while quotienting the BASE RING as well — and the
  dimension-drop lemmas of `RingTheory/KrullDimension/Regular.lean`.
* **REFUTED (2026-07-27).**  Every earlier survey of this node, including the
  one that used to stand in this file, said that the induction step needs the
  **local criterion of flatness** in its `Tor₁` form and that mathlib has no
  `Tor` of modules, so the leaf was hopeless.  The second half is true —
  `grep -rn "^def Tor" Mathlib/` finds only `CategoryTheory.Monoidal.Tor` and
  the group-homology `Rep k G` version — but the first half is FALSE for
  MODULE-FINITE base changes.  `Module.free_quotSMulTop_iff_free`
  (`Mathlib/RingTheory/Regular/Free.lean`) states exactly the induction step:
  for `M` finitely presented over `R` and `x` in the Jacobson radical and
  `M`-regular, `M ⧸ xM` free over `R ⧸ (x)` **iff** `M` free over `R`.  Its
  proof is Nakayama plus a lifting argument, no `Tor` anywhere.  Refuting
  grep: `grep -n free_quotSMulTop_iff_free
  .lake/packages/mathlib/Mathlib/RingTheory/Regular/Free.lean`.
* So the honest statement of the obstruction is much narrower than "no local
  criterion": *with* module-finiteness the criterion is already in the pin,
  and the two remaining gaps are (a) **the fibre-dimension hypothesis has to be
  turned into a regular sequence**, i.e. "regular local ⟹ Cohen–Macaulay", or
  concretely "a system of parameters of a regular local ring is a regular
  sequence" — `grep -rl CohenMacaulay Mathlib/` is still empty and
  `RingTheory/Regular/Depth.lean` is a deprecation stub with ZERO declarations
  — and (b) the passage from the module-finite case to this one.

**THE "ROUTE THAT AVOIDS `Tor` ENTIRELY" DOES NOT APPLY TO *THIS* STATEMENT —
CORRECTED 2026-07-27, and this is the one thing in the survey above that would
have cost a prover a whole task.**  The route recorded here previously read:
"do not attack this leaf at the stalks; go back to an affine cover, where
finiteness survives", and then checked `Module.Flat A B` at the maximal ideals
of `A` (`Module.flat_of_isLocalized_maximal`), used
`Module.free_of_flat_of_isLocalRing` and inducted with
`Module.free_quotSMulTop_iff_free`.  Every step of that is correct — **for the
affine statement.**  It is not a route to the declaration below, because:

* **the declaration below has NO module-finiteness hypothesis**, deliberately
  (see the FAITHFULNESS paragraph above: Matsumura 23.1 with `M = T` needs
  none), and
* `Module.free_quotSMulTop_iff_free` requires `Module.FinitePresentation R M`,
  and `Module.free_of_flat_of_isLocalRing` requires `Module.Finite R P`.

So the affine route is a route to a DIFFERENT theorem — one about
`A → B` with `B` a finite `A`-module — and taking it here means silently adding
a hypothesis that the counterexample in
`ringKrullDim_quotient_map_maximalIdeal_stalkMap` shows is false at stalks.
Anyone who wants that route must first re-cut the CONSUMER
(`flat_of_finite_fibres_endo`) to descend to an affine cover before reaching the
stalks; that is a cut-level change to the glue, not work at this leaf.

**STATUS 2026-07-27 — DECOMPOSED into three sub-leaves, and this node is PROVEN
over them.**  Each is a standard named theorem, and each is stated in exactly
the generality the assembly needs:

1. `exists_isWeaklyRegular_span_eq_maximalIdeal` — a regular local ring has a
   regular system of parameters, and it is a regular sequence.  **This is the
   cheapest of the three and it is blocked only by DECLARATION ORDER**, exactly
   like `isRegularLocalRing_stalk_of_smooth` above: its two inputs,
   `isDomain_of_isRegularLocalRing` and `isRegularLocalRing_quotient_span_singleton`,
   are both PROVEN in `Fermat/FLT/Modularity/KhareWintenberger.lean` (lines 3071
   and 3109 as of this writing), which is strictly downstream of this module.
   **The hoist that closes `isRegularLocalRing_stalk_of_smooth` closes this one
   too** — that is a second reason to do it, and it was not previously recorded.
2. `isWeaklyRegular_map_of_ringKrullDim_eq` — "regular local ⟹
   Cohen–Macaulay", in the only form needed: a system of parameters of a regular
   local ring is a regular sequence.  This is gap (a) above and it is genuinely
   absent from mathlib, from `~/cs/FLT` and from this project.
3. `flat_of_isWeaklyRegular_span_eq_maximalIdeal` — the **local criterion of
   flatness**.  Genuinely absent, and see its own docstring for the single
   one-element lemma it reduces to.

The assembly is three lines and uses each sub-leaf exactly once. -/
theorem flat_of_isRegularLocalRing_of_ringKrullDim_eq {R T : Type u} [CommRing R] [CommRing T]
    [IsRegularLocalRing R] [IsRegularLocalRing T] (φ : R →+* T) [IsLocalHom φ]
    (hdim : ringKrullDim T = ringKrullDim R)
    (hfib : ringKrullDim (T ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) = 0) :
    φ.Flat := by
  obtain ⟨rs, hspan, hlen, hR⟩ := exists_isWeaklyRegular_span_eq_maximalIdeal R
  exact flat_of_isWeaklyRegular_span_eq_maximalIdeal φ rs hspan hR
    (isWeaklyRegular_map_of_ringKrullDim_eq φ rs hspan hlen hdim hfib)

/-- **MIRACLE FLATNESS, endomorphism form** (**PROVEN 2026-07-27** over the
four leaves stated immediately above — PURE COMMUTATIVE
ALGEBRA / general scheme theory, NO abelian varieties, no group law, no
`[n]`: Matsumura *Commutative Ring Theory* Theorem 23.1, the theorem
usually called *miracle flatness*; also in the Stacks Project under that
name, and in EGA IV §6.  Tag numbers deliberately not quoted — they were
not checked against the Stacks Project, and a wrong tag is worse than
none.)

*A proper endomorphism with finite fibres of a smooth proper
geometrically connected scheme over a field is FLAT.*

**Why this shape** (2026-07-27).  It is exactly the residue of
`flat_fiberMap_mulByNat` after the abelian-variety input has been isolated
into `finite_preimage_mulByNat_of_field` below.  Everything specific to
abelian varieties — the group law, the theorem of the cube, the degree
`n^{2g}` — is consumed by that leaf; what is left is a statement about an
arbitrary endomorphism of an arbitrary smooth proper connected variety,
which is where the classical "miracle flatness" theorem lives.  Whoever
proves this proves a general theorem, and it has no group scheme in it at
all — the same division of labour as `flat_of_flat_fiberMap` below.

**The classical proof, in the order the hypotheses are used.**

1. *`u` is FINITE.*  `IsProper u` supplies `LocallyOfFiniteType u`, and
   `hu` supplies finite fibres, so
   `LocallyQuasiFinite.of_finite_preimage_singleton` gives
   `LocallyQuasiFinite u`, and then Zariski's main theorem in mathlib's
   form, `IsFinite.of_isProper_of_locallyQuasiFinite`, gives `IsFinite u`.
   Both lemmas EXIST at this pin — `Morphisms/QuasiFinite.lean:296` and
   `ZariskisMainTheorem.lean:371`, located by name 2026-07-27 — but
   neither module is imported here, so a prover closing this leaf should
   add `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
   `Mathlib.AlgebraicGeometry.ZariskisMainTheorem` to the header.  That
   missing import is exactly why the hypothesis is phrased as `IsProper`
   plus finite fibres rather than as `[IsFinite u]`: in this form the
   statement needs no import this module does not already have, and the
   caller can discharge it from material that is free here.
2. *`X` is REGULAR and IRREDUCIBLE.*  `Smooth g` over a field gives
   geometric regularity, hence regularity, hence normality, hence local
   irreducibility; `GeometricallyConnected g` gives connectedness; and a
   connected, locally noetherian, locally irreducible scheme is
   irreducible.  Only ORDINARY connectedness is used, so a prover may
   weaken that hypothesis freely — `GeometricallyConnected` is merely what
   the caller has in hand (`AbelianSchemeStruct.connected`).
3. *`u` is SURJECTIVE.*  `IsProper g` makes `X` quasi-compact and of
   finite type over the field, hence finite-dimensional.  A finite
   morphism preserves dimension, so `u '' X` is a closed irreducible
   subset of `X` of the full dimension `dim X`, and in an irreducible
   finite-dimensional scheme of finite type over a field the only such
   subset is `X` itself.
4. *Miracle flatness, pointwise.*  Fix `x` and put `y = u x`.  Then
   `𝒪_{X,y} → 𝒪_{X,x}` is a local homomorphism of REGULAR local rings,
   module-finite because `u` is finite, whose fibre ring
   `𝒪_{X,x} / m_y 𝒪_{X,x}` is a localisation of a finite `κ(y)`-algebra
   and so has dimension `0`.  Since `u` is finite,
   `dim closure {x} = dim closure {u x}`, and on a finite-dimensional
   irreducible scheme of finite type over a field
   `dim 𝒪_{X,x} = dim X - dim closure {x}`; hence
   `dim 𝒪_{X,x} = dim 𝒪_{X,y} + dim (𝒪_{X,x} / m_y 𝒪_{X,x})`.  A regular
   local ring is Cohen–Macaulay, so Matsumura 23.1 applies and `𝒪_{X,x}`
   is flat over `𝒪_{X,y}`.  Conclude with
   `AlgebraicGeometry.Flat.iff_flat_stalkMap`
   (`Morphisms/Flat.lean:102`, located by name 2026-07-27).

**BOTH GLOBAL HYPOTHESES ARE LOAD-BEARING — an explicit counterexample.**
Drop connectedness and the statement is FALSE.  Take `X = 𝔸¹_K ⊔ Spec K`
and let `u` be the identity on `𝔸¹` and send the isolated point to the
origin of `𝔸¹`.  Every fibre is finite, yet on stalks `u` is
`𝒪_{𝔸¹,0} → K`, the quotient by the maximal ideal, which is not flat.
(This `X` is smooth over `K` but neither connected nor proper, so it is
excluded twice over — which is the point: neither hypothesis is
decorative.)

**WHAT IS PRESENT AND WHAT IS MISSING at this pin (checked 2026-07-27, not
inherited).**

* PRESENT: `ringKrullDim` (`RingTheory/KrullDimension/Basic.lean`),
  `Module.supportDim`, `topologicalKrullDim`, `Ideal.height`,
  `IsRegularLocalRing` (`RingTheory/RegularLocalRing/Defs.lean`), the
  regular-sequence theory in `RingTheory/Regular/RegularSequence.lean`,
  and the dimension-drop lemmas Stacks 00KW / 0B52 in
  `RingTheory/KrullDimension/Regular.lean` — which are the induction step
  of miracle flatness.  At scheme level, `Flat.iff_flat_stalkMap`,
  `Scheme.Hom.fiber`, and Zariski's main theorem.
* MISSING: **Cohen–Macaulay and depth**.  `grep -rl CohenMacaulay Mathlib/`
  returns nothing, and `RingTheory/Regular/Depth.lean` is 10 lines with
  ZERO declarations (both re-run 2026-07-27).  Also missing: the local
  criterion of flatness (the `Tor₁` statement), generic flatness, and
  openness of the flat locus —
  `grep -rln "genericFlat\|flatLocus" Mathlib/RingTheory/` is empty.
  `~/cs/FLT` has none of it either.

**To refute this survey**, re-run those three greps; a hit on any of them
means this note has gone stale and the leaf may be far cheaper than it
looks.  Note that a prover does NOT need the whole of CM theory: only
"regular local ⟹ Cohen–Macaulay" plus Matsumura 23.1 in the special case
where BOTH rings are regular, which is the classical dimension count and
does not need depth in its full generality.

**STATUS 2026-07-27 — DECOMPOSED, and the survey above is now out of date in
two places that matter.**  The four steps are separated into the four leaves
stated immediately above this docstring, and this node is proven over them:

* step 1 (`u` is FINITE) is **PROVEN HERE**, in the two `haveI` lines below,
  exactly as the survey predicted — `LocallyQuasiFinite.of_finite_preimage_singleton`
  followed by `IsFinite.of_isProper_of_locallyQuasiFinite`, with the two
  modules added to this file's header.  Nothing else in the chain has to
  re-derive it: all three geometric leaves take `[IsFinite u]`.
* steps 2 and 3 (regularity, irreducibility, surjectivity) and the dimension
  count of step 4 are `isRegularLocalRing_stalk_of_smooth` and
  `ringKrullDim_stalk_eq_of_isFinite_endo`;
* the finiteness of the fibres becomes
  `ringKrullDim_quotient_map_maximalIdeal_stalkMap`;
* and the local algebra is `flat_of_isRegularLocalRing_of_ringKrullDim_eq`.

**FIRST CORRECTION.**  The survey says regularity of the stalks has to be
proven.  It does not: it is ALREADY PROVEN in this repository, sorry-free, as
`GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
in `Modularity/KhareWintenberger.lean`, which is DOWNSTREAM of this module.
See the leaf's own docstring — the repair is a hoist, not a proof.

**SECOND CORRECTION.**  The survey says the local criterion of flatness (the
`Tor₁` statement) is missing and therefore blocking.  Missing, yes; blocking,
no — for MODULE-FINITE base changes `Module.free_quotSMulTop_iff_free`
(`Mathlib/RingTheory/Regular/Free.lean`) already IS the induction step, with no
`Tor` in its proof.  The one genuinely missing piece of commutative algebra
under this node is "a system of parameters of a regular local ring is a
regular sequence" (regular ⟹ Cohen–Macaulay).  The ring leaf's docstring
writes out the four-step route that consumes it.

**THIRD CORRECTION (2026-07-27, and it partly walks the second one back).**  The
`Module.free_quotSMulTop_iff_free` route is real, but it is a route to a
MODULE-FINITE statement, and `flat_of_isRegularLocalRing_of_ringKrullDim_eq`
carries no finiteness hypothesis and must not — the stalk map of a finite
morphism is not module-finite.  So that route cannot be executed *at that leaf*;
it could only be reached by re-cutting THIS glue to descend to an affine cover
before taking stalks.  The leaf's honest decomposition is the three sub-leaves
listed in its docstring, of which the local criterion of flatness is one.  Two
further facts landed the same day: the fibre-dimension leaf is now PROVEN (the
descent it wanted is mathlib's `Scheme.Hom.quasiFiniteAt`), and the hoist that
closes `isRegularLocalRing_stalk_of_smooth` also closes
`exists_isWeaklyRegular_span_eq_maximalIdeal`.

**Two routes considered and REJECTED for this leaf**, recorded so they are
not re-attempted: the *theorem of the cube* route needs ample line
bundles, absent as above; the *homogeneity/translation* route needs
openness of the flat locus AND generic flatness, both absent, and its
translation layer would have been free-floating since nothing could
consume it. -/
theorem flat_of_finite_fibres_endo {X : Scheme.{u}} {K : Type u} [Field K]
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [IsProper g] [GeometricallyConnected g]
    (u : X ⟶ X) [IsProper u] (hu : ∀ a : X, (⇑u ⁻¹' {a}).Finite) : Flat u := by
  -- Zariski's main theorem: proper with finite fibres ⟹ FINITE.
  haveI : LocallyQuasiFinite u := LocallyQuasiFinite.of_finite_preimage_singleton u hu
  haveI : IsFinite u := IsFinite.of_isProper_of_locallyQuasiFinite u
  -- Flatness of a morphism is flatness of every stalk map.
  refine AlgebraicGeometry.Flat.of_stalkMap u fun x => ?_
  -- Both stalks are regular local, `X` being smooth over a field.
  haveI := isRegularLocalRing_stalk_of_smooth g x
  haveI := isRegularLocalRing_stalk_of_smooth g (u x)
  -- Matsumura 23.1, with the two dimension inputs supplied by the geometry.
  exact flat_of_isRegularLocalRing_of_ringKrullDim_eq (u.stalkMap x).hom
    (ringKrullDim_stalk_eq_of_isFinite_endo g u x)
    (ringKrullDim_quotient_map_maximalIdeal_stalkMap u x)

/-- **The fibrewise criterion of flatness** (PROVEN 2026-07-27 over the
pointwise statement `flat_stalkMap_of_flat_stalkMap_fiberMapOver` above,
itself PROVEN the same day over the three leaves
`flat_of_flat_of_flat_quotientMap` (Stacks 05UV, ring level),
`essFinitePresentation_stalkMap` and
`flat_quotientMap_of_flat_stalkMap_fiberMapOver`
— general scheme theory, NO abelian varieties: EGA IV 11.3.10, *critère
de platitude par fibres*; Stacks 039E; Matsumura *Commutative Ring
Theory* §23 for the local-algebra form).
Let `u : X ⟶ Y` be a morphism over a base `S`, with both `X` and `Y`
flat and locally of finite presentation over `S`.  If the induced map on
the fibre over every point of `S` is flat, then `u` is flat.

**This is the exact statement being asked for.**  The full criterion is
an "iff at a point": with `Y` flat over `S` at `y = u x`, `u` is flat at
`x` **iff** `X` is flat over `S` at `x` and `u_s` is flat at `x`.  Only
the `⟸` direction, globalized over all points, is stated here — a
strictly weaker statement, so it cannot be false, and it is the whole of
what the abelian-scheme application needs.

**Why it is a separate leaf.**  It is the step that moves the problem
from an arbitrary base to a field, and it has no group-scheme content
whatsoever.  Whoever proves it proves a general theorem, and the
abelian-variety work in `flat_fiberMap_mulByNat` then happens over
`κ(s)`, where a smooth scheme really is regular.

**HOW IT IS PROVEN, and why the cut is where it is.**  Flatness of a
morphism is flatness of every stalk map
(`AlgebraicGeometry.Flat.of_stalkMap`), so the global statement follows
from the statement AT A POINT.  At `x : X` the fibre hypothesis is
consumed at exactly ONE fibre, `p.fiber (p x)`, and at exactly one point
of it, `Scheme.Hom.asFiber p x` — flatness of that fibre morphism gives
flatness of its stalk map there (`AlgebraicGeometry.Flat.stalkMap`).
Nothing is lost: Stacks 039C, the theorem the literature actually proves,
IS pointwise, and 039E is its global specialization.  The pointwise
statement is in turn PROVEN, so the remaining mathematics is now in its
three leaves: `flat_of_flat_of_flat_quotientMap` carries the Tor /
local-criterion / spreading-out survey (that is where the depth is),
`essFinitePresentation_stalkMap` is the finite-presentation analogue of a
lemma mathlib already has for finite type, and
`flat_quotientMap_of_flat_stalkMap_fiberMapOver` carries the
stalk-of-pullback survey.  Each docstring carries its own refuting greps.

**Checked against the source 2026-07-27: Stacks 039E does NOT require `Y`
flat over `S`** — its hypotheses are `X` locally of finite presentation
over `S`, `X` flat over `S`, `f_s` flat for every `s`, and `Y` locally of
finite **type** over `S`; flatness of `Y` over `S` is part of the
*conclusion*.  So the `[Flat q]` and `[LocallyOfFinitePresentation u]`
instances here are redundant, and the pointwise leaf drops them.  They
are harmless: extra hypotheses only weaken this statement, and the
consumer `flat_mulByNat` supplies them anyway.

**What the pin gives a prover, checked 2026-07-26** (this corrects the
survey that used to stand in `flat_mulByNat`'s docstring, which said
mathlib had "no notion of the dimension of a scheme" and that miracle
flatness had to be built from nothing — the RING-level half of that is
false):

* PRESENT.  `ringKrullDim` (`RingTheory/KrullDimension/Basic.lean`),
  `Module.supportDim` and `topologicalKrullDim`
  (`Topology/KrullDimension.lean`), `Ideal.height` / `Ideal.primeHeight`
  and `FiniteRingKrullDim` (`RingTheory/Ideal/Height.lean`), and — the
  induction step of miracle flatness itself — the dimension-drop lemmas
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  (Stacks 00KW) and `supportDim_le_supportDim_quotSMulTop_succ`
  (Stacks 0B52) in `RingTheory/KrullDimension/Regular.lean`.  Also
  `IsRegularLocalRing` / `IsRegularRing`
  (`RingTheory/RegularLocalRing/Defs.lean`), the regular-sequence theory
  `IsWeaklyRegular` / `IsRegular` (`RingTheory/Regular/RegularSequence.lean`,
  `RingTheory/Regular/Flat.lean`), `Module.free_of_flat_of_isLocalRing`
  (`RingTheory/LocalRing/Module.lean`), and, at scheme level,
  `Flat.iff_flat_stalkMap`, stability of `Flat` under base change and
  composition, and `Scheme.Hom.fiber` (`AlgebraicGeometry/Fiber.lean`).
* ABSENT.  **Cohen–Macaulay and depth** — `grep CohenMacaulay` over
  mathlib returns nothing at all, and `RingTheory/Regular/Depth.lean` is
  a 10-line stub with no declarations.  Also absent: the **local
  criterion of flatness** (the `Tor₁` statement), **generic flatness**,
  **openness of the flat locus**, and this criterion itself.  `~/cs/FLT`
  has none of it either (checked 2026-07-26: no `AbelianVariety`, no
  cube, no `CohenMacaulay`), so there is nothing to vendor.

To refute this survey, `grep -rn CohenMacaulay` and
`grep -rln "generic.*[Ff]lat\|flatLocus"` over `.lake/packages/mathlib`;
a hit on either means the note has gone stale. -/
theorem flat_of_flat_fiberMap {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (u : X ⟶ Y) (h : u ≫ q = p) [Flat p] [Flat q]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]
    [LocallyOfFinitePresentation u]
    (H : ∀ s : S, Flat (fiberMapOver u h s)) : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  haveI := H (p x)
  exact flat_stalkMap_of_flat_stalkMap_fiberMapOver u h x (Flat.stalkMap p x)
    (Flat.stalkMap (fiberMapOver u h (p x)) (p.asFiber x))

/-! **`flat_fiberMap_mulByNat` and `flat_mulByNat` used to stand here.**
They moved DOWN, below `finite_preimage_mulByNat` (2026-07-27), because
`flat_fiberMap_mulByNat` is now PROVEN over the theorem-of-the-cube leaf
`finite_preimage_mulByNat_of_field`, which is declared below this point.
Moving the two consumers down was preferred to hoisting that leaf up: the
leaf had a live owner at the time, and relocating a declaration out from
under the agent proving it is how this fleet manufactures merge
conflicts.  Nothing else changed, and `flat_mulByNat` is byte-identical
to its previous form.
-/

/-- **Finite point-fibres COMPOSE**: if every point-fibre of `g` and every
point-fibre of `h` is finite, then so is every point-fibre of `g ≫ h`.

Pure set theory over `Scheme.Hom.comp_apply`: `(g ≫ h) ⁻¹' {c}` is contained
in `⋃ b ∈ h ⁻¹' {c}, g ⁻¹' {b}`, a finite union of finite sets.  Stated for
arbitrary schemes because it is used to split `[n]` along a factorization
`n = p · c` (`mulByNat_mul`), which is what reduces the abelian-variety leaf
below to its two genuinely different cases. -/
theorem finite_preimage_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : ∀ b : Y, (⇑g ⁻¹' {b}).Finite) (hh : ∀ c : Z, (⇑h ⁻¹' {c}).Finite)
    (c : Z) : (⇑(g ≫ h) ⁻¹' {c}).Finite := by
  refine ((hh c).biUnion (fun b _ => hg b)).subset ?_
  intro x hx
  refine Set.mem_biUnion (show g x ∈ ⇑h ⁻¹' {c} from ?_) (show x ∈ ⇑g ⁻¹' {g x} from rfl)
  show h (g x) = c
  rw [← Scheme.Hom.comp_apply]
  exact hx

/-! ### `[n]` is UNRAMIFIED when `n` is prime to the characteristic

The declarations below carry the whole of
`finite_preimage_mulByNat_of_field_prime_to_char`, and since 2026-07-27
they are ALL PROVEN.  Most of them are general scheme theory or
bookkeeping with no abelian-variety content at all; the one piece of real
geometry, `nonempty_module_infKernel_of_squareZero` — the Lie algebra of
a smooth group scheme, in the form "the infinitesimal kernel is a
`K`-vector space" — was the last leaf of this section and is now closed
by the affine-local argument recorded in its docstring.

Note `eq_zero_of_nsmul_eq_zero_of_squareZero`, which was the leaf when
this section was written on 2026-07-27, was then proven over it: the
split moved the arithmetic into a proof and left the geometry as the
leaf, and the geometry has since been proven too. -/

namespace AbelianSchemeStruct

/-- **Precomposition of relative points is SUBTRACTIVE** (PROVEN 2026-07-27).

`RelPoint.pre` preserves `+` and `0` by the structure's own naturality
axioms `pre_add` and `pre_zero`; the inversion step is proven inline from
`neg_add` and cancellation.

**Why inline rather than by reusing `AbelianSchemeStruct.pre_neg`.**  That
lemma exists — `Fermat/FLT/ModularCurve/X0.lean:1352`, same namespace, same
statement — but in a SIBLING module which is not in this import cone (X0
imports `Modularity/AbelianScheme`, not this file).  Re-declaring
`Fermat.AbelianSchemeStruct.pre_neg` here would give two declarations of one
name and break any module that ever imports both, so the two lines are
duplicated instead of the name.  If the two modules are ever merged into one
cone, delete this `have` and use `ab.pre_neg`.

Used once, in `formallyUnramified_mulByNat`, to turn "two points agree
modulo a square-zero ideal" into "their difference lies in the kernel of the
restriction map". -/
theorem pre_sub (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') (x y : RelPoint f g) :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint.pre h hg (x - y) = RelPoint.pre h hg x - RelPoint.pre h hg y := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  have hneg : RelPoint.pre h hg (-y) = -(RelPoint.pre h hg y) := by
    refine eq_neg_of_add_eq_zero_left ?_
    show ab.add (RelPoint.pre h hg (ab.neg y)) (RelPoint.pre h hg y) = ab.zero g'
    rw [← ab.pre_add h hg]
    show RelPoint.pre h hg (ab.add (ab.neg y) y) = ab.zero g'
    rw [ab.neg_add]
    exact ab.pre_zero h hg
  simp only [sub_eq_add_neg]
  rw [← hneg]
  exact ab.pre_add h hg x (-y)

/-- **Precomposition of relative points, packaged as a GROUP HOMOMORPHISM**
(PROVEN 2026-07-27).

`RelPoint.pre h hg` is additive and unital by the two naturality axioms
`pre_add` and `pre_zero`, so it is an `AddMonoidHom` for the group
structures `ab.addCommGroup` on source and target.  Nothing new is proven
here; the point is to have a bundled map whose KERNEL is an
`AddSubgroup`, which is what `infKernel` below needs.

Used only through `infKernel`. -/
def preAddHom (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') :
    letI := ab.addCommGroup g
    letI := ab.addCommGroup g'
    RelPoint f g →+ RelPoint f g' :=
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  { toFun := RelPoint.pre h hg
    map_zero' := ab.pre_zero h hg
    map_add' := ab.pre_add h hg }

/-- **THE INFINITESIMAL KERNEL** — `ker (A(T) ⟶ A(T'))` for a change of
test object `h : T' ⟶ T`, as an additive subgroup of `RelPoint f g`.

For `h` a square-zero thickening `Spec R₀ ⟶ Spec R` this is the group
whose classical description is the *Lie algebra of `A` tensored with the
ideal* — see `nonempty_module_infKernel_of_squareZero` below, which is
the one place its structure beyond "subgroup" is asserted.

Membership is definitionally `RelPoint.pre h hg x = 0`, so
`AddMonoidHom.mem_ker` is not needed to enter or leave it. -/
def infKernel (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') :
    letI := ab.addCommGroup g
    AddSubgroup (RelPoint f g) :=
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  (ab.preAddHom h hg).ker

end AbelianSchemeStruct

/-- **Formally unramified + finite type ⟹ quasi-finite, at RING level**
(PROVEN 2026-07-27, and it is two lines).

**This REFUTES a survey that stood in this file.**  The docstring of
`finite_preimage_mulByNat_of_field_prime_to_char` recorded
`FormallyUnramified f → LocallyOfFiniteType f → LocallyQuasiFinite f` as
ABSENT from the pin, on the strength of
`grep -rn "Unramified" Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`
returning nothing.  That grep is correct and the conclusion drawn from it is
not: the implication holds at ring level as a mathlib INSTANCE,

    Mathlib/RingTheory/Unramified/LocalStructure.lean:333
    instance (priority := low) [EssFiniteType R S] [FormallyUnramified R S] :
      Algebra.QuasiFinite R S

(located by name 2026-07-27), with `Algebra.EssFiniteType.of_finiteType`
supplying `EssFiniteType` from `FiniteType`.  Only the *scheme-level*
packaging was missing, and that is `locallyQuasiFinite_of_formallyUnramified`
below.  **To refute THIS note in turn**, re-run
`grep -rn "EssFiniteType R S. .FormallyUnramified R S" Mathlib/RingTheory/Unramified/`;
an empty result means the instance has been removed or renamed.

The one non-obvious point is that `RingHom.QuasiFinite` is a `def`, not a
class, so `inferInstance` cannot close the goal directly — the `Algebra`-side
instance has to be produced with the ring types NAMED, which is exactly what
this wrapper does. -/
theorem quasiFinite_of_formallyUnramified_of_finiteType {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (h₁ : ψ.FormallyUnramified) (h₂ : ψ.FiniteType) : ψ.QuasiFinite := by
  algebraize [ψ]
  exact (inferInstance : Algebra.QuasiFinite R S)

/-- **Formally unramified + locally of finite type ⟹ locally quasi-finite**
(PROVEN 2026-07-27).  General scheme theory, no abelian varieties.

Both `FormallyUnramified` and `LocallyOfFiniteType` are
`HasRingHomProperty`s, and so is `LocallyQuasiFinite`; `iff_appLE` turns all
three into statements about the same affine-local maps `Γ(Y, U) ⟶ Γ(X, V)`,
where `quasiFinite_of_formallyUnramified_of_finiteType` applies pointwise.
No Zariski gluing is needed because the three characterisations quantify over
the *same* pairs of affine opens.

This is the piece of `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`
that is genuinely absent upstream, and it is a mathlib-facing lemma: it
mentions nothing from this development. -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (u : X ⟶ Y)
    [FormallyUnramified u] [LocallyOfFiniteType u] : LocallyQuasiFinite u := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite) (f := u)]
  intro U V e
  exact quasiFinite_of_formallyUnramified_of_finiteType _
    ((HasRingHomProperty.iff_appLE (P := @FormallyUnramified) (f := u)).mp ‹_› U V e)
    ((HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType) (f := u)).mp ‹_› U V e)

/-! ### The Lie algebra of a smooth group scheme, as a `K`-vector space

The declarations from here to `nonempty_module_infKernel_of_squareZero` are
the ingredients of that theorem's proof and nothing else.  The shape of the
argument is the one recorded in the theorem's docstring: over a field the base
`Spec K` is a single point, so every infinitesimal-kernel point has CONSTANT
image and they all factor through ONE affine open; the leaf then becomes a
statement about ring homomorphisms `Γ(X, U) ⟶ R`, and Milnor patching for
*schemes* is never needed — only the universal property of a fibre product of
RINGS, which is `sqZeroTriple` below. -/

/-- **Pulling a module structure back along an injective additive map.**

If `Δ : M →+ N` is injective into a `K`-module `N` and the image of `Δ` is
closed under the `K`-action — stated in the existential form
`∀ c m, ∃ m', Δ m' = c • Δ m`, which is all the geometric construction can
produce — then `M` carries a `K`-module structure.  All eight module axioms
are transported by `Function.Injective.module`. -/
theorem nonempty_module_of_injective_addMonoidHom {K M N : Type*} [Semiring K]
    [AddCommGroup M] [AddCommGroup N] [Module K N] (Δ : M →+ N)
    (hinj : Function.Injective Δ) (hs : ∀ (c : K) (m : M), ∃ m' : M, Δ m' = c • Δ m) :
    Nonempty (Module K M) := by
  choose σ hσ using hs
  letI : SMul K M := ⟨σ⟩
  exact ⟨Function.Injective.module K Δ hinj (fun c x => hσ c x)⟩

/-- The unbundled form of `nonempty_module_of_injective_addMonoidHom`: the
additivity of `Δ` is supplied as a hypothesis rather than by bundling. -/
theorem nonempty_module_of_injective_map {K M N : Type*} [Semiring K] [AddCommGroup M]
    [AddCommGroup N] [Module K N] (Δ : M → N) (hadd : ∀ m m', Δ (m + m') = Δ m + Δ m')
    (hinj : Function.Injective Δ)
    (hs : ∀ (c : K) (m : M), ∃ m' : M, Δ m' = c • Δ m) : Nonempty (Module K M) :=
  nonempty_module_of_injective_addMonoidHom (AddMonoidHom.mk' Δ hadd) hinj hs

section SqZeroTriple

variable {R R₀ B : Type u} [CommRing R] [CommRing R₀] [CommRing B]

/-- **The triple fibre product `R ×_{R₀} R ×_{R₀} R`**, as a subring of
`R × R × R`.  Its `Spec` is the test object on which the group-law crux of
`nonempty_module_infKernel_of_squareZero` is carried out. -/
def sqZeroTriple (φ : R →+* R₀) : Subring (R × R × R) where
  carrier := {x | φ x.1 = φ x.2.1 ∧ φ x.1 = φ x.2.2}
  mul_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; rw [h1, h1'],
      by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; rw [h2, h2']⟩
  one_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by simp only [Prod.fst_add, Prod.snd_add, map_add]; rw [h1, h1'],
      by simp only [Prod.fst_add, Prod.snd_add, map_add]; rw [h2, h2']⟩
  zero_mem' := ⟨rfl, rfl⟩
  neg_mem' := by
    rintro ⟨a, b, c⟩ ⟨h1, h2⟩
    exact ⟨by simp only [Prod.fst_neg, Prod.snd_neg, map_neg]; rw [h1],
      by simp only [Prod.fst_neg, Prod.snd_neg, map_neg]; rw [h2]⟩

namespace sqZeroTriple

variable (φ : R →+* R₀)

/-- First projection of the triple fibre product. -/
def pr₁ : ↥(sqZeroTriple φ) →+* R where
  toFun x := x.1.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Second projection of the triple fibre product. -/
def pr₂ : ↥(sqZeroTriple φ) →+* R where
  toFun x := x.1.2.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Third projection of the triple fibre product. -/
def pr₃ : ↥(sqZeroTriple φ) →+* R where
  toFun x := x.1.2.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **`σ(a, b, c) = b + c − a`, and it IS a ring homomorphism** when the kernel
of `φ` squares to zero.

This is the whole reason the group-law crux needs no differentials and no
Taylor expansion.  Multiplicativity reduces to `(b − a)(b' − a') = 0`, which
holds because both factors lie in `ker φ`. -/
def sigma (hsq : ∀ a b : R, a ∈ RingHom.ker φ → b ∈ RingHom.ker φ → a * b = 0) :
    ↥(sqZeroTriple φ) →+* R where
  toFun x := x.1.2.1 + x.1.2.2 - x.1.1
  map_one' := by show (1 : R) + 1 - 1 = 1; ring
  map_zero' := by show (0 : R) + 0 - 0 = 0; ring
  map_add' _ _ := by
    show _ + _ - _ = (_ + _ - _) + (_ + _ - _)
    simp only [Prod.fst_add, Prod.snd_add, Subring.coe_add]
    ring
  map_mul' x y := by
    have hx1 : x.1.2.1 - x.1.1 ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, ← x.2.1, sub_self]
    have hx2 : x.1.2.2 - x.1.1 ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, ← x.2.2, sub_self]
    have hy1 : y.1.2.1 - y.1.1 ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, ← y.2.1, sub_self]
    have hy2 : y.1.2.2 - y.1.1 ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, ← y.2.2, sub_self]
    have e12 := hsq _ _ hx1 hy2
    have e21 := hsq _ _ hx2 hy1
    show _ + _ - _ = (_ + _ - _) * (_ + _ - _)
    simp only [Prod.fst_mul, Prod.snd_mul, Subring.coe_mul]
    linear_combination -e12 - e21

/-- **The universal property of the triple fibre product**, in the only
direction the patching argument needs: three ring maps agreeing after `φ`
patch to one map into `R ×_{R₀} R ×_{R₀} R`. -/
def lift (f g h : B →+* R) (hg : ∀ b, φ (f b) = φ (g b)) (hh : ∀ b, φ (f b) = φ (h b)) :
    B →+* ↥(sqZeroTriple φ) where
  toFun b := ⟨(f b, g b, h b), hg b, hh b⟩
  map_one' := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

@[simp] theorem pr₁_lift (f g h : B →+* R) (hg hh) (b : B) :
    pr₁ φ (lift φ f g h hg hh b) = f b := rfl

@[simp] theorem pr₂_lift (f g h : B →+* R) (hg hh) (b : B) :
    pr₂ φ (lift φ f g h hg hh b) = g b := rfl

@[simp] theorem pr₃_lift (f g h : B →+* R) (hg hh) (b : B) :
    pr₃ φ (lift φ f g h hg hh b) = h b := rfl

@[simp] theorem sigma_lift (hsq) (f g h : B →+* R) (hg hh) (b : B) :
    sigma φ hsq (lift φ f g h hg hh b) = g b + h b - f b := rfl

/-- **Patching is INJECTIVE on restrictions**: a map into the triple fibre
product is determined by its three coordinates. -/
theorem hom_ext {ψ ψ' : B →+* ↥(sqZeroTriple φ)}
    (h₁ : ∀ b, pr₁ φ (ψ b) = pr₁ φ (ψ' b)) (h₂ : ∀ b, pr₂ φ (ψ b) = pr₂ φ (ψ' b))
    (h₃ : ∀ b, pr₃ φ (ψ b) = pr₃ φ (ψ' b)) : ψ = ψ' := by
  refine RingHom.ext fun b => Subtype.ext ?_
  refine Prod.ext (h₁ b) (Prod.ext (h₂ b) (h₃ b))

end sqZeroTriple

end SqZeroTriple

namespace AbelianSchemeStruct

/-- **Membership in the infinitesimal kernel, spelled as an equation of
morphisms.**  Membership is definitionally `RelPoint.pre h hg x = 0`; this
unwinds it to `h ≫ x.1 = g' ≫ ab.zeroSection`, which is the form every step of
`nonempty_module_infKernel_of_squareZero` consumes. -/
theorem mem_infKernel_iff (ab : AbelianSchemeStruct f) {T' T : Scheme.{u}} (h : T' ⟶ T)
    {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g') (x : RelPoint f g) :
    letI := ab.addCommGroup g
    (x ∈ ab.infKernel h hg ↔ h ≫ x.1 = g' ≫ ab.zeroSection) := by
  letI := ab.addCommGroup g
  letI := ab.addCommGroup g'
  constructor
  · intro hx
    have hx' : RelPoint.pre h hg x = ab.zero g' := hx
    have h2 : h ≫ x.1 = (ab.zero g').1 := congrArg Subtype.val hx'
    rw [h2]
    exact ab.zero_val g'
  · intro hx
    show RelPoint.pre h hg x = ab.zero g'
    apply Subtype.ext
    rw [show (RelPoint.pre h hg x).1 = h ≫ x.1 from rfl, hx]
    exact (ab.zero_val g').symm

end AbelianSchemeStruct

/-- **`Spec` of a surjective ring map with square-zero kernel is SURJECTIVE on
points.**  `ker φ ^ 2 = ⊥` puts `ker φ` inside every prime, so the closed image
`V(ker φ)` of `Spec φ` is all of `Spec R`. -/
theorem surjective_specMap_of_sq_ker_eq_bot {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ).base := by
  have key : ∀ x : PrimeSpectrum R, x ∈ Set.range (PrimeSpectrum.comap φ.hom) := by
    intro x
    rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have h2 : a ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hker] at h2
    have h3 : a ^ 2 = 0 := by simpa using h2
    rw [h3]
    exact x.asIdeal.zero_mem
  intro p
  obtain ⟨p', hp'⟩ := key p
  exact ⟨p', hp'⟩

section InfKernelChart

variable {X : Scheme.{u}} {K : Type u} [Field K] {fK : X ⟶ Spec (CommRingCat.of K)}

/-- **The base map of an infinitesimal-kernel point is CONSTANT**, at the image
of the zero section.

This is the step that the bundled-`K` defect blocked and that the unbundled
binder makes free: `Spec (CommRingCat.of K)` is a ONE-POINT space, so the zero
section has a single point in its image, and `Spec ψ` being surjective forces
the whole of `⇑w.1` to that point. -/
theorem base_eq_zeroSection_of_infKernel (ab : AbelianSchemeStruct fK)
    {C C₀ : CommRingCat.{u}} (ψ : C ⟶ C₀)
    (hsurj : Function.Surjective (Spec.map ψ).base)
    {gC : Spec C ⟶ Spec (CommRingCat.of K)} (w : RelPoint fK gC)
    (hw : Spec.map ψ ≫ w.1 = (Spec.map ψ ≫ gC) ≫ ab.zeroSection)
    (p : ↥(Spec C)) :
    w.1.base p = ab.zeroSection.base default := by
  obtain ⟨p', hp'⟩ := hsurj p
  have h1 : w.1.base ((Spec.map ψ).base p') =
      ((Spec.map ψ ≫ gC) ≫ ab.zeroSection).base p' := by
    rw [← hw]; rfl
  rw [← hp', h1]
  show ab.zeroSection.base ((Spec.map ψ ≫ gC).base p') = _
  congr 1
  exact Subsingleton.elim _ _

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- **The affine chart morphism attached to an affine open**, `Spec Γ(X, U) ⟶ X`.
Composing with it is how a ring homomorphism `Γ(X, U) ⟶ C` becomes a morphism
`Spec C ⟶ X`. -/
noncomputable def affineOpenChart : Spec Γ(X, U) ⟶ X := hU.isoSpec.inv ≫ U.ι

theorem affineOpenChart_mono : Mono (affineOpenChart hU) := by
  rw [affineOpenChart]; infer_instance

/-- **Ring homomorphisms inject into morphisms through the chart.**  This is the
`Δ`-injectivity of `nonempty_module_infKernel_of_squareZero`, and it is also
what makes patching injective on restrictions. -/
theorem affineOpenChart_injective (C : CommRingCat.{u}) :
    Function.Injective (fun θ : Γ(X, U) ⟶ C => Spec.map θ ≫ affineOpenChart hU) := by
  intro θ θ' h
  have := affineOpenChart_mono hU
  exact Spec.map_injective ((cancel_mono (affineOpenChart hU)).mp h)

/-- **Every morphism from an affine scheme whose image lies in `U` factors
through the chart.**  This is `IsOpenImmersion.lift` followed by
`IsAffineOpen.isoSpec`. -/
theorem exists_affineOpenChart_factor {C : CommRingCat.{u}} (w : Spec C ⟶ X)
    (hw : Set.range w.base ⊆ (U : Set X)) :
    ∃ θ : Γ(X, U) ⟶ C, Spec.map θ ≫ affineOpenChart hU = w := by
  have hrange : Set.range w.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hw
  refine ⟨Spec.preimage (IsOpenImmersion.lift U.ι w hrange ≫ hU.isoSpec.hom), ?_⟩
  rw [affineOpenChart, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]
  exact IsOpenImmersion.lift_fac U.ι w hrange

end InfKernelChart

/-- **THE LIE ALGEBRA OF A SMOOTH GROUP SCHEME** — *the infinitesimal kernel of
an abelian scheme is a `K`-VECTOR SPACE* (**PROVEN 2026-07-27**; created the
same day as `eq_zero_of_nsmul_eq_zero_of_squareZero`, restated in this
module-theoretic form, and closed here).

`Spec R₀ ⟶ Spec R` is a square-zero thickening (`φ` surjective,
`ker φ ^ 2 = ⊥`), and `ab.infKernel (Spec.map φ) rfl` is the subgroup of
`R`-points of `A` over `q` that restrict to the identity element on `Spec R₀`.
That abelian group carries a `K`-module structure — necessarily compatible with
its own addition, since `Module K ↥(…)` is stated over the subgroup's own
`AddCommGroup`.

Consumed by `eq_zero_of_nsmul_eq_zero_of_squareZero` below, which is the
`d[n] = n · id` statement and closes the prime-to-characteristic half of
`finite_preimage_mulByNat_of_field`.  It says nothing about the other half: at
`n = p = ringChar K` the scalar `(n : K)` is zero and the argument gives no
information, which is why `finite_preimage_mulByNat_of_field_char` really does
need the theorem of the cube.

## How it is proven

Everything from `nonempty_module_of_injective_addMonoidHom` down to
`exists_affineOpenChart_factor` above exists for this proof and nothing else.

1. *Affine-local reduction.*  `Spec (CommRingCat.of K)` is a ONE-POINT space, so
   the zero section `ab.zeroSection` has a single point `x₀` in its image.  Every
   kernel point `d` satisfies `Spec.map φ ≫ d.1 = (Spec.map φ ≫ q) ≫ zeroSection`
   (`mem_infKernel_iff`), and `Spec.map φ` is SURJECTIVE on points because
   `ker φ ^ 2 = ⊥` puts `ker φ` inside every prime
   (`surjective_specMap_of_sq_ker_eq_bot`).  Hence `⇑d.1` is constant at `x₀` for
   *every* `d` at once (`base_eq_zeroSection_of_infKernel`), so all kernel points
   factor through one affine open `U ∋ x₀` (`exists_affineOpenChart_factor`), and
   with `B := Γ(X, U)` the whole leaf becomes a statement about ring
   homomorphisms `θ d : B ⟶ R`.  **Milnor patching for SCHEMES is never needed.**
2. *The coordinate map.*  `Δ d := θ d − θ 0` takes values in `ker φ`, and
   `affineOpenChart_injective` makes it INJECTIVE.
3. *Additivity of `Δ` — the group-law crux, and it uses no differentials, no
   Taylor expansion and no morphism `m`.*  Put `J := R ×_{R₀} R ×_{R₀} R`
   (`sqZeroTriple`); `σ(a, b, c) = b + c − a` is a ring homomorphism `J ⟶ R`
   because `ker φ ^ 2 = ⊥` (`sqZeroTriple.sigma`).  Patch the points
   `P(0, x, 0)` and `P(0, 0, y)` over `Spec J`; their sum restricts to
   `(0, x, y)` along the three projections by `ab.pre_add` alone, and it lies in
   the infinitesimal kernel over `Spec J` (whose thickening `J ⟶ R₀` again has
   square-zero kernel), so it too factors through the chart and is therefore
   DETERMINED by those three restrictions (`sqZeroTriple.hom_ext`).  Applying
   `σ` and `ab.pre_add` once more gives `Δ(x + y) = Δ x + Δ y`.
4. *Scaling.*  For `c : K` the map `b ↦ θ 0 b + q♯(c) · Δ d b` is a ring
   homomorphism (again by `ker φ ^ 2 = ⊥`), lands over `q`, lies in the kernel,
   and has `Δ` equal to `c • Δ d`.
5. *Transport.*  `nonempty_module_of_injective_map` pulls the `K`-module
   structure of `B → R` back along `Δ`; all eight axioms come from
   `Function.Injective.module`.

## RECORD: the bundled-`K` instance defect that made this leaf FALSE

**REPAIRED 2026-07-27; this section is a record, not a warning.**  The binder
used to be `(K : CommRingCat.{u}) [Field K]` with base `Spec K`, and then the
conclusion's scalars came from the `[Field ↑K]` BINDER while `Spec K` and all
the geometry used `K`'s own `CommRing` structure.  Nothing forced the two to
agree.  Taking `↑K = 𝔽_p[t]` with a `[Field ↑K]` instance transported from `ℚ`
along a bijection of underlying sets, and `X = E₀ ×_{𝔽_p} 𝔽_p[t]`,
`R = 𝔽_p[t][ε]/(ε²)`, gave `ab.infKernel (Spec.map φ) rfl ≅ 𝔽_p[t] ≠ 0`, killed
by `p`, while the conclusion demanded a `ℚ`-vector space — torsion free.  FALSE.
The same counterexample refuted the consumer.

The repair was to take the base field UNBUNDLED, as in the present statement,
and it was threaded through the whole `_of_field` family in one commit.

**Keep it that way: a new declaration in this family must use the unbundled
shape.**  A file mixing the two conventions is worse than one with the bug
throughout, since instance search for `CommRing ↥K` is then ambiguous at every
boundary between the styles.  The one-line test for the defect class: under a
bundled `K` with `[Field K]`, `Subsingleton ↥(Spec K)` and `Unique ↥(Spec K)`
FAIL to synthesise while `Nonempty` succeeds; all three succeed for
`Spec (CommRingCat.of F)` with `F` unbundled.  A pin written
`CommRingCat.of ↑K = K` is VACUOUS — it is `rfl`.  Step 1 of the proof above is
exactly what the bundled binder blocked.

## A GENERALISATION THAT IS ALSO TRUE

The kernel is a module over `R₀` itself (restrict along `K ⟶ R₀` to recover the
statement below), over an arbitrary base, and without `ab.smooth` — the
classical isomorphism `ker(G(R) ⟶ G(R₀)) ≅ Hom_{R₀}(e^* Ω_{G/S} ⊗ R₀, ker φ)`
(SGA 3 Exp. II; Mumford *Abelian Varieties* §11; Milne *Abelian Varieties* I.7)
is valid for every group scheme.  It is stated over a field here because that is
exactly what the consumer needs and it is the weakest form that suffices.  Note
the proof below never constructs `Ω`: it works directly with the ring
homomorphisms `θ d`, which is why nothing about Kähler differentials for group
schemes — genuinely absent from this pin — was required. -/
theorem nonempty_module_infKernel_of_squareZero {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    {q : Spec R ⟶ Spec (CommRingCat.of K)} :
    letI := ab.addCommGroup q
    Nonempty (Module K (ab.infKernel (Spec.map φ)
      (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))) := by
  letI := ab.addCommGroup q
  set D := ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q) with hD
  -- the unit section and the point it hits
  obtain ⟨U, hU, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := ab.zeroSection.base default)
    (U := ⊤) (by trivial)
  have hsurj : Function.Surjective (Spec.map φ).base := surjective_specMap_of_sq_ker_eq_bot φ hφ hker
  -- every kernel point factors through the chart
  have hfac : ∀ d : ↥D, ∃ θ : Γ(X, U) ⟶ R, Spec.map θ ≫ affineOpenChart hU = d.1.1 := by
    intro d
    refine exists_affineOpenChart_factor hU _ ?_
    rintro _ ⟨p, rfl⟩
    rw [base_eq_zeroSection_of_infKernel ab φ hsurj d.1 ((ab.mem_infKernel_iff _ rfl d.1).mp d.2) p]
    exact hx₀
  choose θ hθ using hfac
  -- the reference ring homomorphisms
  obtain ⟨qR, hqR⟩ : ∃ r : CommRingCat.of K ⟶ R, Spec.map r = q :=
    ⟨Spec.preimage q, Spec.map_preimage q⟩
  obtain ⟨κ, hκ⟩ : ∃ r : CommRingCat.of K ⟶ Γ(X, U), Spec.map r = affineOpenChart hU ≫ fK :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra K ↥R := qR.hom.toAlgebra
  -- the difference function
  set t : ↥D → ↥Γ(X, U) → ↥R := fun d b => (θ d).hom b - (θ 0).hom b with ht
  -- all chart coordinates agree after `φ`
  have hφeq : ∀ d : ↥D, θ d ≫ φ = θ 0 ≫ φ := by
    intro d
    refine affineOpenChart_injective hU R₀ ?_
    show Spec.map (θ d ≫ φ) ≫ affineOpenChart hU = Spec.map (θ 0 ≫ φ) ≫ affineOpenChart hU
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hθ, hθ]
    rw [(ab.mem_infKernel_iff _ rfl d.1).mp d.2,
      (ab.mem_infKernel_iff _ rfl (0 : ↥D).1).mp (0 : ↥D).2]
  -- each `t d b` lies in the square-zero ideal
  have hker_mem : ∀ (d : ↥D) (b : ↥Γ(X, U)), t d b ∈ RingHom.ker φ.hom := by
    intro d b
    have := congrArg (fun (f : Γ(X, U) ⟶ R₀) => f.hom b) (hφeq d)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    show (θ d).hom b - (θ 0).hom b ∈ RingHom.ker φ.hom
    rw [RingHom.mem_ker, map_sub, this, sub_self]
  -- products of two such vanish
  have hsq : ∀ (a b : ↥R), a ∈ RingHom.ker φ.hom → b ∈ RingHom.ker φ.hom → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker φ.hom ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hker] at this
    simpa using this
  -- the Leibniz rule for `t`
  have hleib : ∀ (d : ↥D) (b b' : ↥Γ(X, U)),
      t d (b * b') = (θ 0).hom b * t d b' + t d b * (θ 0).hom b' := by
    intro d b b'
    have h0 : t d b * t d b' = 0 := hsq _ _ (hker_mem d b) (hker_mem d b')
    have e1 : (θ d).hom b = (θ 0).hom b + t d b := by simp [ht]
    have e2 : (θ d).hom b' = (θ 0).hom b' + t d b' := by simp [ht]
    show (θ d).hom (b * b') - (θ 0).hom (b * b') = _
    rw [map_mul, map_mul, e1, e2]
    linear_combination h0
  -- `t` is additive in `b`
  have hadd_b : ∀ (d : ↥D) (b b' : ↥Γ(X, U)), t d (b + b') = t d b + t d b' := by
    intro d b b'
    show (θ d).hom (b + b') - (θ 0).hom (b + b') = _
    rw [map_add, map_add]; ring
  have hone : ∀ d : ↥D, t d 1 = 0 := by
    intro d; show (θ d).hom 1 - (θ 0).hom 1 = 0; rw [map_one, map_one, sub_self]
  -- every chart coordinate restricts to the structure map on the base field
  have hκθ : ∀ d' : ↥D, κ ≫ θ d' = qR := by
    intro d'
    apply Spec.map_injective
    rw [Spec.map_comp, hκ, hqR, ← Category.assoc, hθ]
    exact d'.1.2
  -- `t d` vanishes on the base field
  have hbase : ∀ (d : ↥D) (k : K), t d (κ.hom k) = 0 := by
    intro d k
    have hd := congrArg (fun (f : CommRingCat.of K ⟶ R) => f.hom k) (hκθ d)
    have h0 := congrArg (fun (f : CommRingCat.of K ⟶ R) => f.hom k) (hκθ 0)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hd h0
    show (θ d).hom (κ.hom k) - (θ 0).hom (κ.hom k) = 0
    rw [hd, h0, sub_self]
  have hκθa : ∀ (a : ↥D) (k : K), (θ a).hom (κ.hom k) = qR.hom k := by
    intro a k
    have := congrArg (fun (f : CommRingCat.of K ⟶ R) => f.hom k) (hκθ a)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this
  -- THE CRUX: additivity of `t` in the point
  have hadd : ∀ d d' : ↥D, ∀ b, t (d + d') b = t d b + t d' b := by
    intro d d'
    -- the triple fibre product `R ×_{R₀} R ×_{R₀} R` and its structure maps
    set JC : CommRingCat.{u} := CommRingCat.of ↥(sqZeroTriple φ.hom) with hJC
    set p₁ : JC ⟶ R := CommRingCat.ofHom (sqZeroTriple.pr₁ φ.hom) with hp₁
    set p₂ : JC ⟶ R := CommRingCat.ofHom (sqZeroTriple.pr₂ φ.hom) with hp₂
    set p₃ : JC ⟶ R := CommRingCat.ofHom (sqZeroTriple.pr₃ φ.hom) with hp₃
    set sg : JC ⟶ R := CommRingCat.ofHom (sqZeroTriple.sigma φ.hom hsq) with hsg
    have hagree : ∀ (a : ↥D) (b : ↥Γ(X, U)), φ.hom ((θ 0).hom b) = φ.hom ((θ a).hom b) := by
      intro a b
      have h := congrArg (fun (f : Γ(X, U) ⟶ R₀) => f.hom b) (hφeq a)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
      exact h.symm
    set mk : ↥D → ↥D → (Γ(X, U) ⟶ JC) := fun a c =>
      CommRingCat.ofHom (sqZeroTriple.lift φ.hom (θ 0).hom (θ a).hom (θ c).hom
        (hagree a) (hagree c)) with hmk
    have hmk₁ : ∀ a c : ↥D, mk a c ≫ p₁ = θ 0 :=
      fun a c => CommRingCat.hom_ext (RingHom.ext fun b => rfl)
    have hmk₂ : ∀ a c : ↥D, mk a c ≫ p₂ = θ a :=
      fun a c => CommRingCat.hom_ext (RingHom.ext fun b => rfl)
    have hmk₃ : ∀ a c : ↥D, mk a c ≫ p₃ = θ c :=
      fun a c => CommRingCat.hom_ext (RingHom.ext fun b => rfl)
    have hmkσ : ∀ (a c : ↥D) (b : ↥Γ(X, U)),
        (mk a c ≫ sg).hom b = (θ a).hom b + (θ c).hom b - (θ 0).hom b := fun a c b => rfl
    -- all patches share one base point on `Spec JC`
    have hκmk : ∀ a c : ↥D, κ ≫ mk a c = κ ≫ mk 0 0 := by
      intro a c
      apply CommRingCat.hom_ext
      refine sqZeroTriple.hom_ext φ.hom (fun k => rfl) (fun k => ?_) (fun k => ?_)
      · show (θ a).hom (κ.hom k) = (θ 0).hom (κ.hom k)
        rw [hκθa a k, hκθa 0 k]
      · show (θ c).hom (κ.hom k) = (θ 0).hom (κ.hom k)
        rw [hκθa c k, hκθa 0 k]
    set qJ : Spec JC ⟶ Spec (CommRingCat.of K) := Spec.map (κ ≫ mk 0 0) with hqJ
    letI := ab.addCommGroup qJ
    -- the restriction maps to `Spec R`
    have hres : ∀ ρ : JC ⟶ R, mk 0 0 ≫ ρ = θ 0 → Spec.map ρ ≫ qJ = q := by
      intro ρ hρ
      rw [hqJ, ← Spec.map_comp, Category.assoc, hρ, hκθ 0, hqR]
    have hsg00 : mk 0 0 ≫ sg = θ 0 :=
      CommRingCat.hom_ext (RingHom.ext fun b => by rw [hmkσ]; ring)
    have h₁ : Spec.map p₁ ≫ qJ = q := hres p₁ (hmk₁ 0 0)
    have h₂ : Spec.map p₂ ≫ qJ = q := hres p₂ (hmk₂ 0 0)
    have h₃ : Spec.map p₃ ≫ qJ = q := hres p₃ (hmk₃ 0 0)
    have hσ : Spec.map sg ≫ qJ = q := hres sg hsg00
    -- the patch points
    have hPt : ∀ a c : ↥D, (Spec.map (mk a c) ≫ affineOpenChart hU) ≫ fK = qJ := by
      intro a c
      rw [Category.assoc, ← hκ, ← Spec.map_comp, hκmk a c, hqJ]
    set Pt : ↥D → ↥D → RelPoint fK qJ := fun a c => ⟨Spec.map (mk a c) ≫ affineOpenChart hU, hPt a c⟩
      with hPtdef
    -- restriction of a patch point along a structure map
    have key : ∀ (a c : ↥D) (ρ : JC ⟶ R) (f : Γ(X, U) ⟶ R) (_ : mk a c ≫ ρ = f)
        (hf : (Spec.map f ≫ affineOpenChart hU) ≫ fK = q) (hs : Spec.map ρ ≫ qJ = q),
        RelPoint.pre (Spec.map ρ) hs (Pt a c) = ⟨Spec.map f ≫ affineOpenChart hU, hf⟩ := by
      intro a c ρ f hρ hf hs
      apply Subtype.ext
      show Spec.map ρ ≫ Spec.map (mk a c) ≫ affineOpenChart hU = Spec.map f ≫ affineOpenChart hU
      rw [← Category.assoc, ← Spec.map_comp, hρ]
    have hval : ∀ a : ↥D, (Spec.map (θ a) ≫ affineOpenChart hU) ≫ fK = q := by
      intro a; rw [hθ a]; exact a.1.2
    have hDpt : ∀ a : ↥D, (⟨Spec.map (θ a) ≫ affineOpenChart hU, hval a⟩ : RelPoint fK q) = a.1 :=
      fun a => Subtype.ext (hθ a)
    have hzeroval : Spec.map (θ 0) ≫ affineOpenChart hU = (ab.zero q).1 := hθ 0
    -- the three restrictions of the two patch points
    have hA₁ : RelPoint.pre (Spec.map p₁) h₁ (Pt d 0) = 0 := by
      rw [key d 0 p₁ (θ 0) (hmk₁ d 0) (hval 0) h₁]; exact Subtype.ext hzeroval
    have hA₂ : RelPoint.pre (Spec.map p₂) h₂ (Pt d 0) = d.1 := by
      rw [key d 0 p₂ (θ d) (hmk₂ d 0) (hval d) h₂]; exact hDpt d
    have hA₃ : RelPoint.pre (Spec.map p₃) h₃ (Pt d 0) = 0 := by
      rw [key d 0 p₃ (θ 0) (hmk₃ d 0) (hval 0) h₃]; exact Subtype.ext hzeroval
    have hB₁ : RelPoint.pre (Spec.map p₁) h₁ (Pt 0 d') = 0 := by
      rw [key 0 d' p₁ (θ 0) (hmk₁ 0 d') (hval 0) h₁]; exact Subtype.ext hzeroval
    have hB₂ : RelPoint.pre (Spec.map p₂) h₂ (Pt 0 d') = 0 := by
      rw [key 0 d' p₂ (θ 0) (hmk₂ 0 d') (hval 0) h₂]; exact Subtype.ext hzeroval
    have hB₃ : RelPoint.pre (Spec.map p₃) h₃ (Pt 0 d') = d'.1 := by
      rw [key 0 d' p₃ (θ d') (hmk₃ 0 d') (hval d') h₃]; exact hDpt d'
    -- naturality of the group law along each structure map
    have hsum : ∀ (ρ : JC ⟶ R) (hs : Spec.map ρ ≫ qJ = q),
        RelPoint.pre (Spec.map ρ) hs (Pt d 0 + Pt 0 d') =
          RelPoint.pre (Spec.map ρ) hs (Pt d 0) + RelPoint.pre (Spec.map ρ) hs (Pt 0 d') :=
      fun ρ hs => ab.pre_add (Spec.map ρ) hs _ _
    -- `Spec (p₁ ≫ φ)` is surjective, so the sum has constant image too
    have hδsurj : Function.Surjective (Spec.map (p₁ ≫ φ)).base := by
      refine surjective_specMap_of_sq_ker_eq_bot _ ?_ ?_
      · intro y
        obtain ⟨x, hx⟩ := hφ y
        exact ⟨⟨(x, x, x), rfl, rfl⟩, hx⟩
      · rw [eq_bot_iff, pow_two]
        refine Ideal.mul_le.mpr fun a ha b hb => ?_
        have ha1 : (a : ↥R × ↥R × ↥R).1 ∈ RingHom.ker φ.hom := RingHom.mem_ker.mpr ha
        have hb1 : (b : ↥R × ↥R × ↥R).1 ∈ RingHom.ker φ.hom := RingHom.mem_ker.mpr hb
        have ha2 : (a : ↥R × ↥R × ↥R).2.1 ∈ RingHom.ker φ.hom := by
          rw [RingHom.mem_ker, ← a.2.1]; exact RingHom.mem_ker.mp ha1
        have ha3 : (a : ↥R × ↥R × ↥R).2.2 ∈ RingHom.ker φ.hom := by
          rw [RingHom.mem_ker, ← a.2.2]; exact RingHom.mem_ker.mp ha1
        have hb2 : (b : ↥R × ↥R × ↥R).2.1 ∈ RingHom.ker φ.hom := by
          rw [RingHom.mem_ker, ← b.2.1]; exact RingHom.mem_ker.mp hb1
        have hb3 : (b : ↥R × ↥R × ↥R).2.2 ∈ RingHom.ker φ.hom := by
          rw [RingHom.mem_ker, ← b.2.2]; exact RingHom.mem_ker.mp hb1
        refine Ideal.mem_bot.mpr (Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_)))
        · exact hsq _ _ ha1 hb1
        · exact hsq _ _ ha2 hb2
        · exact hsq _ _ ha3 hb3
    have hker0 : Spec.map p₁ ≫ (Pt d 0 + Pt 0 d').1 = q ≫ ab.zeroSection := by
      have hs := hsum p₁ h₁
      rw [hA₁, hB₁, add_zero] at hs
      have hv : Spec.map p₁ ≫ (Pt d 0 + Pt 0 d').1 = (ab.zero q).1 := congrArg Subtype.val hs
      rw [hv]; exact ab.zero_val q
    have hfacsum : ∃ ζ : Γ(X, U) ⟶ JC, Spec.map ζ ≫ affineOpenChart hU = (Pt d 0 + Pt 0 d').1 := by
      refine exists_affineOpenChart_factor hU _ ?_
      rintro _ ⟨p, rfl⟩
      have hcond : Spec.map (p₁ ≫ φ) ≫ (Pt d 0 + Pt 0 d').1
          = (Spec.map (p₁ ≫ φ) ≫ qJ) ≫ ab.zeroSection := by
        rw [Spec.map_comp, Category.assoc (Spec.map φ) (Spec.map p₁) qJ, h₁, Category.assoc,
          hker0, Category.assoc]
      rw [base_eq_zeroSection_of_infKernel ab (p₁ ≫ φ) hδsurj (Pt d 0 + Pt 0 d') hcond p]
      exact hx₀
    obtain ⟨ζ, hζ⟩ := hfacsum
    -- identify the three coordinates of `ζ`
    have hcoord : ∀ (ρ : JC ⟶ R) (f : Γ(X, U) ⟶ R) (hs : Spec.map ρ ≫ qJ = q)
        (hf : (Spec.map f ≫ affineOpenChart hU) ≫ fK = q),
        RelPoint.pre (Spec.map ρ) hs (Pt d 0 + Pt 0 d') = ⟨Spec.map f ≫ affineOpenChart hU, hf⟩ →
        ζ ≫ ρ = f := by
      intro ρ f hs hf hEq
      refine affineOpenChart_injective hU R ?_
      show Spec.map (ζ ≫ ρ) ≫ affineOpenChart hU = Spec.map f ≫ affineOpenChart hU
      rw [Spec.map_comp, Category.assoc, hζ]
      exact congrArg Subtype.val hEq
    have hζ₁ : ζ ≫ p₁ = θ 0 := by
      refine hcoord p₁ (θ 0) h₁ (hval 0) ?_
      rw [hsum p₁ h₁, hA₁, hB₁, add_zero]
      exact (Subtype.ext hzeroval).symm
    have hζ₂ : ζ ≫ p₂ = θ d := by
      refine hcoord p₂ (θ d) h₂ (hval d) ?_
      rw [hsum p₂ h₂, hA₂, hB₂, add_zero]
      exact (hDpt d).symm
    have hζ₃ : ζ ≫ p₃ = θ d' := by
      refine hcoord p₃ (θ d') h₃ (hval d') ?_
      rw [hsum p₃ h₃, hA₃, hB₃, zero_add]
      exact (hDpt d').symm
    -- apply `σ` and read off additivity
    have hζσ : ∀ b : ↥Γ(X, U),
        (ζ ≫ sg).hom b = (θ d).hom b + (θ d').hom b - (θ 0).hom b := by
      intro b
      have e₁ := congrArg (fun (f : Γ(X, U) ⟶ R) => f.hom b) hζ₁
      have e₂ := congrArg (fun (f : Γ(X, U) ⟶ R) => f.hom b) hζ₂
      have e₃ := congrArg (fun (f : Γ(X, U) ⟶ R) => f.hom b) hζ₃
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e₁ e₂ e₃
      show (ζ.hom b).1.2.1 + (ζ.hom b).1.2.2 - (ζ.hom b).1.1 = _
      rw [← e₁, ← e₂, ← e₃]
      rfl
    have hsgA : mk d 0 ≫ sg = θ d :=
      CommRingCat.hom_ext (RingHom.ext fun b => by rw [hmkσ]; ring)
    have hsgB : mk 0 d' ≫ sg = θ d' :=
      CommRingCat.hom_ext (RingHom.ext fun b => by rw [hmkσ]; ring)
    have hσsum : (d + d').1 = RelPoint.pre (Spec.map sg) hσ (Pt d 0 + Pt 0 d') := by
      rw [hsum sg hσ, key d 0 sg (θ d) hsgA (hval d) hσ, key 0 d' sg (θ d') hsgB (hval d') hσ,
        hDpt d, hDpt d']
      rfl
    have hθsum : θ (d + d') = ζ ≫ sg := by
      refine affineOpenChart_injective hU R ?_
      show Spec.map (θ (d + d')) ≫ affineOpenChart hU = Spec.map (ζ ≫ sg) ≫ affineOpenChart hU
      rw [hθ (d + d'), Spec.map_comp, Category.assoc, hζ]
      exact congrArg Subtype.val hσsum
    intro b
    show (θ (d + d')).hom b - (θ 0).hom b = _
    rw [hθsum, hζσ b]
    show _ = ((θ d).hom b - (θ 0).hom b) + ((θ d').hom b - (θ 0).hom b)
    ring
  refine nonempty_module_of_injective_map (K := K) (fun d => t d) ?_ ?_ ?_
  · intro d d'; funext b; exact hadd d d' b
  · -- injectivity
    intro d d' h
    have hb : ∀ b, (θ d).hom b = (θ d').hom b := by
      intro b
      have := congrFun h b
      simpa [ht, sub_left_inj] using this
    have hcomp : θ d = θ d' := by
      apply CommRingCat.hom_ext
      exact RingHom.ext hb
    have : d.1.1 = d'.1.1 := by rw [← hθ d, ← hθ d', hcomp]
    exact Subtype.ext (Subtype.ext this)
  · -- closure under scaling
    intro c d
    have hzero : t d 0 = 0 := by
      show (θ d).hom 0 - (θ 0).hom 0 = 0
      rw [map_zero, map_zero, sub_self]
    -- the twisted ring homomorphism `θ₀ + c · t d`
    let μ : ↥Γ(X, U) →+* ↥R :=
      { toFun := fun b => (θ 0).hom b + qR.hom c * t d b
        map_one' := by rw [map_one, hone d]; ring
        map_mul' := fun b b' => by
          have h0 : t d b * t d b' = 0 := hsq _ _ (hker_mem d b) (hker_mem d b')
          show (θ 0).hom (b * b') + qR.hom c * t d (b * b') = _
          rw [map_mul, hleib d b b']
          linear_combination (-(qR.hom c ^ 2)) * h0
        map_zero' := by rw [map_zero, hzero]; ring
        map_add' := fun b b' => by
          show (θ 0).hom (b + b') + qR.hom c * t d (b + b') = _
          rw [map_add, hadd_b d b b']; ring }
    let μC : Γ(X, U) ⟶ R := CommRingCat.ofHom μ
    have hμval : ∀ b, μC.hom b = (θ 0).hom b + qR.hom c * t d b := fun _ => rfl
    -- it agrees with `θ 0` after `φ`
    have hμφ : μC ≫ φ = θ 0 ≫ φ := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun b => ?_
      show φ.hom (μC.hom b) = φ.hom ((θ 0).hom b)
      rw [hμval, map_add, map_mul, RingHom.mem_ker.mp (hker_mem d b), mul_zero, add_zero]
    -- it agrees with the structure map on the base field
    have hμκ : κ ≫ μC = qR := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun k => ?_
      show μC.hom (κ.hom k) = qR.hom k
      rw [hμval, hbase d k, mul_zero, add_zero]
      exact congrArg (fun (f : CommRingCat.of K ⟶ R) => f.hom k) (hκθ 0)
    -- the resulting relative point
    have hover : (Spec.map μC ≫ affineOpenChart hU) ≫ fK = q := by
      rw [Category.assoc, ← hκ, ← Spec.map_comp, hμκ, hqR]
    have hmem : (⟨Spec.map μC ≫ affineOpenChart hU, hover⟩ : RelPoint fK q) ∈ D := by
      rw [ab.mem_infKernel_iff _ rfl]
      show Spec.map φ ≫ Spec.map μC ≫ affineOpenChart hU = _
      rw [← Category.assoc, ← Spec.map_comp, hμφ, Spec.map_comp, Category.assoc, hθ]
      exact (ab.mem_infKernel_iff _ rfl (0 : ↥D).1).mp (0 : ↥D).2
    refine ⟨⟨⟨Spec.map μC ≫ affineOpenChart hU, hover⟩, hmem⟩, ?_⟩
    have hθμ : θ ⟨⟨Spec.map μC ≫ affineOpenChart hU, hover⟩, hmem⟩ = μC := by
      refine affineOpenChart_injective hU R ?_
      show Spec.map (θ ⟨⟨Spec.map μC ≫ affineOpenChart hU, hover⟩, hmem⟩) ≫ affineOpenChart hU = _
      rw [hθ]
    funext b
    show (θ _).hom b - (θ 0).hom b = _
    rw [hθμ, hμval]
    show (θ 0).hom b + qR.hom c * t d b - (θ 0).hom b = c • t d b
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    ring


/-- **THE INFINITESIMAL KERNEL IS TORSION FREE AT `n` PRIME TO THE
CHARACTERISTIC** (PROVEN 2026-07-27 over the single leaf
`nonempty_module_infKernel_of_squareZero` above; this used to BE the leaf).

`Spec R₀ ⟶ Spec R` is a square-zero thickening, `d` is an `R`-point of `A`
over the base point `q` restricting to the identity element on `Spec R₀`,
and `n · d = 0` with `(n : K) ≠ 0`.  Then `d = 0`.  This is exactly the
classical `d[n] = n · id` statement, and it is why the
prime-to-characteristic half of `finite_preimage_mulByNat_of_field` is
cheap while the characteristic half needs the theorem of the cube: at
`n = p = ringChar K` the scalar `(n : K)` is zero and the argument below
says nothing.

**The proof is pure module theory, and that is the point of the split.**
`d` lies in `ab.infKernel (Spec.map φ) rfl` by `hres` — definitionally, so
no `AddMonoidHom.mem_ker` step is needed.  On that subgroup the leaf
supplies a `K`-module structure whose addition IS the group's, so
`Nat.cast_smul_eq_nsmul` turns `hnd` into `(n : K) • ⟨d, _⟩ = 0`, and
multiplying by `(n : K)⁻¹` — available because `K` is a field and
`hn : (n : K) ≠ 0` — gives `⟨d, _⟩ = 0`.  `Subtype.val` then returns the
statement about `d`.

No geometry is used HERE; all of it is inside the leaf. -/
theorem eq_zero_of_nsmul_eq_zero_of_squareZero {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : (n : K) ≠ 0)
    {R R₀ : CommRingCat.{u}} (φ : R ⟶ R₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    {q : Spec R ⟶ Spec (CommRingCat.of K)} (d : RelPoint fK q)
    (hres : letI := ab.addCommGroup (Spec.map φ ≫ q)
      RelPoint.pre (Spec.map φ) rfl d = 0)
    (hnd : letI := ab.addCommGroup q; n • d = 0) :
    letI := ab.addCommGroup q; d = 0 := by
  letI := ab.addCommGroup q
  letI := ab.addCommGroup (Spec.map φ ≫ q)
  obtain ⟨inst⟩ := nonempty_module_infKernel_of_squareZero K ab φ hφ hker (q := q)
  letI := inst
  have hd : d ∈ ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q) := hres
  have hx : (n : K) • (⟨d, hd⟩ :
      ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact Subtype.ext hnd
  have hz : (⟨d, hd⟩ :
      ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) = 0 :=
    calc (⟨d, hd⟩ : ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))
        = ((n : K)⁻¹ * (n : K)) • (⟨d, hd⟩ :
            ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q)) := by
          rw [inv_mul_cancel₀ hn, one_smul]
      _ = (n : K)⁻¹ • ((n : K) • (⟨d, hd⟩ :
            ab.infKernel (Spec.map φ) (rfl : Spec.map φ ≫ q = Spec.map φ ≫ q))) := mul_smul _ _ _
      _ = 0 := by rw [hx, smul_zero]
  exact congrArg Subtype.val hz

/-- **`[n]` is FORMALLY UNRAMIFIED when `n` is prime to the characteristic**
(PROVEN 2026-07-27 over `eq_zero_of_nsmul_eq_zero_of_squareZero` above,
which is itself now proven over the single leaf
`nonempty_module_infKernel_of_squareZero`).

This is the functor-of-points argument in full, and it uses no geometry
beyond the group structure.  Mathlib's `FormallyUnramified.of_hom_ext`
reduces formal unramifiedness to: for every surjection `φ : R ⟶ R₀` with
`ker φ ^ 2 = ⊥` and every pair `g₁ g₂ : Spec R ⟶ A` with
`Spec.map φ ≫ g₁ = Spec.map φ ≫ g₂` and `g₁ ≫ [n] = g₂ ≫ [n]`, one has
`g₁ = g₂`.

The proof:

1. *Both are relative points over the SAME base point.*  `[n] ≫ f = f`
   (`mulByNat_comp`) turns `g₁ ≫ [n] = g₂ ≫ [n]` into `g₂ ≫ f = g₁ ≫ f`,
   so `g₁` and `g₂` are two elements of the group `RelPoint f (g₁ ≫ f)`.
2. *The hypotheses become group statements.*  `nsmul_val` says precomposition
   with `[n]` IS multiplication by `n`, so `g₁ ≫ [n] = g₂ ≫ [n]` reads
   `n • y₁ = n • y₂`, i.e. `n • (y₁ - y₂) = 0`; and `pre_sub` turns the
   agreement over `Spec R₀` into `RelPoint.pre _ _ (y₁ - y₂) = 0`.
3. *Apply the leaf* to `d = y₁ - y₂` and conclude `y₁ = y₂`, hence
   `g₁ = g₂`.

No line bundles, no `Pic`, no theorem of the cube, and no smoothness is used
HERE — smoothness is consumed inside the leaf. -/
theorem formallyUnramified_mulByNat {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : (n : K) ≠ 0) :
    FormallyUnramified (ab.mulByNat n) := by
  refine FormallyUnramified.of_hom_ext _ ?_
  intro R R₀ φ hφ hker g₁ g₂ hres hcomp
  have hq₂ : g₂ ≫ fK = g₁ ≫ fK := by
    conv_lhs => rw [← ab.mulByNat_comp n]
    rw [← Category.assoc, ← hcomp, Category.assoc, ab.mulByNat_comp]
  letI := ab.addCommGroup (g₁ ≫ fK)
  letI := ab.addCommGroup (Spec.map φ ≫ (g₁ ≫ fK))
  set y₁ : RelPoint fK (g₁ ≫ fK) := ⟨g₁, rfl⟩ with hy₁
  set y₂ : RelPoint fK (g₁ ≫ fK) := ⟨g₂, hq₂⟩ with hy₂
  have hsub : y₁ - y₂ = 0 := by
    refine eq_zero_of_nsmul_eq_zero_of_squareZero K ab n hn φ hφ hker _ ?_ ?_
    · rw [ab.pre_sub, sub_eq_zero]
      exact Subtype.ext hres
    · rw [smul_sub, sub_eq_zero]
      refine Subtype.ext ?_
      rw [ab.nsmul_val, ab.nsmul_val]
      exact hcomp
  exact congrArg Subtype.val (sub_eq_zero.mp hsub)

/-- **`[n]` has finite fibres when `n` is invertible in the base field**
(PROVEN 2026-07-27 over the single leaf
`nonempty_module_infKernel_of_squareZero`; this used to be a sorry leaf).

One half of the old `finite_preimage_mulByNat_of_field`, split out
2026-07-27.  Since `K` is a field, `(n : K) ≠ 0` says exactly that `n` is
prime to the characteristic.

**THE ROUTE, AND IT DOES NOT GO THROUGH THE THEOREM OF THE CUBE.**  `[n]`
is FORMALLY UNRAMIFIED, and formally unramified plus locally of finite type
is quasi-finite.  Unramifiedness is immediate from the functor of points,
with no line bundles anywhere: let `T ↪ T'` be a square-zero thickening and
`h₁ h₂ : T' ⟶ A` two lifts with `h₁ ≫ [n] = h₂ ≫ [n]` that agree on `T`.
By `nsmul_val` that says `n • h₁ = n • h₂` in the group `RelPoint f (T' ⟶ S)`,
i.e. `n • (h₁ - h₂) = 0`, and `h₁ - h₂` lies in the kernel of
`RelPoint f (T' ⟶ S) → RelPoint f (T ⟶ S)`.  For a SMOOTH group scheme that
kernel is a module over `Γ(T, 𝒪_T)`, which is a `K`-algebra; so `n` acts
invertibly on it as soon as `(n : K) ≠ 0`, forcing `h₁ = h₂`.  This is the
classical "`d[n] = n · id` on the Lie algebra", and it is exactly why the
prime-to-characteristic case is cheap while the characteristic case
(`finite_preimage_mulByNat_of_field_char`) is not: there `d[p] = 0`.

**What IS present at this pin** (each claim refutable by one grep).
`AlgebraicGeometry.FormallyUnramified`
(`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:54`),
`LocallyQuasiFinite` (`Morphisms/QuasiFinite.lean:71`) with
`locallyQuasiFinite_iff_finite_preimage_singleton`, and — for spreading
quasi-finiteness at the origin over all of `A` — `Scheme.Hom.quasiFiniteLocus`
and `Scheme.Hom.isOpen_quasiFiniteAt`
(`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:314`, `:290`), which say
the quasi-finite locus is OPEN.  Mathlib has also STARTED abelian varieties:
`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` exist and carry
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed` and
`smooth_of_grpObj`.  Re-check that directory at every pin bump.

**THE TWO OBLIGATIONS THIS DOCSTRING USED TO RECORD: one is now PROVEN, one
is now the single leaf.**  Neither was ever the cube.

1. The `Γ(T, 𝒪_T)`-module structure on the kernel above, i.e. the Lie algebra
   / tangent space of a smooth group scheme.  **Still missing, and it is now
   the leaf `nonempty_module_infKernel_of_squareZero` above**, where the
   argument, the references and the refuting greps are recorded.  Mathlib
   still has NO scheme tangent space: `grep -rni "tangentSpace\|DualNumber"
   Mathlib/AlgebraicGeometry/` returns NOTHING (re-run 2026-07-27).
2. `FormallyUnramified f → LocallyOfFiniteType f → LocallyQuasiFinite f`.
   **This was recorded as ABSENT and that was WRONG** — the grep it rested on
   (`grep -rn "Unramified" Morphisms/QuasiFinite.lean` → nothing) is true but
   does not support the conclusion, because the implication lives at RING
   level as the mathlib instance
   `[EssFiniteType R S] [FormallyUnramified R S] : Algebra.QuasiFinite R S`
   (`Mathlib/RingTheory/Unramified/LocalStructure.lean:333`).  It is now
   PROVEN here as `locallyQuasiFinite_of_formallyUnramified`, in four lines.

**The `quasiFiniteLocus` spreading tool is NOT needed** — and recording that
saves the next reader a detour.  `Scheme.Hom.quasiFiniteLocus` /
`isOpen_quasiFiniteAt` were suggested for propagating quasi-finiteness from
the origin over all of `A`, but the functor-of-points argument proves
`FormallyUnramified` at EVERY affine test scheme at once, so there is nothing
to spread.  (Openness of the quasi-finite locus would not have sufficed
anyway: spreading from one point needs homogeneity, i.e. translations, not
just an open locus.)

References: Mumford *Abelian Varieties* §6, §11; Milne *Abelian Varieties*
I.7; SGA 3, Exp. II. -/
theorem finite_preimage_mulByNat_of_field_prime_to_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (n : ℕ) (hn : (n : K) ≠ 0) (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI : LocallyOfFiniteType (ab.mulByNat n) := ab.locallyOfFiniteType_mulByNat n
  haveI : IsProper (ab.mulByNat n) := ab.isProper_mulByNat n
  haveI : QuasiCompact (ab.mulByNat n) := inferInstance
  haveI : FormallyUnramified (ab.mulByNat n) := formallyUnramified_mulByNat K ab n hn
  haveI : LocallyQuasiFinite (ab.mulByNat n) :=
    locallyQuasiFinite_of_formallyUnramified (ab.mulByNat n)
  exact (ab.mulByNat n).finite_preimage_singleton a

section ShearReduction

-- `_root_.` is not optional: a bare `open Limits` inside `namespace Fermat` would
-- bind to a nested `Fermat.Limits` if one is ever declared.  The file already
-- opens `Limits` this way in its two earlier sections.
open _root_.CategoryTheory.Limits

/-! ### The shearing reduction: ALL fibres of `[n]` from the ONE fibre `ker[n]`

(Added 2026-07-27, while proving `finite_preimage_mulByNat_of_field_char`.)

Everything in this block is PROVEN and **cube-free**, and it is stated for an
arbitrary base `S` — there is no field, no characteristic and no smoothness in
it.  It replaces the "all fibres of `[n]`" problem by the ONE statement the
literature actually proves, namely that `[n]` is an ISOGENY:

  `ker[n] ⟶ S` is a FINITE morphism.

The argument is the classical one, and it is worth recording because it is
*not* the theorem of the cube:

1. `finite_preimage_of_finite_preimage_pullback_fst` — pure scheme theory.
   For ANY `h : X ⟶ Y`, finite fibres of `pullback.fst h h` give finite fibres
   of `h`.  Reason: given `u, v` with `h u = h v`, `Scheme.Pullback.exists_preimage_pullback`
   produces a point of `X ×_Y X` over the pair `(u, v)` — the map from the
   carrier of a fibre product ONTO the set-theoretic fibre product is
   surjective, because `κ(u) ⊗_{κ(h u)} κ(v)` is a nonzero ring.  So
   `pullback.snd` maps the (finite) fibre of `pullback.fst` over `u` ONTO
   `h ⁻¹' {h u}`.

2. `kerShear` — the shearing morphism `A ×_{[n], A, [n]} A ⟶ A ×_S ker[n]`,
   `(u, v) ↦ (u, v - u)`, written directly on relative points: `v - u` is a
   relative point of `f` over `A ×_{[n]} A`, and `nsmul_val` turns
   `[n] ∘ v = [n] ∘ u` into `n • (v - u) = 0`, i.e. `v - u` factors through
   `ker[n]`.  `kerUnshear` is `(u, k) ↦ (u, u + k)` and
   `kerShear_unshear` says `kerShear ≫ kerUnshear = 𝟙`, so `kerShear` is
   injective on points — which is all that is needed.  Only ONE round trip is
   proven; the other is not required and is not claimed.

3. `pullback.fst f (ker[n] ⟶ S)` is the base change of `ker[n] ⟶ S`, hence
   finite when that is, hence has finite fibres.  Composing (2) and (1) gives
   `finite_preimage_mulByNat_of_isFinite_ker`.

`isFinite_ker_mulByNat_of_finite_preimage` is a convenience bridge in the other
direction: since `[n]` is proper (`isProper_mulByNat`) and locally of finite
type (`locallyOfFiniteType_mulByNat`), so is `ker[n] ⟶ S`, and Zariski's main
theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`) upgrades "every fibre of
`ker[n] ⟶ S` is a finite SET" to "`ker[n] ⟶ S` is a finite MORPHISM".  A prover
of the residual leaf therefore only ever has to exhibit a finite point set —
over a field, a single one.

**This block is `n`-generic and characteristic-blind.**  It applies verbatim to
the prime-to-characteristic sibling `finite_preimage_mulByNat_of_field_prime_to_char`
and to the arbitrary-base `finite_preimage_mulByNat`.  Those have their own
owners and are deliberately NOT touched here; this note is so the next owner
sees the shared route.
-/

/-- **Finite fibres descend from `pullback.fst h h` to `h`** (PROVEN
2026-07-27).  General scheme theory, no group structure and no hypotheses on
`h` whatever.

The point is that the carrier of `X ×_Y X` surjects onto the set-theoretic
fibre product of the carriers (`Scheme.Pullback.exists_preimage_pullback`,
which is where the nonvanishing of `κ(u) ⊗_{κ(s)} κ(v)` is used).  So for `u`
in the fibre of `h` over `y`, the whole fibre `h ⁻¹' {y}` is the image under
`pullback.snd h h` of the fibre of `pullback.fst h h` over `u`. -/
theorem finite_preimage_of_finite_preimage_pullback_fst {X Y : Scheme.{u}} (h : X ⟶ Y)
    (H : ∀ x : X, (⇑(pullback.fst h h) ⁻¹' {x}).Finite) (y : Y) :
    (⇑h ⁻¹' {y}).Finite := by
  rcases Set.eq_empty_or_nonempty (⇑h ⁻¹' {y}) with he | ⟨u, hu⟩
  · rw [he]; exact Set.finite_empty
  · refine ((H u).image ⇑(pullback.snd h h)).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu hv
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := h) (g := h) u v (hu.trans hv.symm)
    exact ⟨z, by simpa using hz1, hz2⟩

namespace AbelianSchemeStruct

variable (ab : AbelianSchemeStruct f) (n : ℕ)

/-- Both projections of `A ×_{[n], A, [n]} A` lie over the same point of `S`,
because `[n]` is a morphism over `S`. -/
theorem pullbackSnd_comp_structure :
    pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ f
      = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by
  calc pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ f
      = pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ (ab.mulByNat n ≫ f) := by
        rw [ab.mulByNat_comp]
    _ = (pullback.snd (ab.mulByNat n) (ab.mulByNat n) ≫ ab.mulByNat n) ≫ f :=
        (Category.assoc _ _ _).symm
    _ = (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ ab.mulByNat n) ≫ f := by
        rw [pullback.condition]
    _ = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ (ab.mulByNat n ≫ f) :=
        Category.assoc _ _ _
    _ = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by rw [ab.mulByNat_comp]

/-- **The structure morphism of `ker[n] = A ×_{[n], A, e} S`**: the inclusion
`ker[n] ⟶ A` followed by `f` is the second projection.  Uses only
`mulByNat_comp` and `zeroSection_comp`. -/
theorem kerι_comp_structure :
    pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f
      = pullback.snd (ab.mulByNat n) ab.zeroSection := by
  calc pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f
      = pullback.fst (ab.mulByNat n) ab.zeroSection ≫ (ab.mulByNat n ≫ f) := by
        rw [ab.mulByNat_comp]
    _ = (pullback.fst (ab.mulByNat n) ab.zeroSection ≫ ab.mulByNat n) ≫ f :=
        (Category.assoc _ _ _).symm
    _ = (pullback.snd (ab.mulByNat n) ab.zeroSection ≫ ab.zeroSection) ≫ f := by
        rw [pullback.condition]
    _ = pullback.snd (ab.mulByNat n) ab.zeroSection ≫ (ab.zeroSection ≫ f) :=
        Category.assoc _ _ _
    _ = pullback.snd (ab.mulByNat n) ab.zeroSection := by
        rw [ab.zeroSection_comp, Category.comp_id]

/-- The first projection of `A ×_{[n], A, [n]} A`, read as a relative point. -/
noncomputable def shearFst :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ⟨pullback.fst (ab.mulByNat n) (ab.mulByNat n), rfl⟩

/-- The second projection of `A ×_{[n], A, [n]} A`, read as a relative point. -/
noncomputable def shearSnd :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ⟨pullback.snd (ab.mulByNat n) (ab.mulByNat n), ab.pullbackSnd_comp_structure n⟩

/-- The difference `q₂ - q₁` of the two projections, as a relative point.
Written with `ab.add`/`ab.neg` rather than `-` so that the definition carries
no `letI`. -/
noncomputable def shearDiff :
    RelPoint f (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) :=
  ab.add (ab.shearSnd n) (ab.neg (ab.shearFst n))

theorem shearDiff_eq_sub :
    letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
    ab.shearDiff n = ab.shearSnd n - ab.shearFst n := rfl

/-- **`n • (q₂ - q₁) = 0`**: this is `pullback.condition` read through
`nsmul_val`, and it is the whole reason the shearing lands in `ker[n]`. -/
theorem nsmul_shearDiff_eq_zero :
    letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
    n • ab.shearDiff n = 0 := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  rw [ab.shearDiff_eq_sub n, smul_sub, sub_eq_zero]
  refine Subtype.ext ?_
  rw [ab.nsmul_val, ab.nsmul_val]
  exact pullback.condition.symm

/-- `(q₂ - q₁) ≫ [n]` is the zero section: the difference factors through
`ker[n]`. -/
theorem shearDiff_comp_mulByNat :
    (ab.shearDiff n).1 ≫ ab.mulByNat n
      = (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f) ≫ ab.zeroSection := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  rw [← ab.nsmul_val n (ab.shearDiff n), ab.nsmul_shearDiff_eq_zero n]
  exact ab.zero_val _

/-- **The shearing morphism** `A ×_{[n], A, [n]} A ⟶ A ×_S ker[n]`,
`(u, v) ↦ (u, v - u)`. -/
noncomputable def kerShear :
    pullback (ab.mulByNat n) (ab.mulByNat n) ⟶
      pullback f (pullback.snd (ab.mulByNat n) ab.zeroSection) :=
  pullback.lift (pullback.fst (ab.mulByNat n) (ab.mulByNat n))
    (pullback.lift (ab.shearDiff n).1 (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
      (ab.shearDiff_comp_mulByNat n))
    (pullback.lift_snd _ _ _).symm

/-- The shearing is the identity in the `A`-coordinate — the fact that makes
it useful for comparing fibres of the two first projections. -/
theorem kerShear_fst :
    ab.kerShear n ≫ pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      = pullback.fst (ab.mulByNat n) (ab.mulByNat n) := by
  simp only [kerShear]
  exact pullback.lift_fst _ _ _

theorem kerShear_snd_fst :
    ab.kerShear n ≫ pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
        ≫ pullback.fst (ab.mulByNat n) ab.zeroSection
      = (ab.shearDiff n).1 := by
  rw [← Category.assoc]
  simp only [kerShear]
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- The first projection of `A ×_S ker[n]`, as a relative point. -/
noncomputable def unshearFst :
    RelPoint f (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) :=
  ⟨pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection), rfl⟩

/-- The `ker[n]`-component of `A ×_S ker[n]`, read as a relative point of `A`. -/
noncomputable def unshearSnd :
    RelPoint f (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) :=
  ⟨pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      ≫ pullback.fst (ab.mulByNat n) ab.zeroSection, by
    rw [Category.assoc, ab.kerι_comp_structure n]
    exact pullback.condition.symm⟩

/-- **A point of `ker[n]` is killed by `n`** — by construction, but this is
the form the shearing needs. -/
theorem nsmul_unshearSnd_eq_zero :
    letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
    n • ab.unshearSnd n = 0 := by
  letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
  refine Subtype.ext ?_
  rw [ab.nsmul_val]
  have hz : ((0 : RelPoint f
      (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f))).1
      = (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f) ≫ ab.zeroSection :=
    ab.zero_val _
  rw [hz]
  show (pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
      ≫ pullback.fst (ab.mulByNat n) ab.zeroSection) ≫ ab.mulByNat n = _
  rw [Category.assoc, pullback.condition (f := ab.mulByNat n) (g := ab.zeroSection),
    ← Category.assoc, ← pullback.condition, Category.assoc]

/-- **The inverse shearing** `A ×_S ker[n] ⟶ A ×_{[n], A, [n]} A`,
`(u, k) ↦ (u, u + k)`.  It lands in the fibre product because `n • k = 0`. -/
noncomputable def kerUnshear :
    pullback f (pullback.snd (ab.mulByNat n) ab.zeroSection) ⟶
      pullback (ab.mulByNat n) (ab.mulByNat n) :=
  pullback.lift (ab.unshearFst n).1 (ab.add (ab.unshearFst n) (ab.unshearSnd n)).1 (by
    letI := ab.addCommGroup (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
    have h : n • (ab.unshearFst n) = n • (ab.unshearFst n + ab.unshearSnd n) := by
      rw [smul_add, ab.nsmul_unshearSnd_eq_zero, add_zero]
    have h2 := congrArg Subtype.val h
    rwa [ab.nsmul_val, ab.nsmul_val] at h2)

theorem kerUnshear_fst :
    ab.kerUnshear n ≫ pullback.fst (ab.mulByNat n) (ab.mulByNat n) = (ab.unshearFst n).1 := by
  simp only [kerUnshear]
  exact pullback.lift_fst _ _ _

theorem kerUnshear_snd :
    ab.kerUnshear n ≫ pullback.snd (ab.mulByNat n) (ab.mulByNat n)
      = (ab.add (ab.unshearFst n) (ab.unshearSnd n)).1 := by
  simp only [kerUnshear]
  exact pullback.lift_snd _ _ _

/-- **`kerShear` is a split monomorphism**: `(u, v) ↦ (u, v - u) ↦ (u, u + (v - u))`
is the identity.  Only this round trip is proven — injectivity on points is all
the fibre comparison needs — and the naturality axiom `pre_add` is what turns
the computation into the group identity `u + (v - u) = v`. -/
theorem kerShear_kerUnshear : ab.kerShear n ≫ ab.kerUnshear n = 𝟙 _ := by
  letI := ab.addCommGroup (pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f)
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ab.kerUnshear_fst n, Category.id_comp]
    show ab.kerShear n ≫ pullback.fst f _ = _
    exact ab.kerShear_fst n
  · rw [Category.assoc, ab.kerUnshear_snd n, Category.id_comp]
    have hg : ab.kerShear n ≫ (pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection) ≫ f)
        = pullback.fst (ab.mulByNat n) (ab.mulByNat n) ≫ f := by
      rw [← Category.assoc, ab.kerShear_fst n]
    have key := ab.pre_add (ab.kerShear n) hg (ab.unshearFst n) (ab.unshearSnd n)
    have h1 : RelPoint.pre (ab.kerShear n) hg (ab.unshearFst n) = ab.shearFst n :=
      Subtype.ext (ab.kerShear_fst n)
    have h2 : RelPoint.pre (ab.kerShear n) hg (ab.unshearSnd n) = ab.shearDiff n :=
      Subtype.ext (by
        show ab.kerShear n ≫ (pullback.snd f (pullback.snd (ab.mulByNat n) ab.zeroSection)
            ≫ pullback.fst (ab.mulByNat n) ab.zeroSection) = _
        exact ab.kerShear_snd_fst n)
    rw [h1, h2] at key
    have h3 : ab.add (ab.shearFst n) (ab.shearDiff n) = ab.shearSnd n := by
      show ab.shearFst n + ab.shearDiff n = ab.shearSnd n
      rw [ab.shearDiff_eq_sub n, add_sub_cancel]
    exact congrArg Subtype.val (key.trans h3)

/-- **ZMT bridge**: `ker[n] ⟶ S` is a FINITE MORPHISM as soon as each of its
fibres is a finite SET (PROVEN 2026-07-27).

`[n]` is proper and locally of finite type, hence so is its base change
`ker[n] ⟶ S`; `LocallyQuasiFinite.of_finite_preimage_singleton` then gives
quasi-finiteness and `IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's
main theorem) upgrades it.  Over a field the hypothesis is a single finite
point set — the classical "`ker[n]` is zero-dimensional". -/
theorem isFinite_ker_mulByNat_of_finite_preimage
    (H : ∀ s : S, (⇑(pullback.snd (ab.mulByNat n) ab.zeroSection) ⁻¹' {s}).Finite) :
    IsFinite (pullback.snd (ab.mulByNat n) ab.zeroSection) := by
  haveI : IsProper (ab.mulByNat n) := ab.isProper_mulByNat n
  haveI : LocallyOfFiniteType (ab.mulByNat n) := ab.locallyOfFiniteType_mulByNat n
  haveI : LocallyQuasiFinite (pullback.snd (ab.mulByNat n) ab.zeroSection) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ H
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **EVERY fibre of `[n]` is finite as soon as `ker[n] ⟶ S` is a finite
morphism** (PROVEN 2026-07-27) — i.e. as soon as `[n]` is an ISOGENY.

Cube-free, `n`-generic, characteristic-blind, and stated over an ARBITRARY
base `S`.  This is the reduction described in the section header: shear
`A ×_{[n], A, [n]} A` onto `A ×_S ker[n]`, note that the first projection of
the latter is a base change of `ker[n] ⟶ S` and so has finite fibres, and then
descend along `finite_preimage_of_finite_preimage_pullback_fst`. -/
theorem finite_preimage_mulByNat_of_isFinite_ker
    (hker : IsFinite (pullback.snd (ab.mulByNat n) ab.zeroSection)) (a : A) :
    (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI := hker
  refine finite_preimage_of_finite_preimage_pullback_fst (ab.mulByNat n) (fun x => ?_) a
  have hQ : (⇑(pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)) ⁻¹' {x}).Finite :=
    Scheme.Hom.finite_preimage_singleton _ x
  have hinj : Function.Injective ⇑(ab.kerShear n) := by
    intro c d hcd
    have h1 : (ab.kerShear n ≫ ab.kerUnshear n) c = (ab.kerShear n ≫ ab.kerUnshear n) d := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcd]
    rw [ab.kerShear_kerUnshear n] at h1
    simpa using h1
  have hset : (⇑(pullback.fst (ab.mulByNat n) (ab.mulByNat n)) ⁻¹' {x})
      = ⇑(ab.kerShear n) ⁻¹'
        (⇑(pullback.fst f (pullback.snd (ab.mulByNat n) ab.zeroSection)) ⁻¹' {x}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← ab.kerShear_fst n, Scheme.Hom.comp_apply]
  rw [hset]
  exact hQ.preimage hinj.injOn

end AbelianSchemeStruct

/-- **A QUASI-AFFINE scheme that is universally closed over an affine scheme is
AFFINE** (PROVEN 2026-07-27; general scheme theory, nothing abelian in it).

This is EGA II 5.1.6's "quasi-affine + proper ⟹ affine", and it is the last
step of the classical ample-line-bundle proof of
`isQuasiAffine_ker_mulByNat_of_field_char` below.  Proving it here is what lets
that leaf be stated as `IsQuasiAffine` — *literally* the sentence the ample
argument produces — instead of `IsAffine`.

The proof is four lines of mathlib.  `X.toSpecΓ` is an OPEN immersion because
`X` is quasi-affine (mathlib's `Scheme.IsQuasiAffine` instance); it is
UNIVERSALLY CLOSED by cancellation, since `X.toSpecΓ ≫ Spec.map f.appTop` is
`f ≫ Y.toSpecΓ` with `Y.toSpecΓ` an isomorphism (`Y` affine) and
`Spec.map f.appTop` separated (a morphism of affine schemes).  An open immersion
with closed range is a CLOSED immersion (`IsClosedImmersion.of_isPreimmersion`),
closed immersions are affine morphisms, and an affine morphism to the affine
scheme `Spec Γ(X, ⊤)` forces `IsAffine X` (`isAffine_of_isAffineHom`).

Note the hypothesis is `UniversallyClosed`, not `IsProper`: separatedness is
free from `IsQuasiAffine` and finite type is not used at all. -/
theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.IsQuasiAffine] [UniversallyClosed f] [IsAffine Y] :
    IsAffine X := by
  have h₁ : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have h₂ : UniversallyClosed X.toSpecΓ :=
    .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have h₃ : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _
      (Set.image_univ ▸ X.toSpecΓ.isClosedMap _ isClosed_univ)
  exact isAffine_of_isAffineHom X.toSpecΓ

namespace AbelianSchemeStruct

/-- **The zero section base-changes to the zero section** (PROVEN 2026-07-27):
`e_{A_T} ≫ pr_A = g ≫ e_A`.

Unfolding, `(ab.baseChange g).zeroSection` is `RelPoint.baseChangeUp g (ab.zero (𝟙 T ≫ g))`,
whose underlying morphism is `pullback.lift (ab.zero (𝟙 T ≫ g)).1 (𝟙 T) _`; composing
with `pullback.fst` reads off the first component, and `zero_val` rewrites it as
`(𝟙 T ≫ g) ≫ ab.zeroSection`.

This is the second of the two squares — `baseChange_mulByNat` is the first — that
identify `ker[n]` of a base change with the base change of `ker[n]`; see
`isPullback_ker_baseChange` immediately below. -/
theorem baseChange_zeroSection (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S) :
    (ab.baseChange g).zeroSection ≫ pullback.fst f g = g ≫ ab.zeroSection := by
  show ((ab.baseChange g).zero (𝟙 T)).1 ≫ pullback.fst f g = _
  rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeUp_val, pullback.lift_fst,
    ab.zero_val, Category.id_comp]

/-- **`ker[n]` OF A BASE CHANGE IS THE BASE CHANGE OF `ker[n]`** (PROVEN
2026-07-27) — stated as the assertion that the comparison square

```
  ker[n]_{A_T} ---φ---> ker[n]_A
       |                    |
       v                    v
       T --------g--------> S
```

is CARTESIAN, where `φ` is `pullback.map` along the projection `pr_A : A_T ⟶ A`.

**This is what makes "WLOG the base field is algebraically closed" available**
(route 9 of `isQuasiAffine_ker_mulByNat_of_isAlgClosed` below): with the square
cartesian, `Surjective` — being stable under base change
(`Mathlib/AlgebraicGeometry/PullbackCarrier.lean`) — carries a surjection
`T ↠ S` up to a surjection `ker[n]_{A_T} ↠ ker[n]_A`, and a finite point set
descends along it.

**The proof is two applications of the pasting lemma and nothing else.**  No new
theory, no abelian-variety input; both inputs are the two base-change squares
above.

1. *`[n]` on `A_T` is the base change of `[n]` on `A` along `pr_A`.*  Paste the
   candidate square on top of the defining square of `A_T = A ×_S T`: the
   pasted square is again the defining square, because `[n]' ≫ pr_T = pr_T`
   (`mulByNat_comp`) and `[n] ≫ f = f`.  `IsPullback.of_bot` then extracts the
   top square.
2. *Fold that into the kernel.*  Paste the defining square of
   `ker[n]_{A_T} = A_T ×_{[n]', e'} T` horizontally with the square from 1;
   after rewriting `e' ≫ pr_A = g ≫ e` (`baseChange_zeroSection`) the result is
   the horizontal composite of the wanted square with the defining square of
   `ker[n]_A`, so `IsPullback.of_right` extracts the wanted square. -/
theorem isPullback_ker_baseChange (ab : AbelianSchemeStruct f) {T : Scheme.{u}} (g : T ⟶ S)
    (n : ℕ) :
    IsPullback
      (pullback.map ((ab.baseChange g).mulByNat n) (ab.baseChange g).zeroSection
        (ab.mulByNat n) ab.zeroSection (pullback.fst f g) g (pullback.fst f g)
        (ab.baseChange_mulByNat g n) (ab.baseChange_zeroSection g))
      (pullback.snd ((ab.baseChange g).mulByNat n) (ab.baseChange g).zeroSection)
      (pullback.snd (ab.mulByNat n) ab.zeroSection) g := by
  have hsqbc : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have hsqp : IsPullback (pullback.fst f g) ((ab.baseChange g).mulByNat n)
      (ab.mulByNat n) (pullback.fst f g) := by
    refine IsPullback.of_bot ?_ (ab.baseChange_mulByNat g n).symm hsqbc
    rw [(ab.baseChange g).mulByNat_comp n, ab.mulByNat_comp n]
    exact hsqbc
  have hker' : IsPullback
      (pullback.fst ((ab.baseChange g).mulByNat n) (ab.baseChange g).zeroSection)
      (pullback.snd ((ab.baseChange g).mulByNat n) (ab.baseChange g).zeroSection)
      ((ab.baseChange g).mulByNat n) (ab.baseChange g).zeroSection :=
    IsPullback.of_hasPullback _ _
  have hker : IsPullback (pullback.fst (ab.mulByNat n) ab.zeroSection)
      (pullback.snd (ab.mulByNat n) ab.zeroSection) (ab.mulByNat n) ab.zeroSection :=
    IsPullback.of_hasPullback _ _
  have houter := hker'.paste_horiz hsqp
  rw [ab.baseChange_zeroSection g] at houter
  refine IsPullback.of_right ?_ ?_ hker
  · rw [pullback.lift_fst]
    exact houter
  · exact pullback.lift_snd _ _ _

end AbelianSchemeStruct

/-! ### Sheaf-level bookkeeping for the theorem-of-the-cube cut

One identification that the tensor calculus does not yet state and that the
induction below needs.  It is PROVEN and it is not new mathematics.

**THE SECOND ONE HAS GONE UPSTREAM, WHICH IS WHERE THIS NOTE ASKED FOR IT
(2026-07-30, at the release-22 merge).**  This block used to declare
`isInvertibleSheaf_modPullback` here as well, with the note: it is exactly the
statement `Fermat.exists_abelJacobiPoint`'s docstring
(`ModularCurve/RelativePicard.lean`) names as the piece blocking its `aj_pre`
clause ("*that* needs **`IsInvertibleSheaf (modPullback h N)`**, which is absent
from this module"), it belongs in the tensor-calculus section there, and it sat
here only because the proof ran through `exists_trivialization_modPullback`
(`Modularity/AmpleSheaf.lean`), DOWNSTREAM of `RelativePicard.lean` — so the
requested home needed "either a different proof or a hoist of the trivialization
machinery".

It got the different proof.  `RelativePicard.lean`:906 now proves it directly
from `modRestrictPullbackIso` / `modPullbackCompIso` / `modPullbackUnitIso`, with
no trivialization machinery at all, so the copy here was a duplicate declaration
at the same root namespace in a module that imports it — which is a hard error,
and is how it was found.  Deleted; the consumers below resolve to the upstream
one, whose signature is identical. -/

/-- **`(𝟙_X)^* L ≅ L`** — `Scheme.Modules.pullbackId`, read on an object.  The
missing companion of `modPullbackCompIso`/`modPullbackCongrIso`. -/
noncomputable def modPullbackIdIso {X : Scheme.{u}} (L : X.Modules) :
    modPullback (𝟙 X) L ≅ L :=
  (Scheme.Modules.pullbackId X).app L

/-! ### THE THEOREM OF THE CUBE, AT THE SHEAF LEVEL

(Cut 2026-07-28.)  Two leaves in this development asked for the *same*
geometry in two different packagings, and neither could be proven without the
other's content:

* `exists_isAmpleSheaf_cube_of_isAlgClosed` immediately below — a symmetric
  ample `L` with `[n]^* L ≅ L^{⊗ n²}`, over an algebraically closed field,
  consumed by `isQuasiAffine_ker_mulByNat_of_isAlgClosed`;
* `Fermat.exists_cubeModel_of_abelianScheme`
  (`Fermat/FLT/ModularCurve/X0.lean`) — a symmetric very ample `L` over `ℚ`
  with the cube written in COORDINATES, consumed by the geometric half of
  Mordell–Weil.

The common input is one statement, and it is the one written here:
`exists_isAmpleSheaf_symmetric_cube`.  Over ANY field, an abelian variety
carries an invertible sheaf that is ample, SYMMETRIC (`[−1]^* L ≅ L`),
NORMALIZED (`e^* L ≅ 𝒪_S`), and satisfies the theorem of the cube in its
symmetric two-variable form

  `σ^* L ⊗ δ^* L  ≅  p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}`   on `A ×_S A`,

with `σ (P, Q) = P + Q` and `δ (P, Q) = P − Q`.  Both consumers are then
derived from it: the `[n]^*` form by the classical induction
(`nonempty_modPullback_mulByNat_of_cube`), the coordinate form by the
coordinate dictionary in `X0.lean`.

**WHY THE TWO-VARIABLE FORM IS THE RIGHT PRIMITIVE, and not `[n]^*L ≅ L^{n²}`.**
The `[n]^*` form is a *consequence* of the cube taken along the two morphisms
`(P, Q) ↦ ([n]P, P)`; the converse is not available, because the `[n]^*` form
says nothing about a pair of independent points.  The coordinate consumer needs
exactly the pair statement — its whole content is that the SEGRE PRODUCT of
`φ(P+Q)` and `φ(P−Q)` has bidegree `(2,2)` in `(φ(P), φ(Q))`, and a producer
that establishes `h(2P)` alone has not proven the parallelogram law.  So the
pair form is strictly stronger and is what both consumers factor through.

**Relation to `Fermat.addHom` / `Fermat.negHom` in `X0.lean`.**  Those are the
same construction specialised to the base `SpecQ`; `ab.sumHom` and
`ab.negSelfHom` are stated over an arbitrary base because the sheaf statement
here has to serve the algebraically-closed consumer as well.  They are not
merely equal but DEFINITIONALLY the same terms at `S = SpecQ`, so no transport
lemma is needed; `X0.lean` keeps its own names because they are used a few
dozen times there. -/

namespace AbelianSchemeStruct

/-- **Inversion `[−1] : A ⟶ A`, as a morphism of schemes** — the Yoneda
realization of `ab.neg` at the tautological point `RelPoint.self`, exactly as
`mulByNat` is the Yoneda realization of `n • ·`.  `mulByNat` covers only
`n : ℕ`, so `[−1]` needs a name of its own. -/
noncomputable def negSelfHom {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) :
    X ⟶ X :=
  (ab.neg (RelPoint.self q)).1

/-- **NEGATION OF RELATIVE POINTS IS PRECOMPOSITION WITH `negSelfHom`** (PROVEN
2026-07-30) — the Yoneda statement that `negSelfHom` really is `[-1]`, proved
verbatim as `nsmul_val` is, over naturality of `neg` and `RelPoint.pre_self`.

Naturality of `neg` is inlined rather than named, for the reason recorded in
`diff_val` below: `AbelianSchemeStruct.pre_neg` already exists DOWNSTREAM in
`ModularCurve/X0.lean`. -/
theorem neg_val {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q)
    {T' : Scheme.{u}} {g : T' ⟶ T} (y : RelPoint q g) :
    (ab.neg y).1 = y.1 ≫ ab.negSelfHom := by
  have hpre : ∀ {U' U : Scheme.{u}} (h : U' ⟶ U) {b : U ⟶ T} {b' : U' ⟶ T}
      (hb : h ≫ b = b') (z : RelPoint q b),
      RelPoint.pre h hb (ab.neg z) = ab.neg (RelPoint.pre h hb z) := by
    intro U' U h b b' hb z
    letI := ab.addCommGroup b'
    have e1 : ab.add (RelPoint.pre h hb (ab.neg z)) (RelPoint.pre h hb z) = ab.zero b' := by
      rw [← ab.pre_add h hb, ab.neg_add, ab.pre_zero]
    have e2 : ab.add (ab.neg (RelPoint.pre h hb z)) (RelPoint.pre h hb z) = ab.zero b' :=
      ab.neg_add _
    exact add_right_cancel (e1.trans e2.symm)
  conv_lhs => rw [← RelPoint.pre_self y]
  rw [← hpre y.1 y.2 (RelPoint.self q)]
  rfl

/-- **`[-1]` is a morphism over the base.** -/
theorem negSelfHom_comp {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) :
    ab.negSelfHom ≫ q = q :=
  (ab.neg (RelPoint.self q)).2

/-- **`[-1]` IS AN INVOLUTION** (PROVEN 2026-07-30): `neg_val` read at the point
`-(RelPoint.self q)`, whose negative is `RelPoint.self q` by `neg_neg`. -/
theorem negSelfHom_comp_negSelfHom {X T : Scheme.{u}} {q : X ⟶ T}
    (ab : AbelianSchemeStruct q) : ab.negSelfHom ≫ ab.negSelfHom = 𝟙 X := by
  letI := ab.addCommGroup q
  have h := ab.neg_val (ab.neg (RelPoint.self q))
  have hnn : ab.neg (ab.neg (RelPoint.self q)) = RelPoint.self q := neg_neg (RelPoint.self q)
  rw [hnn] at h
  exact h.symm

/-- **`[-1]` IS AN ISOMORPHISM** — it is its own inverse.

This is what makes `isAmpleSheaf_modPullback` (stated for a CLOSED IMMERSION)
apply to `[-1]`, and it is the whole reason the symmetrization step of
`exists_isAmpleSheaf_symmetric_cube` can be written: the pin has
`instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f`
(`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean`), so ampleness under
pullback along an isomorphism needs no new statement at all. -/
theorem isIso_negSelfHom {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) :
    IsIso ab.negSelfHom :=
  ⟨ab.negSelfHom, ab.negSelfHom_comp_negSelfHom, ab.negSelfHom_comp_negSelfHom⟩

/-- **The sum morphism `σ : A ×_S A ⟶ A`**, `(P, Q) ↦ P + Q`: `ab.add` applied
to the two projections, read as relative points over the common base point
`p₁ ≫ f`. -/
noncomputable def sumHom {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) :
    pullback q q ⟶ X :=
  (ab.add (⟨pullback.fst q q, rfl⟩ : RelPoint q (pullback.fst q q ≫ q))
    (⟨pullback.snd q q, pullback.condition.symm⟩ :
      RelPoint q (pullback.fst q q ≫ q))).1

/-- **The difference morphism `δ : A ×_S A ⟶ A`**, `(P, Q) ↦ P − Q`. -/
noncomputable def diffHom {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) :
    pullback q q ⟶ X :=
  (ab.add (⟨pullback.fst q q, rfl⟩ : RelPoint q (pullback.fst q q ≫ q))
    (ab.neg (⟨pullback.snd q q, pullback.condition.symm⟩ :
      RelPoint q (pullback.fst q q ≫ q)))).1

/-- **`ab.add` IS PRECOMPOSITION WITH `sumHom`** (PROVEN 2026-07-30) — the
Yoneda statement that `σ` really is the group law, proved exactly as `nsmul_val`
is: `pre_add` read along the map `⟨x, y⟩ : T' ⟶ A ×_S A` determined by the two
points, whose two projections are `x` and `y` by `pullback.lift_fst`/`lift_snd`.

This is what turns the two-variable cube into a statement about `[n]`: restricting
`HasCubeIso` along `⟨[n+1], 𝟙⟩` needs `σ ∘ ⟨[n+1], 𝟙⟩ = [n+2]`, which is this
lemma plus `succ_nsmul` and nothing else.

**`Fermat.add_eq_addHom` in `ModularCurve/X0.lean` is the same statement for
`addHom` at the base `SpecQ`.**  It is not reused because it is DOWNSTREAM of
this module; the hoist that would merge the two is the one recorded against
`AbelianSchemeStruct.pre_neg` below. -/
theorem sum_val {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q)
    {T' : Scheme.{u}} {g : T' ⟶ T} (x y : RelPoint q g) :
    (ab.add x y).1 = pullback.lift x.1 y.1 (by rw [x.2, y.2]) ≫ ab.sumHom := by
  set u : T' ⟶ pullback q q := pullback.lift x.1 y.1 (by rw [x.2, y.2]) with hu
  have hg : u ≫ pullback.fst q q ≫ q = g := by
    rw [← Category.assoc, hu, pullback.lift_fst, x.2]
  have h := ab.pre_add u hg (⟨pullback.fst q q, rfl⟩ : RelPoint q (pullback.fst q q ≫ q))
    (⟨pullback.snd q q, pullback.condition.symm⟩ : RelPoint q (pullback.fst q q ≫ q))
  have h1 : RelPoint.pre u hg (⟨pullback.fst q q, rfl⟩ :
      RelPoint q (pullback.fst q q ≫ q)) = x := by
    refine Subtype.ext ?_
    show u ≫ pullback.fst q q = x.1
    rw [hu, pullback.lift_fst]
  have h2 : RelPoint.pre u hg (⟨pullback.snd q q, pullback.condition.symm⟩ :
      RelPoint q (pullback.fst q q ≫ q)) = y := by
    refine Subtype.ext ?_
    show u ≫ pullback.snd q q = y.1
    rw [hu, pullback.lift_snd]
  rw [h1, h2] at h
  exact (congrArg Subtype.val h).symm

/-- **`ab.add x (ab.neg y)` IS PRECOMPOSITION WITH `diffHom`** (PROVEN
2026-07-30) — `sum_val` with naturality of `neg` spliced in.

**NATURALITY OF `neg` IS INLINED RATHER THAN NAMED, AND THAT IS DELIBERATE — the
name is already taken DOWNSTREAM.**  `Fermat.AbelianSchemeStruct.pre_neg` exists
in `ModularCurve/X0.lean`, which `public import`s THIS module, so declaring it
here would break `X0.lean` with "has already been declared" while this module
still built green — the single-module-build blind spot.  A THIRD copy of the same
statement is `Fermat.relPointPre_neg` in `ModularCurve/EllipticScheme.lean`,
whose docstring already records the duplication and asks for a hoist.  The right
home for all three is `Modularity/AbelianScheme.lean`, where
`AbelianSchemeStruct` is defined and which is upstream of every consumer; that
hoist is left to an owner of those files, and adding a FOURTH site here would
make it worse.

The argument is cancellation, not a new axiom: `neg x` is the unique solution of
`· + x = 0`, and `pre` preserves `+` and `0` by `pre_add`/`pre_zero`. -/
theorem diff_val {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q)
    {T' : Scheme.{u}} {g : T' ⟶ T} (x y : RelPoint q g) :
    (ab.add x (ab.neg y)).1 = pullback.lift x.1 y.1 (by rw [x.2, y.2]) ≫ ab.diffHom := by
  have hpre : ∀ {U' U : Scheme.{u}} (h : U' ⟶ U) {b : U ⟶ T} {b' : U' ⟶ T}
      (hb : h ≫ b = b') (z : RelPoint q b),
      RelPoint.pre h hb (ab.neg z) = ab.neg (RelPoint.pre h hb z) := by
    intro U' U h b b' hb z
    letI := ab.addCommGroup b'
    have e1 : ab.add (RelPoint.pre h hb (ab.neg z)) (RelPoint.pre h hb z) = ab.zero b' := by
      rw [← ab.pre_add h hb, ab.neg_add, ab.pre_zero]
    have e2 : ab.add (ab.neg (RelPoint.pre h hb z)) (RelPoint.pre h hb z) = ab.zero b' :=
      ab.neg_add _
    exact add_right_cancel (e1.trans e2.symm)
  set u : T' ⟶ pullback q q := pullback.lift x.1 y.1 (by rw [x.2, y.2]) with hu
  have hg : u ≫ pullback.fst q q ≫ q = g := by
    rw [← Category.assoc, hu, pullback.lift_fst, x.2]
  have h := ab.pre_add u hg (⟨pullback.fst q q, rfl⟩ : RelPoint q (pullback.fst q q ≫ q))
    (ab.neg (⟨pullback.snd q q, pullback.condition.symm⟩ :
      RelPoint q (pullback.fst q q ≫ q)))
  rw [hpre u hg] at h
  have h1 : RelPoint.pre u hg (⟨pullback.fst q q, rfl⟩ :
      RelPoint q (pullback.fst q q ≫ q)) = x := by
    refine Subtype.ext ?_
    show u ≫ pullback.fst q q = x.1
    rw [hu, pullback.lift_fst]
  have h2 : RelPoint.pre u hg (⟨pullback.snd q q, pullback.condition.symm⟩ :
      RelPoint q (pullback.fst q q ≫ q)) = y := by
    refine Subtype.ext ?_
    show u ≫ pullback.snd q q = y.1
    rw [hu, pullback.lift_snd]
  rw [h1, h2] at h
  exact (congrArg Subtype.val h).symm

/-- **THE THEOREM OF THE CUBE for `L`**, in its symmetric two-variable form

  `σ^* L ⊗ δ^* L  ≅  p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}`   on `A ×_S A`.

This is the identity that Mumford, *Abelian Varieties* §6 derives from the
theorem of the cube for a SYMMETRIC `L`; for a general `L` the right-hand side
reads `p₁^*(L ⊗ [−1]^* L) ⊗ p₂^*(L ⊗ [−1]^* L)` instead, so asserting this form
asserts symmetry implicitly (and `exists_isAmpleSheaf_symmetric_cube` asserts
it explicitly beside it, because both consumers want it by name).

`Nonempty`, not a chosen isomorphism: no consumer depends on WHICH
isomorphism, only on its existence. -/
def HasCubeIso {X T : Scheme.{u}} {q : X ⟶ T} (ab : AbelianSchemeStruct q) (L : X.Modules) :
    Prop :=
  Nonempty (modTensor (modPullback ab.sumHom L) (modPullback ab.diffHom L) ≅
    modTensor (modPullback (pullback.fst q q) (modTensorPow L 2))
      (modPullback (pullback.snd q q) (modTensorPow L 2)))

end AbelianSchemeStruct

/-- **THE CUBE, IN THE RECURSION FORM MUMFORD'S INDUCTION USES** (PROVEN
2026-07-30 from `HasCubeIso` ALONE — no field, no ampleness, no symmetry
hypothesis, and no new leaf):

  `[n+2]^* L ⊗ [n]^* L  ≅  ([n+1]^* L)^{⊗2} ⊗ L^{⊗2}`.

**THE PROOF IS ONE RESTRICTION.**  Let `u := ⟨[n+1], 𝟙⟩ : X ⟶ X ×_T X`, i.e.
`P ↦ ([n+1]P, P)`.  Its four composites are pure Yoneda:

* `u ≫ p₁ = [n+1]` and `u ≫ p₂ = 𝟙` — `pullback.lift_fst`/`lift_snd`;
* `u ≫ σ = [n+2]` — `sum_val` at the pair `((n+1) • self, self)` together with
  `succ_nsmul`;
* `u ≫ δ = [n]` — `diff_val` at the same pair, since `(n+1) • s - s = n • s`.

Pulling `HasCubeIso` back along `u` and pushing `u^*` through the four tensors
(`nonempty_modPullback_modTensor`, `modPullbackCompIso`, `modPullbackCongrIso`,
`nonempty_modPullback_modTensorPow`, `modPullbackIdIso`) then reads off exactly
the displayed identity.

**WHY THIS SHAPE, AND WHY IT IS NOT A WEAKENING.**  The two-variable form is
strictly stronger (see the section docstring), and this recursion is the only
consequence of it the `[n]^*` induction needs; separating them keeps the
mathlib-scale content in `exists_isAmpleSheaf_symmetric_cube` and leaves this
step, which is bookkeeping, verifiable on its own.  The indexing is shifted by
one from the textbook form `[n+1]^*L ⊗ [n−1]^*L ≅ ([n]^*L)^{⊗2} ⊗ L^{⊗2}`
precisely so that no `Nat` subtraction appears. -/
theorem nonempty_modTensor_modPullback_mulByNat_cube {X T : Scheme.{u}} {q : X ⟶ T}
    (ab : AbelianSchemeStruct q) (L : X.Modules) (hcube : ab.HasCubeIso L) (n : ℕ) :
    Nonempty (modTensor (modPullback (ab.mulByNat (n + 2)) L)
          (modPullback (ab.mulByNat n) L)
        ≅ modTensor (modTensorPow (modPullback (ab.mulByNat (n + 1)) L) 2)
          (modTensorPow L 2)) := by
  letI := ab.addCommGroup q
  obtain ⟨ec⟩ := hcube
  -- the shear `u : P ↦ ([n+1]P, P)`
  have hlift : ab.mulByNat (n + 1) ≫ q = 𝟙 X ≫ q := by
    rw [ab.mulByNat_comp, Category.id_comp]
  set u : X ⟶ pullback q q := pullback.lift (ab.mulByNat (n + 1)) (𝟙 X) hlift with hu
  have hfst : u ≫ pullback.fst q q = ab.mulByNat (n + 1) := by rw [hu, pullback.lift_fst]
  have hsnd : u ≫ pullback.snd q q = 𝟙 X := by rw [hu, pullback.lift_snd]
  -- the two group-law composites, by Yoneda
  have hsum : u ≫ ab.sumHom = ab.mulByNat (n + 2) := by
    have h := ab.sum_val ((n + 1) • RelPoint.self q) (RelPoint.self q)
    have hadd : ab.add ((n + 1) • RelPoint.self q) (RelPoint.self q)
        = (n + 2) • RelPoint.self q := (succ_nsmul (RelPoint.self q) (n + 1)).symm
    rw [hadd] at h
    exact h.symm
  have hdiff : u ≫ ab.diffHom = ab.mulByNat n := by
    have h := ab.diff_val ((n + 1) • RelPoint.self q) (RelPoint.self q)
    have hadd : ab.add ((n + 1) • RelPoint.self q) (ab.neg (RelPoint.self q))
        = n • RelPoint.self q := by
      show (n + 1) • RelPoint.self q + -RelPoint.self q = n • RelPoint.self q
      rw [succ_nsmul]
      abel
    rw [hadd] at h
    exact h.symm
  -- restrict the cube isomorphism along `u`
  obtain ⟨t1⟩ := nonempty_modPullback_modTensor u (modPullback ab.sumHom L)
    (modPullback ab.diffHom L)
  obtain ⟨t2⟩ := nonempty_modPullback_modTensor u
    (modPullback (pullback.fst q q) (modTensorPow L 2))
    (modPullback (pullback.snd q q) (modTensorPow L 2))
  obtain ⟨tp⟩ := nonempty_modPullback_modTensorPow (ab.mulByNat (n + 1)) L 2
  have eL : modPullback u (modTensor (modPullback ab.sumHom L) (modPullback ab.diffHom L))
      ≅ modTensor (modPullback (ab.mulByNat (n + 2)) L)
        (modPullback (ab.mulByNat n) L) :=
    t1 ≪≫ modTensorMapIso
      (modPullbackCompIso u ab.sumHom L ≪≫ modPullbackCongrIso hsum L)
      (modPullbackCompIso u ab.diffHom L ≪≫ modPullbackCongrIso hdiff L)
  have eR : modPullback u (modTensor (modPullback (pullback.fst q q) (modTensorPow L 2))
        (modPullback (pullback.snd q q) (modTensorPow L 2)))
      ≅ modTensor (modTensorPow (modPullback (ab.mulByNat (n + 1)) L) 2)
        (modTensorPow L 2) :=
    t2 ≪≫ modTensorMapIso
      (modPullbackCompIso u (pullback.fst q q) (modTensorPow L 2) ≪≫
        modPullbackCongrIso hfst (modTensorPow L 2) ≪≫ tp)
      (modPullbackCompIso u (pullback.snd q q) (modTensorPow L 2) ≪≫
        modPullbackCongrIso hsnd (modTensorPow L 2) ≪≫ modPullbackIdIso (modTensorPow L 2))
  exact ⟨eL.symm ≪≫ modPullbackMapIso u ec ≪≫ eR⟩

/-! ### The four leaves of the 2026-07-30 cut of `exists_isAmpleSheaf_symmetric_cube`

**WHAT THE CUT SEPARATES, and why it is worth +3 leaves.**  The parent asserted
five things at once, of which exactly two are mathlib-scale and they are
mathematically independent of each other:

* `exists_isAmpleSheaf_of_field` — PROJECTIVITY of an abelian variety (theta
  divisors).  Says nothing about `[n]`, `[-1]`, symmetry or normalization;
* `hasCubeIso_of_symm_of_normalized` — THE THEOREM OF THE CUBE itself, for a
  sheaf that is already symmetric and normalized.  Says nothing about ampleness.

The other three conjuncts of the parent are formal consequences, and after this
cut they are written out rather than asserted: SYMMETRY comes from
`L := L₀ ⊗ [-1]^* L₀` and `negSelfHom_comp_negSelfHom`; NORMALIZATION comes from
`Pic (Spec K) = 0`; and ampleness of that tensor product is the one remaining
small geometric input, `isAmpleSheaf_modTensor`.

So the two hard leaves can now be attacked independently and neither has to
carry the other's hypotheses.  That is the whole point; the count going 1 → 4 is
disclosure of structure that was previously hidden inside one `sorry`.

**THIS BLOCK IS THE SALVAGE OF A RIVAL CUT.**  Branch `flt-lean-321` had proven
the same symmetrization argument against a different parent
(`exists_isAmpleSheaf_symm_of_isAlgClosed`, over `AbelianSchemeStruct.negMor`)
while `main` was replacing that shape with the two-variable one.  `main`'s shape
won — it is what `ModularCurve/X0.lean` consumes — and this is that branch's
mathematics re-expressed in it.  Two of its five leaves turned out to exist
already, upstream and PROVEN, as `nonempty_iso_of_modTensor_left` and
`modTensorComm`; the third became the theorem
`nonempty_modTensor_modPullback_mulByNat_cube` above. -/

/-- **AN ABELIAN VARIETY OVER A FIELD IS PROJECTIVE** (sorry leaf, cut 2026-07-30
out of `exists_isAmpleSheaf_symmetric_cube` above) — Mumford *Abelian Varieties*
§6, Application 1 / §16; equivalently Weil's theorem that an abelian variety is
projective.

*There is an ample invertible sheaf on `A`.*

**THIS IS ONE OF THE TWO MATHLIB-SCALE HALVES, AND IT IS NOW ISOLATED FROM
EVERYTHING ELSE.**  Nothing here mentions `[n]`, `[-1]`, normalization, symmetry
or the cube: the consumer manufactures all four from this sheaf by formal
operations.  The classical proof is the theta divisor — take an effective ample
divisor `D`, show `3D` is base-point free, and conclude — and it needs divisors,
linear systems and coherent cohomology, none of which exist at this pin
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY; re-run it before believing
this sentence).

**`IsInvertibleSheaf` is deliberately NOT asserted here.**  It is free:
`isInvertibleSheaf_of_isAmpleSheaf` (`AmpleSheaf.lean`, PROVEN) derives local
freeness of rank one from ampleness.  Asserting it would make this leaf strictly
harder for no gain.

**NO `[IsAlgClosed K]`, and that is a deliberate strengthening over the shape
this argument was first written in.**  Projectivity descends from the algebraic
closure, and the parent here is stated over an arbitrary field because BOTH its
consumers need it that way — the coordinate one over `ℚ`
(`Fermat.exists_cubeModel_of_abelianScheme`, `ModularCurve/X0.lean`) and the
algebraically-closed one through `exists_isAmpleSheaf_cube_of_isAlgClosed` below.
A prover who can only do the algebraically closed case should prove that first and
then descend, not weaken this statement.

**`ab` is genuinely used.**  "An ample sheaf exists" is false for a general proper
`X` — it says exactly that `X` is quasi-projective — and it is the group structure
that supplies the theta divisor. -/
theorem exists_isAmpleSheaf_of_field {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) :
    ∃ L : X.Modules, IsAmpleSheaf L :=
  sorry

/-- **`(L ⊗ M)^{⊗k} ≅ L^{⊗k} ⊗ M^{⊗k}`** (PROVEN 2026-07-30, in three lines) — the
`modTensorPow` half of what `isAmpleSheaf_modTensor` below needs.

Induction on `k` over `nonempty_modTensor_middleFour` (`AmpleSheaf.lean`, PROVEN):
`modTensorPow` is right-nested, so the successor step is literally
`(L ⊗ M) ⊗ (L^{⊗k} ⊗ M^{⊗k}) ≅ (L ⊗ L^{⊗k}) ⊗ (M ⊗ M^{⊗k})`, which is the
middle-four interchange with no reassociation on either side.  The base case is the
left unitor at `𝒪_Z`, backwards.

Like `isAmpleSheaf_modTensor` below this belongs in `Modularity/AmpleSheaf.lean`,
beside `nonempty_modTensorPow_mul`; it is here only so that the 2026-07-30 cut
lands in one file. -/
theorem nonempty_modTensorPow_modTensor {Z : Scheme.{u}} (L M : Z.Modules) (k : ℕ) :
    Nonempty (modTensorPow (modTensor L M) k ≅
      modTensor (modTensorPow L k) (modTensorPow M k)) := by
  induction k with
  | zero => exact ⟨(modTensorUnitLeftIso (modUnit Z)).symm⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨m4⟩ := nonempty_modTensor_middleFour L M (modTensorPow L k) (modTensorPow M k)
    exact ⟨modTensorMapIso (Iso.refl _) e ≪≫ m4⟩

/-- **A TENSOR OF TWO SECTIONS IS A GENERATOR EXACTLY WHERE BOTH FACTORS ARE**
(PROVEN 2026-07-30): `Z_{a ⊗ b} = Z_a ∩ Z_b`, for INVERTIBLE `A` and `B`.

This is the second half of what `isAmpleSheaf_modTensor` below needs, and it is
where the "a tensor of two sections is a unit exactly where both factors are"
clause of that leaf's route is discharged.

**INVERTIBILITY IS USED, AND ONLY TO PRODUCE TRIVIALIZATIONS.**  Both directions go
through `nonvanishingAt_iff_trivializedSection` at ONE common open: `hA` and `hB`
give trivializing neighbourhoods `U₁, U₂ ∋ z`, `trivializationOfLE` restricts both
to `U₁ ⊓ U₂`, and `exists_trivialization_modTensor` (`AmpleSheaf.lean`, PROVEN)
turns that pair into a trivialization `θ` of `A ⊗ B` there whose VALUE on
`tensorSection a b` is the honest product `trivializedSection φ a *
trivializedSection χ b`.  `Scheme.basicOpen_mul` then splits the membership.

It is the pinned VALUE that makes the `⊆` direction work: the anonymous
isomorphism `nonempty_restrict_modTensor` supplies would give a trivialization of
`A ⊗ B` but no equation, and the locus is not recoverable from it — the same
unit-scaling gap recorded on `exists_trivialization_modTensor` itself.

Like the two statements around it, this belongs in `Modularity/AmpleSheaf.lean`,
beside `nonvanishingLocus_tensorPowSection`. -/
theorem nonvanishingLocus_tensorSection {Z : Scheme.{u}} {A B : Z.Modules}
    (hA : IsInvertibleSheaf A) (hB : IsInvertibleSheaf B) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    nonvanishingLocus (modTensor A B) (tensorSection a b)
      = nonvanishingLocus A a ∩ nonvanishingLocus B b := by
  ext z
  obtain ⟨U₁, hz₁, ⟨φ₁⟩⟩ := hA z
  obtain ⟨U₂, hz₂, ⟨φ₂⟩⟩ := hB z
  have hz : z ∈ U₁ ⊓ U₂ := ⟨hz₁, hz₂⟩
  obtain ⟨θ, hθ⟩ := exists_trivialization_modTensor
    (trivializationOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) φ₁)
    (trivializationOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) φ₂)
  show NonvanishingAt _ _ z ↔ NonvanishingAt _ _ z ∧ NonvanishingAt _ _ z
  rw [nonvanishingAt_iff_trivializedSection _ θ hz,
    nonvanishingAt_iff_trivializedSection a _ hz,
    nonvanishingAt_iff_trivializedSection b _ hz, hθ a b, Scheme.basicOpen_mul]
  exact Iff.rfl

/-- **A TENSOR PRODUCT OF AMPLE INVERTIBLE SHEAVES IS AMPLE** (sorry leaf, cut
2026-07-30 out of `exists_isAmpleSheaf_symmetric_cube` above) — EGA II 4.5.7,
Hartshorne II Ex. 7.5.

ROUTE.  At `z`, ampleness of `L` gives `n > 0`, `s : Γ(L^{⊗n}, ⊤)` and an affine
`V` with `nonvanishingLocus s = V ∋ z`; ampleness of `M` gives `m > 0`,
`t : Γ(M^{⊗m}, ⊤)` and an affine `W ∋ z`.  Read `s^{⊗m} ⊗ t^{⊗n}` as a section of
`(L ⊗ M)^{⊗(nm)}` through `nonempty_modTensorPow_mul` and
`exists_trivialization_modTensor`; its non-vanishing locus is `V ⊓ W`, by
`nonvanishingLocus_tensorPowSection` and the fact that a tensor of two sections is
a unit exactly where both factors are.

**`[IsSeparated g]` OVER AN AFFINE BASE IS LOAD-BEARING, and it is the ONLY
geometric input.**  `IsAmpleSheaf` demands that the non-vanishing locus EQUAL an
affine open, and the locus produced above is `V ⊓ W`.  An intersection of two
affine opens is affine when the scheme is separated, and need not be otherwise —
the line with a doubled origin has two affine opens whose intersection is
`𝔸¹ ∖ {0}` glued to itself, i.e. not affine.  So a prover who finds the hypothesis
in the way should look for a different witness, not drop it.

Both hypotheses are FREE to the consumer: `ab.proper` supplies `IsSeparated fK`
and `Spec` is affine.

This statement belongs in `Modularity/AmpleSheaf.lean` beside
`isAmpleSheaf_modTensorPow` and `isAmpleSheaf_modPullback`; it is here only so
that this cut lands in one file.  Move it when convenient — and take the two
lemmas immediately above with it, which belong there for the same reason.

**PROVEN 2026-07-30**, along exactly the route above, over the two lemmas
`nonempty_modTensorPow_modTensor` and `nonvanishingLocus_tensorSection`
immediately above.  Two notes for a reader:

* the exponent is `n * m` on BOTH sides — `s^{⊗m}` lives in `(L^{⊗n})^{⊗m}` and
  `t^{⊗n}` in `(M^{⊗m})^{⊗n}`, so the right factor needs `Nat.mul_comm` and the
  left does not, which is the only asymmetry in the assembly;
* `[IsSeparated g]` and `[IsAffine W]` are consumed EXACTLY ONCE, and only to
  produce `Scheme.IsSeparated Z` (`g ≫ terminal.from W = terminal.from Z`) and
  through it the instance `IsAffineHom (pullback.diagonal (terminal.from Z))`
  that mathlib's `IsAffineOpen.inf` demands.  So the counterexample recorded
  above — the line with a doubled origin — is exactly what the hypothesis is
  bought against, and nothing else in the proof looks at `g`. -/
theorem isAmpleSheaf_modTensor {Z W : Scheme.{u}} (g : Z ⟶ W) [IsAffine W] [IsSeparated g]
    {L M : Z.Modules} (hL : IsAmpleSheaf L) (hM : IsAmpleSheaf M) :
    IsAmpleSheaf (modTensor L M) := by
  -- `Z` is separated over `⊤_ Scheme`, which is what `IsAffineOpen.inf` needs.
  haveI : Scheme.IsSeparated Z := by
    constructor
    have h : IsSeparated (g ≫ terminal.from W) := inferInstance
    rwa [terminal.comp_from] at h
  intro z
  obtain ⟨n, hn, s, V, hzV, hV, hlocV⟩ := hL z
  obtain ⟨m, hm, t, V', hzV', hV', hlocV'⟩ := hM z
  have hLinv : IsInvertibleSheaf L := isInvertibleSheaf_of_isAmpleSheaf hL
  have hMinv : IsInvertibleSheaf M := isInvertibleSheaf_of_isAmpleSheaf hM
  -- `s^{⊗m}` and `t^{⊗n}`, both read in degree `n * m`, with unchanged loci.
  obtain ⟨s', hs'⟩ := exists_tensorPowSection (k := m) (modTensorPow L n) s hm V hlocV
  obtain ⟨t', ht'⟩ := exists_tensorPowSection (k := n) (modTensorPow M m) t hn V' hlocV'
  obtain ⟨eL⟩ := nonempty_modTensorPow_mul L n m
  obtain ⟨eM⟩ := nonempty_modTensorPow_mul M m n
  have eM' : modTensorPow (modTensorPow M m) n ≅ modTensorPow M (n * m) :=
    eM ≪≫ eqToIso (by rw [Nat.mul_comm])
  set sL : Γ(modTensorPow L (n * m), ⊤) := eL.hom.val.app (Opposite.op ⊤) s' with hsL
  set tM : Γ(modTensorPow M (n * m), ⊤) := eM'.hom.val.app (Opposite.op ⊤) t' with htM
  have hlocL : nonvanishingLocus (modTensorPow L (n * m)) sL = (V : Set Z) := by
    rw [hsL, nonvanishingLocus_of_iso]; exact hs'
  have hlocM : nonvanishingLocus (modTensorPow M (n * m)) tM = (V' : Set Z) := by
    rw [htM, nonvanishingLocus_of_iso]; exact ht'
  obtain ⟨e⟩ := nonempty_modTensorPow_modTensor L M (n * m)
  refine ⟨n * m, Nat.mul_pos hn hm, e.symm.hom.val.app (Opposite.op ⊤) (tensorSection sL tM),
    V ⊓ V', ⟨hzV, hzV'⟩, hV.inf hV', ?_⟩
  rw [nonvanishingLocus_of_iso,
    nonvanishingLocus_tensorSection (isInvertibleSheaf_modTensorPow hLinv _)
      (isInvertibleSheaf_modTensorPow hMinv _), hlocL, hlocM]
  rfl

/-- **`Pic (Spec K) = 0` FOR A FIELD `K`** (**PROVEN 2026-07-30**; cut 2026-07-30) —
every invertible sheaf on the spectrum of a field is trivial.

ROUTE, and it is short — this is what was written.  `Spec K` has exactly ONE point
(`Unique (Spec (.of K))`, an instance in the pin for a field), so the only open
containing that point is `⊤`.  `IsInvertibleSheaf M` therefore hands back `U = ⊤`
together with `M.restrict (⊤ : Opens).ι ≅ modUnit ((⊤ : Opens) : Scheme)`, and all
that remains is to transport along the isomorphism `Scheme.topIso : (⊤ : Opens) ≅ Spec K`
of schemes.

The transport is done through `modPullback` rather than through
`Scheme.Modules.restrictUnitIso`, which is what the original route suggested:
`modRestrictPullbackIso` turns `M.restrict ⊤.ι` into `modPullback ⊤.ι M`, and then
pulling back along `Scheme.topIso.inv` and using `modPullbackCompIso`,
`Scheme.toIso_inv_ι` and `Scheme.Modules.pullbackId` gives `M` itself; the unit side
is `modPullbackUnitIso`.  Every one of those five is PROVEN upstream in
`ModularCurve/RelativePicard.lean`, so this leaf added no machinery.

**This is the ONE leaf of this cut that is not mathlib-scale**, and it is the
reason both `exists_isAmpleSheaf_symmetric_cube` and its coordinate sibling need
a FIELD base rather than an arbitrary one: over a base with `Pic S ≠ 0` the
normalization conjunct is simply false for the sheaf the construction produces. -/
theorem nonempty_iso_modUnit_of_isInvertibleSheaf_of_field (K : Type u) [Field K]
    (M : (Spec (CommRingCat.of K)).Modules) (hM : IsInvertibleSheaf M) :
    Nonempty (M ≅ modUnit (Spec (CommRingCat.of K))) := by
  -- `Spec K` has a unique point, so the trivializing open around it is `⊤`.
  obtain ⟨U, hzU, ⟨α⟩⟩ := hM default
  have hUtop : U = ⊤ :=
    le_antisymm le_top fun z _ => by rwa [Subsingleton.elim z default]
  subst hUtop
  -- transport along `Spec K ≃ (⊤ : (Spec K).Opens)`, which turns `M|_⊤ ≅ 𝒪_⊤` into `M ≅ 𝒪`.
  have hid : modPullback (𝟙 (Spec (CommRingCat.of K))) M ≅ M :=
    (Scheme.Modules.pullbackId (Spec (CommRingCat.of K))).app M
  have hchain : M ≅ modPullback (Spec (CommRingCat.of K)).topIso.inv
      (M.restrict (⊤ : (Spec (CommRingCat.of K)).Opens).ι) :=
    (modPullbackMapIso (Spec (CommRingCat.of K)).topIso.inv
        (modRestrictPullbackIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι M) ≪≫
      modPullbackCompIso (Spec (CommRingCat.of K)).topIso.inv
        (⊤ : (Spec (CommRingCat.of K)).Opens).ι M ≪≫
      modPullbackCongrIso (Scheme.toIso_inv_ι (Spec (CommRingCat.of K))) M ≪≫ hid).symm
  exact ⟨hchain ≪≫ modPullbackMapIso (Spec (CommRingCat.of K)).topIso.inv α ≪≫
    modPullbackUnitIso (Spec (CommRingCat.of K)).topIso.inv⟩

/-- **THE THEOREM OF THE CUBE, FOR A SYMMETRIC NORMALIZED INVERTIBLE SHEAF**
(sorry leaf, cut 2026-07-30 out of `exists_isAmpleSheaf_symmetric_cube` above):

  `σ^* L ⊗ δ^* L  ≅  p₁^* L^{⊗2} ⊗ p₂^* L^{⊗2}`   on `A ×_K A`.

**THIS IS THE OTHER MATHLIB-SCALE HALF, and it now carries NO ampleness
hypothesis.**  Mumford *Abelian Varieties* §6: the theorem of the cube proper —
for `L` on `A × A × A`, triviality on each of the three coordinate crosses forces
triviality — which at this pin needs the seesaw principle and flat base change for
coherent cohomology.  Neither exists.  `Fermat.modTensor` and `Fermat.modPullback`
make the STATEMENT writable and supply none of the proof.

**BOTH HYPOTHESES ARE LOAD-BEARING, and dropping either makes the statement
FALSE.**  The general corollary of the cube, applied to the three morphisms
`x = p₁`, `y = p₂`, `z = -p₂` on `A ×_K A`, reads

  `σ^* L ⊗ δ^* L  ≅  p₁^* L^{⊗2} ⊗ p₂^*(L ⊗ [-1]^* L) ⊗ (c^* L)^{-1}`

where `c : A ×_K A ⟶ Spec K ⟶ A` is the constant zero map.  So:

* `hsymm` is what turns `p₂^*(L ⊗ [-1]^* L)` into `p₂^* L^{⊗2}`.  Without it the
  statement fails for any `L` in `Pic⁰` with `L^{⊗2} ≇ 𝒪`: there `[-1]^* L ≅
  L^{-1}`, so the true right-hand side has `p₂`-part `𝒪` while the asserted one
  has `p₂^* L^{⊗2}`;
* `hzero` is what kills `(c^* L)^{-1}`.  Without it the statement fails by the
  constant factor `e^* L` — replace a normalized `L` by `L ⊗ f^* N` for a
  nontrivial invertible `N` on the base and the two sides differ by `p₁^* f^* N ⊗
  p₂^* f^* N ⊗ (c^* f^* N)^{-1}`.  (Over a FIELD `hzero` is free, by
  `nonempty_iso_modUnit_of_isInvertibleSheaf_of_field` above — which is why the
  consumer can supply it at no cost — but it is not free in the statement, and a
  prover who finds it unused has proved something else.)

**A prover who wants the general Corollary 2 as a separate leaf should cut it.**
It is the honest shape of the mathematics, and this statement is three formal
steps below it; it is not cut here only because this project forbids
free-floating declarations and nothing would yet consume it. -/
theorem hasCubeIso_of_symm_of_normalized {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) (L : X.Modules)
    (hinv : IsInvertibleSheaf L)
    (hsymm : Nonempty (modPullback ab.negSelfHom L ≅ L))
    (hzero : Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of K)))) :
    ab.HasCubeIso L :=
  sorry

/-- **AN ABELIAN VARIETY OVER A FIELD CARRIES A SYMMETRIC, NORMALIZED, AMPLE
INVERTIBLE SHEAF SATISFYING THE THEOREM OF THE CUBE** (**PROVEN 2026-07-30** over
the four leaves in the block immediately above; cut
2026-07-28 out of `exists_isAmpleSheaf_cube_of_isAlgClosed` below and out of
`Fermat.exists_cubeModel_of_abelianScheme` in `Fermat/FLT/ModularCurve/X0.lean`
— it is the SHARED geometric core of both, and after this cut it is the only
place in the development where projectivity of an abelian variety and the
theorem of the cube are asserted).

TRUE and classical: Mumford, *Abelian Varieties* §6 (the theorem of the cube,
and Application 1 for projectivity via the theta divisor); Hindry–Silverman,
*Diophantine Geometry* Theorem A.7.2.1 and B.5.1; Silverman *AEC* VIII.6.2 for
the elliptic case.  `ab.proper`, `ab.smooth` and `ab.connected` make `X` an
abelian variety over `K`, hence projective, so it carries an ample invertible
`L₀`; `L := L₀ ⊗ [−1]^* L₀` is ample and symmetric, and `Pic (Spec K) = 0`
normalizes it along the origin at no cost.

**WHY OVER A FIELD AND NOT OVER AN ARBITRARY BASE.**  The statement would be
FALSE over a general base `S`: `IsAmpleSheaf L` is ABSOLUTE ampleness on the
total space `X`, which forces `X` itself to be quasi-projective, and an abelian
scheme over an arbitrary base is not.  (Even relative ampleness would be wrong
in general — a polarization of an abelian scheme need only exist étale-locally
on the base.)  Over a field both objections vanish.  The base is left as an
arbitrary field rather than `ℚ` or an algebraically closed `K` precisely so
that the two consumers can share it.

**WHAT THE CONJUNCTS ARE FOR.**

* `IsInvertibleSheaf L` — `L` is locally free of rank one; needed to cancel
  tensor factors downstream.
* `IsAmpleSheaf L` — `X` is PROJECTIVE.  The coordinate consumer upgrades this
  to very ampleness by passing to `L^{⊗3}` (Mumford §6, Application 1), which
  the cube identity survives because it is multiplicative in `L`.
* `Nonempty (modPullback ab.negSelfHom L ≅ L)` — SYMMETRY.  Implied by
  `HasCubeIso` restricted along `(0, Q)`, but asserted separately because both
  consumers use it by name and the classical construction supplies it for free.
* `Nonempty (modPullback ab.zeroSection L ≅ modUnit _)` — NORMALIZATION along
  the origin, `e^* L ≅ 𝒪_{Spec K}`.  Free classically (`Pic (Spec K) = 0`), and
  it is what makes the `n = 0` case of `nonempty_modPullback_mulByNat_of_cube`
  true rather than false.
* `ab.HasCubeIso L` — THE THEOREM OF THE CUBE, in the two-variable form; see
  the section docstring above for why that form and not `[n]^* L ≅ L^{⊗n²}`.

**MISSING MACHINERY** — unchanged in kind by this cut, but now asserted in
exactly one place: divisors, linear systems and the cohomology of coherent
sheaves, none of which exist at this pin (`grep -rl Ample
Mathlib/AlgebraicGeometry/` is EMPTY; the check that refutes this sentence is
that grep plus `grep -rn "TheoremOfTheCube\|VeryAmple\|IsVeryAmple" Fermat/
.lake/packages/mathlib/Mathlib/ ~/cs/FLT/`).  What this project DOES have, and
a prover should start from, is `Fermat/FLT/Modularity/AmpleSheaf.lean`.

**NO LONGER A LEAF (2026-07-30).**  PROVEN over the four leaves in the block
immediately below.  Everything above is the record of the 2026-07-28 cut; read it
for what the conjuncts mean.  What the split bought: the SYMMETRIZATION and
NORMALIZATION bookkeeping — two of the five conjuncts — is now discharged
formally, and the two mathlib-scale assertions (PROJECTIVITY and THE CUBE) are
separated from each other and from the two small formal facts.  See the block
header below for the accounting. -/
theorem exists_isAmpleSheaf_symmetric_cube {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) :
    ∃ L : X.Modules, IsInvertibleSheaf L ∧ IsAmpleSheaf L ∧
      Nonempty (modPullback ab.negSelfHom L ≅ L) ∧
      Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of K))) ∧
      ab.HasCubeIso L := by
  haveI := ab.proper
  haveI : IsIso ab.negSelfHom := ab.isIso_negSelfHom
  obtain ⟨L₀, hamp₀⟩ := exists_isAmpleSheaf_of_field K ab
  have hinv₀ : IsInvertibleSheaf L₀ := isInvertibleSheaf_of_isAmpleSheaf hamp₀
  have hinvN : IsInvertibleSheaf (modPullback ab.negSelfHom L₀) :=
    isInvertibleSheaf_modPullback _ hinv₀
  have hampN : IsAmpleSheaf (modPullback ab.negSelfHom L₀) :=
    isAmpleSheaf_modPullback ab.negSelfHom hamp₀
  have hinvL : IsInvertibleSheaf (modTensor L₀ (modPullback ab.negSelfHom L₀)) :=
    isInvertibleSheaf_modTensor hinv₀ hinvN
  -- `L := L₀ ⊗ [-1]^* L₀` is symmetric because `[-1]` is an involution
  have hsymm : Nonempty (modPullback ab.negSelfHom
      (modTensor L₀ (modPullback ab.negSelfHom L₀)) ≅
        modTensor L₀ (modPullback ab.negSelfHom L₀)) := by
    obtain ⟨e1⟩ := nonempty_modPullback_modTensor ab.negSelfHom L₀
      (modPullback ab.negSelfHom L₀)
    have e2 : modPullback ab.negSelfHom (modPullback ab.negSelfHom L₀) ≅ L₀ :=
      modPullbackCompIso ab.negSelfHom ab.negSelfHom L₀ ≪≫
        modPullbackCongrIso ab.negSelfHom_comp_negSelfHom L₀ ≪≫ modPullbackIdIso L₀
    exact ⟨e1 ≪≫ modTensorMapIso (Iso.refl _) e2 ≪≫
      modTensorComm (modPullback ab.negSelfHom L₀) L₀⟩
  -- and normalized for free, because `Pic (Spec K) = 0`
  have hzero : Nonempty (modPullback ab.zeroSection
      (modTensor L₀ (modPullback ab.negSelfHom L₀)) ≅ modUnit (Spec (CommRingCat.of K))) :=
    nonempty_iso_modUnit_of_isInvertibleSheaf_of_field K _
      (isInvertibleSheaf_modPullback ab.zeroSection hinvL)
  exact ⟨modTensor L₀ (modPullback ab.negSelfHom L₀), hinvL,
    isAmpleSheaf_modTensor fK hamp₀ hampN, hsymm, hzero,
    hasCubeIso_of_symm_of_normalized K ab _ hinvL hsymm hzero⟩

/-- **`[n]^* L ≅ L^{⊗ n²}` FOLLOWS FROM THE TWO-VARIABLE CUBE** (**PROVEN
2026-07-30**, over no new leaf — see the CORRECTION at the end of this docstring;
cut 2026-07-28 out of `exists_isAmpleSheaf_cube_of_isAlgClosed` below).

TRUE over an ARBITRARY base — no field, no ampleness and no symmetry hypothesis
is needed, because the symmetric form of the cube already carries the symmetry
this uses.  The proof is the classical induction, and it is worth writing out
here because it is what makes this leaf strictly smaller than its parent:

* restrict `HasCubeIso` along `u := pullback.lift (mulByNat (n+1)) (𝟙 X)`, i.e.
  along `P ↦ ([n+1]P, P)`.  Then `σ ∘ u = [n+2]`, `δ ∘ u = [n]`, `p₁ ∘ u =
  [n+1]` and `p₂ ∘ u = 𝟙`, so the cube reads
  `[n+2]^* L ⊗ [n]^* L ≅ ([n+1]^* L)^{⊗2} ⊗ L^{⊗2}`.  (Note the indexing: the
  textbook form of this step is `[n+1]^*L ⊗ [n−1]^*L ≅ ([n]^*L)^{⊗2} ⊗ L^{⊗2}`,
  which is the same identity written with a truncated `ℕ` subtraction.  Shifting
  it by one is what keeps the Lean proof free of `Nat.sub`, and the four
  identities above are then pure Yoneda — `ab.pre_add` and `nsmul_val` — with no
  sheaf theory in them at all.)
* with `[n]^* L ≅ L^{⊗n²}` and `[n+1]^* L ≅ L^{⊗(n+1)²}` inductively, the right
  side is `L^{⊗(2(n+1)² + 2)}`, so
  `[n+2]^* L ≅ L^{⊗(2(n+1)²+2−n²)} = L^{⊗(n+2)²}`;
* base cases: `n = 0` is `hzero` (`[0] = f ≫ e`, so `[0]^* L ≅ f^* e^* L ≅ 𝒪 =
  L^{⊗0}` — this is the ONLY place `hzero` is used, and without it the leaf is
  FALSE at `n = 0`), and `n = 1` is `mulByNat_one`.

**CORRECTION (2026-07-30) — THE "WHY IT IS STILL OPEN" PARAGRAPH WAS ALREADY
STALE WHEN IT WAS WRITTEN, AND ITS OWN CHECKS REFUTE IT.**  It said the
cancellation step waits on two absent facts: `f^*(L ⊗ M) ≅ f^* L ⊗ f^* M`,
"which is itself a sorry leaf at the time of writing", and the INVERSE of an
invertible sheaf, which "does not exist in this project at all
(`grep -rn "modInv\|Picard.*inv" Fermat/`)".  Both are wrong:

* `Fermat.nonempty_modPullback_modTensor` (`Modularity/AmpleSheaf.lean`) is
  **PROVEN**, over `exists_modPullback_modTensor`;
* the inverse is `Fermat.exists_modTensor_inv`
  (`ModularCurve/RelativePicard.lean`), and the cancellation lemma built on it —
  `Fermat.nonempty_iso_of_modTensor_left` (`AmpleSheaf.lean`) — is **PROVEN**
  too.  The grep missed it because it searched for `modInv`, and the declaration
  is spelled `modTensor_inv`.

Only one thing was genuinely missing, and it was not in that list:
`isInvertibleSheaf_modPullback` (proved above), which is what makes `[k]^* L`
cancellable.  With that in hand the leaf is exactly the induction above, so it
is **PROVEN 2026-07-30** — over no new leaf at all.  The recursion step is
`nonempty_modTensor_modPullback_mulByNat_cube` immediately above, i.e. the
restriction of `HasCubeIso` along `⟨[n+1], 𝟙⟩`. -/
theorem nonempty_modPullback_mulByNat_of_cube {X T : Scheme.{u}} {q : X ⟶ T}
    (ab : AbelianSchemeStruct q) (L : X.Modules) (hinv : IsInvertibleSheaf L)
    (hzero : Nonempty (modPullback ab.zeroSection L ≅ modUnit T))
    (hcube : ab.HasCubeIso L) (n : ℕ) :
    Nonempty (modPullback (ab.mulByNat n) L ≅ modTensorPow L (n ^ 2)) := by
  obtain ⟨ez⟩ := hzero
  -- `[0] = q ≫ e`, so `[0]^* L ≅ q^*(e^* L) ≅ q^* 𝒪_T ≅ 𝒪_X = L^{⊗0}`
  have h0 : Nonempty (modPullback (ab.mulByNat 0) L ≅ modTensorPow L (0 ^ 2)) :=
    ⟨modPullbackCongrIso ab.mulByNat_zero L ≪≫
      (modPullbackCompIso q ab.zeroSection L).symm ≪≫
      modPullbackMapIso q ez ≪≫ modPullbackUnitIso q⟩
  -- `[1] = 𝟙`, and `L^{⊗1} = L ⊗ 𝒪_X`
  have h1 : Nonempty (modPullback (ab.mulByNat 1) L ≅ modTensorPow L (1 ^ 2)) :=
    ⟨modPullbackCongrIso ab.mulByNat_one L ≪≫ modPullbackIdIso L ≪≫
      (modTensorUnitLeftIso L).symm ≪≫ modTensorComm (modUnit X) L⟩
  -- two-step induction, carrying the pair `(P m, P (m+1))`
  have key : ∀ m : ℕ,
      Nonempty (modPullback (ab.mulByNat m) L ≅ modTensorPow L (m ^ 2)) ∧
        Nonempty (modPullback (ab.mulByNat (m + 1)) L ≅ modTensorPow L ((m + 1) ^ 2)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨ek⟩ := ih.1
      obtain ⟨ek1⟩ := ih.2
      obtain ⟨ec⟩ := nonempty_modTensor_modPullback_mulByNat_cube ab L hcube k
      obtain ⟨p1⟩ := nonempty_modTensorPow_mul L ((k + 1) ^ 2) 2
      obtain ⟨p2⟩ := nonempty_modTensorPow_add L ((k + 1) ^ 2 * 2) 2
      obtain ⟨p3⟩ := nonempty_modTensorPow_add L (k ^ 2) ((k + 2) ^ 2)
      have eRHS : modTensor (modTensorPow (modPullback (ab.mulByNat (k + 1)) L) 2)
            (modTensorPow L 2) ≅ modTensorPow L ((k + 1) ^ 2 * 2 + 2) :=
        modTensorMapIso (modTensorPowMapIso ek1 2 ≪≫ p1) (Iso.refl _) ≪≫ p2
      have eN : modTensor (modPullback (ab.mulByNat k) L) (modTensorPow L ((k + 2) ^ 2))
            ≅ modTensorPow L ((k + 1) ^ 2 * 2 + 2) :=
        modTensorMapIso ek (Iso.refl _) ≪≫ p3 ≪≫
          eqToIso (by rw [show k ^ 2 + (k + 2) ^ 2 = (k + 1) ^ 2 * 2 + 2 by ring])
      refine nonempty_iso_of_modTensor_left
        (isInvertibleSheaf_modPullback (ab.mulByNat k) hinv) ?_
      exact modTensorComm _ _ ≪≫ ec ≪≫ eRHS ≪≫ eN.symm
  exact (key n).1

/-- **AN ABELIAN VARIETY OVER AN ALGEBRAICALLY CLOSED FIELD CARRIES A SYMMETRIC
AMPLE INVERTIBLE SHEAF SATISFYING THE CUBE IDENTITY `[n]^* L ≅ L^{⊗ n²}`**

**NO LONGER A LEAF (2026-07-28).**  It is now PROVEN over the two leaves
immediately above — `exists_isAmpleSheaf_symmetric_cube`, which supplies the
symmetric normalized ample `L` together with the theorem of the cube in its
two-variable form, and `nonempty_modPullback_mulByNat_of_cube`, which is the
classical induction turning that into `[n]^* L ≅ L^{⊗ n²}`.  Neither the
algebraic closedness of `K` nor `n` is used by the first of those, which is
precisely why the cut is worth making: the SAME sheaf statement is the input
of `Fermat.exists_cubeModel_of_abelianScheme` over `ℚ`
(`Fermat/FLT/ModularCurve/X0.lean`), and before this cut the two consumers were
each asserting the whole of Mumford §6 privately.  Everything from here down is
the record of the 2026-07-27 cut; read it for what the conjuncts mean, not for
the current state.

(sorry leaf, cut 2026-07-27 — this is Mumford *Abelian Varieties* §6,
Application 2 of the THEOREM OF THE CUBE, together with the projectivity of an
abelian variety, and it is the whole mathematical residue of
`isQuasiAffine_ker_mulByNat_of_isAlgClosed` below).

**What each conjunct is.**

* `IsInvertibleSheaf L` — `L` is locally free of rank one.
* `IsAmpleSheaf L` — `A` is PROJECTIVE.  Classically this is the theta
  divisor: a symmetric ample `L` exists on any abelian variety over an
  algebraically closed field.
* `modPullback ab.zeroSection L ≅ modUnit _` — `L` is NORMALIZED along the
  origin, `e^* L ≅ 𝒪_{Spec K}`.  This is free classically (`Pic(Spec K) = 0`
  for a field `K`), and it is folded into this leaf rather than made a seventh
  one because the classical construction produces a normalized `L` anyway.
  The consumer uses it to identify `([p]^* L)|_{ker[p]}` with `𝒪`.
* `modPullback (ab.mulByNat n) L ≅ modTensorPow L (n ^ 2)` — THE CUBE, in the
  form Application 2 uses.  Note this form REQUIRES `L` symmetric: for a
  general `L` the cube only gives
  `[n]^* L ≅ L^{(n²+n)/2} ⊗ ([−1]^* L)^{(n²−n)/2}`.  Symmetry is therefore
  asserted implicitly, by asserting the conclusion it buys; a prover
  constructs `L := L₀ ⊗ [−1]^* L₀` from any ample `L₀`, which is symmetric and
  still ample.

**Why the statement is expressible at all** — and this is the change that made
the cut available on 2026-07-27.  `Fermat.modTensor`
(`ModularCurve/RelativePicard.lean`) is the object part of the tensor product
of sheaves of modules, obtained by SHEAFIFYING the presheaf tensor product;
`Fermat.modTensorPow`, `Fermat.IsAmpleSheaf` and the six sheaf-theoretic
obligations live in `Modularity/AmpleSheaf.lean`.  Before that landed, the
consumer's docstring recorded — correctly for mathlib, and incorrectly for
this project after the fact — that `L^{⊗n}` "cannot even be WRITTEN".

**`n` is arbitrary and no characteristic hypothesis appears.**  The cube is
characteristic-blind; the consumer instantiates it at `n = p = ringChar K`.
Do not add `hp`/`hchar` here — they would record a dependence that does not
exist, and the Lie-algebra route's inability to reach `n = p` is a fact about
the CONSUMER, not about this statement.

**Do not attempt this leaf before reading
`isQuasiAffine_ker_mulByNat_of_field_char` below**: nine cube-free routes are
refuted there, each with the check that would refute the refutation, and the
survey of what `Mathlib/AlgebraicGeometry/` does and does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY) is re-verified there.
This is a mathlib-scale build: theta divisors need divisors, linear systems
and cohomology, none of which exist at this pin. -/
theorem exists_isAmpleSheaf_cube_of_isAlgClosed {X : Scheme.{u}}
    (K : Type u) [Field K] [IsAlgClosed K] {fK : X ⟶ Spec (CommRingCat.of K)}
    (ab : AbelianSchemeStruct fK) (n : ℕ) :
    ∃ L : X.Modules, IsInvertibleSheaf L ∧ IsAmpleSheaf L ∧
      Nonempty (modPullback ab.zeroSection L ≅ modUnit (Spec (CommRingCat.of K))) ∧
      Nonempty (modPullback (ab.mulByNat n) L ≅ modTensorPow L (n ^ 2)) := by
  obtain ⟨L, hinv, hamp, _hsym, hzero, hcube⟩ := exists_isAmpleSheaf_symmetric_cube K ab
  exact ⟨L, hinv, hamp, hzero, nonempty_modPullback_mulByNat_of_cube ab L hinv hzero hcube n⟩

/-- **`ker[p]` is a QUASI-AFFINE SCHEME over an ALGEBRAICALLY CLOSED field of
characteristic `p`** (PROVEN 2026-07-27 over
`exists_isAmpleSheaf_cube_of_isAlgClosed` above and the six sheaf-theoretic
leaves of `Modularity/AmpleSheaf.lean`; cut 2026-07-27 out of
`isQuasiAffine_ker_mulByNat_of_field_char` below by ROUTE 9, "WLOG `K`
algebraically closed", which that leaf's docstring had recorded as the axis
nobody had ranged over).

**WHAT THIS CUT IS AND IS NOT.**  It is NOT another change of shape — two of
those have already been made in this chain and a third would buy nothing (see
the consumer's CORRECTION 3).  It is a strengthening of the HYPOTHESES: this
leaf may assume `[IsAlgClosed K]`, and the descent from it to arbitrary `K` is
now PROVEN below.  What that buys is that every classical proof of the residue
is written over an algebraically closed field, and two of them become
*expressible* only here:

* Mumford *Abelian Varieties* §6, Application 2 of the theorem of the cube (the
  symmetric ample `L`, `[n]^*L ≅ L^{n²}`, `(L|_Z)^{p²} ≅ 𝒪_Z`) — projectivity of
  `A` via the theta divisor is an algebraically-closed-field statement;
* refuted route 7's reduction to `B = ((ker[p])_red)⁰`, a positive-dimensional
  abelian variety killed by `p`: `_red` and the identity component behave as the
  classical argument expects only over a perfect — here algebraically closed —
  field.

**THIS DECLARATION IS NO LONGER A LEAF (2026-07-27, second revision).**  It is
now PROVEN over Mumford's Application 2 itself, stated as
`exists_isAmpleSheaf_cube_of_isAlgClosed` immediately above plus six
sheaf-theoretic leaves in `Modularity/AmpleSheaf.lean`.  Everything from here
down is the history of how it got here; read it for the refuted routes, not
for the current state.

**THE RECORDED BLOCKER WAS HALF-FALSE, AND THE CHECK THAT REFUTED IT IS ONE
GREP.**  The paragraph that used to stand here said the blocker "is UNCHANGED
and is the thing to attack: at this pin there is **no monoidal structure on
`SheafOfModules`**, so `L^{⊗n}` cannot be written at all".  The first half is
right about mathlib and WRONG about this project: `Fermat.modTensor`
(`ModularCurve/RelativePicard.lean`, landed 2026-07-27) supplies the object
part by sheafifying the presheaf tensor product, and with `Fermat.modPullback`
and `Fermat.IsInvertibleSheaf` beside it, `L^{⊗n}` (`Fermat.modTensorPow`) and
the cube's output `[n]^* L ≅ L^{⊗ n²}` are both WRITABLE — verified by
elaborating them, 2026-07-27.  Ampleness was the one statement-level gap that
really did remain; `Fermat.IsAmpleSheaf` closes it.

So the standing rule applied here in the direction the old note denied: the cut
needed the ample-sheaf theory only STATED, not proven.  What is NOT disputed is
the old note's conclusion that PROVING it is a theory build — the six leaves in
`AmpleSheaf.lean` are that theory, and each says what it is waiting on.

Still true, and still worth obeying: do not re-cut this statement into
`IsAffine` / `Finite` / `topologicalKrullDim ≤ 0`, all of which are
interchangeable with it here.

**Routes already refuted for the general-`K` form apply verbatim here**, with
one exception worth naming: route 5 (quasi-finiteness at the origin, spread by
translations) was refuted partly because "the translations are not `K`-morphisms
at non-rational points", and over an algebraically closed field they ARE.  That
does not revive it — the hard part was always quasi-finiteness AT the origin,
where `ker F ⊆ ker[p]` is infinitesimal with `Lie(ker[p]) = Lie(A)` of full
dimension `g` — but a successor should know the objection has changed shape.

See `isQuasiAffine_ker_mulByNat_of_field_char` below for the full survey: the
classical proof in the order that produces `IsQuasiAffine`, the re-verified
account of what mathlib does and does not have, and nine refuted routes each
with the check that would refute the refutation. -/
theorem isQuasiAffine_ker_mulByNat_of_isAlgClosed {X : Scheme.{u}}
    (K : Type u) [Field K] [IsAlgClosed K] {fK : X ⟶ Spec (CommRingCat.of K)}
    (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (_hchar : ringChar K = p) :
    Scheme.IsQuasiAffine (pullback (ab.mulByNat p) ab.zeroSection) := by
  classical
  -- 1.  `ker[p] ↪ A` is a CLOSED IMMERSION: it is a base change of the zero
  --     section, which is a section of the separated `fK`.
  haveI : IsProper fK := ab.proper
  haveI : IsClosedImmersion ab.zeroSection := by
    haveI : IsClosedImmersion (ab.zeroSection ≫ fK) := by
      rw [show ab.zeroSection ≫ fK = 𝟙 _ from (ab.zero (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp _ fK
  haveI : IsClosedImmersion (pullback.fst (ab.mulByNat p) ab.zeroSection) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  -- 2.  `ker[p]` is QUASI-COMPACT: `ker[p] ⟶ Spec K` is a base change of the
  --     proper `[p]`, and `Spec K` is compact.
  haveI : IsProper (ab.mulByNat p) := ab.isProper_mulByNat p
  haveI : IsProper (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : CompactSpace ↥(pullback (ab.mulByNat p) ab.zeroSection : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (ab.mulByNat p) ab.zeroSection)
  -- 3.  Mumford §6, Application 2: a normalized symmetric ample `L` with the cube.
  obtain ⟨L, -, hLamp, ⟨htriv⟩, ⟨hcube⟩⟩ :=
    exists_isAmpleSheaf_cube_of_isAlgClosed K ab p
  set ι : (pullback (ab.mulByNat p) ab.zeroSection : Scheme.{u}) ⟶ X :=
    pullback.fst (ab.mulByNat p) ab.zeroSection with hι
  set st : (pullback (ab.mulByNat p) ab.zeroSection : Scheme.{u}) ⟶
      Spec (CommRingCat.of K) := pullback.snd (ab.mulByNat p) ab.zeroSection with hst
  obtain ⟨etens⟩ := nonempty_modPullback_modTensorPow ι L (p ^ 2)
  obtain ⟨eunit⟩ := nonempty_modPullback_modUnit st
  -- 4.  `[p]` is CONSTANT on `ker[p]` — that is `pullback.condition` — so
  --     `(L|_{ker[p]})^{⊗ p²} ≅ ([p]^* L)|_{ker[p]} ≅ (str)^* (e^* L) ≅ 𝒪`.
  have e : modTensorPow (modPullback ι L) (p ^ 2) ≅
      modUnit (pullback (ab.mulByNat p) ab.zeroSection) :=
    etens.symm ≪≫
      modPullbackMapIso ι hcube.symm ≪≫
      modPullbackCompIso ι (ab.mulByNat p) L ≪≫
      modPullbackCongrIso pullback.condition L ≪≫
      (modPullbackCompIso st ab.zeroSection L).symm ≪≫
      modPullbackMapIso st htriv ≪≫
      eunit
  -- 5.  `L|_{ker[p]}` is ample, hence so is its `p²`-th power, hence so is
  --     `𝒪_{ker[p]}` — and a scheme with ample structure sheaf is QUASI-AFFINE.
  exact isQuasiAffine_of_isAmpleSheaf_modUnit _
    (isAmpleSheaf_of_iso e (isAmpleSheaf_modTensorPow (pow_pos hp.pos 2)
      (isAmpleSheaf_modPullback ι hLamp)))

/-- **`ker[p]` is a QUASI-AFFINE SCHEME in characteristic `p`** (PROVEN
2026-07-27 over `isQuasiAffine_ker_mulByNat_of_isAlgClosed` above, by ROUTE 9 —
"WLOG the base field is algebraically closed"; it used to be the sorry itself,
cut 2026-07-27 out of
`isAffine_ker_mulByNat_of_field_char`, which is now PROVEN over it through the
bridge `isAffine_of_isQuasiAffine_of_universallyClosed` immediately above).

**THIS DECLARATION IS NO LONGER A LEAF.**  Route 9 below was taken on
2026-07-27 and it closes this statement over an arbitrary field, reducing it to
`isQuasiAffine_ker_mulByNat_of_isAlgClosed` above.  The survey that follows is
kept HERE, in one place, because it is about the residue, which is unchanged:
everything below still describes what the algebraically-closed leaf owes.

**HONESTY FIRST: the two earlier cuts were a CHANGE OF SHAPE, NOT a reduction of
content.**  For a scheme proper over a field, *quasi-affine*, *affine* and
*finite* are all equivalent, and both equivalences are PROVEN here — so a prover
at this leaf owes neither more nor less than a prover owed at
`finite_preimage_mulByNat_of_field_char` two cuts ago.  Nobody should report
those cuts as progress on the mathematics.  What they buy, and the
only reason they were made:

* the residue is a property of the SCHEME `ker[p]` alone — no morphism
  bookkeeping, no `∀ s : Spec K` packaging, no Zariski's-main-theorem step;
* and it is *exactly* where the classical argument stops.  The ample-line-bundle
  proof does not produce "the point set is finite" and does not produce
  "affine": it produces "`𝒪_Z` is ample, hence `Z` is quasi-affine"
  (EGA II 5.1.2).  Everything after that is the bridge above, and the bridge is
  no longer owed to anybody.

**The bridges, both PROVEN.**  quasi-affine ⟹ affine is
`isAffine_of_isQuasiAffine_of_universallyClosed` above (`ker[p] ⟶ Spec K` is
proper as a base change of `[p]`, `isProper_mulByNat`).  affine ⟹ finite fibre
is `finite_ker_mulByNat_of_field_char` below (`IsAffineHom` is then free since
`Spec K` is affine, so `IsFinite.iff_isProper_and_isAffineHom` gives a FINITE
morphism and `Scheme.Hom.finite_preimage_singleton` reads off the fibre).

**The classical proof, in the order that produces `IsQuasiAffine`.**  Mumford
*Abelian Varieties* §6, Application 2 of the theorem of the cube:

1. `A` carries a symmetric AMPLE invertible sheaf `L` (`A` is projective — a
   theorem, via the theta divisor).
2. The cube gives `[n]^* L ≅ L^{n²}`.
3. `[p]` is constant on `Z = ker[p]` (it factors through the zero section), so
   `([p]^* L)|_Z ≅ 𝒪_Z`; with 2, `(L|_Z)^{p²} ≅ 𝒪_Z`.
4. `L|_Z` is ample (restriction of an ample sheaf to a closed subscheme), hence
   so is `(L|_Z)^{p²} ≅ 𝒪_Z`; and a scheme whose structure sheaf is ample is
   QUASI-AFFINE.  That is this leaf, and it is where the classical argument
   ends.

The second classical route, `[p] = V ∘ F`, produces finiteness rather than
quasi-affineness and needs the Verschiebung, hence `Pic⁰` and the dual abelian
variety.

**MISSING MACHINERY at this pin — every claim re-run 2026-07-27 against this
worktree's own `.lake/packages/mathlib`.  THE PREVIOUS VERSION OF THIS SURVEY
WAS WRONG ON TWO COUNTS; both corrections are recorded first.**

*Correction 1: mathlib DOES have quasi-affine schemes.*
`Mathlib/AlgebraicGeometry/QuasiAffine.lean` defines `Scheme.IsQuasiAffine`
(quasi-compact + `X.toSpecΓ` an immersion, which it proves is then an OPEN
immersion) with `IsQuasiAffine.of_forall_exists_mem_basicOpen`,
`.of_isAffineHom`, `.of_isImmersion` and `.isBasis_basicOpen`.  That is the
target type of EGA II 5.1.2, and the earlier survey never mentioned it — which
is why the leaf used to be stated one step too late.

*Correction 2: mathlib DOES have zero-dimensionality ⟹ affine, topologically.*
`Mathlib/AlgebraicGeometry/Artinian.lean` has
`IsLocallyArtinian.of_topologicalKrullDim_le_zero`,
`IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology`,
`IsLocallyArtinian.discreteTopology` and `IsArtinianScheme.finite`.  So
`topologicalKrullDim (ker[p]) ≤ 0` is an equally valid shape for this leaf.  It
was not chosen because it is *further* from what the cube outputs, not because
it is unavailable.  Also present and useful to a prover:
`isIntegral_appTop_of_universallyClosed` (`Γ(Z, 𝒪)` is integral over `K`) and
`isField_of_universallyClosed`, both in `Morphisms/Proper.lean`.

*Still genuinely absent, each refutable by one grep in
`.lake/packages/mathlib`:*
`grep -rl Ample Mathlib/AlgebraicGeometry/` → EMPTY (mathlib's only `Ample` is
`Analysis/Convex/AmpleSet.lean`).  `grep -rli picard Mathlib/AlgebraicGeometry/`
→ only `EllipticCurve/Weierstrass.lean`.
`grep -rliE "line bundle|invertible sheaf" Mathlib/AlgebraicGeometry/` → EMPTY,
and `Mathlib/AlgebraicGeometry/Modules/` is `Presheaf.lean`, `Sheaf.lean`,
`Tilde.lean` only — there is no invertible-sheaf theory to build `Pic` on.
`grep -rli theoremOfTheCube Mathlib/` → EMPTY.
`grep -rli frobenius Mathlib/AlgebraicGeometry/` → EMPTY.
`grep -rl CohenMacaulay Mathlib/` → EMPTY.
`Mathlib/AlgebraicGeometry/AlgebraicCycle/` exists but is `Basic.lean` alone —
cycles, no intersection numbers and no positivity.
`Mathlib/AlgebraicGeometry/Group/` is `Abelian.lean` + `Smooth.lean` only.
`~/cs/FLT`'s only `Ample`/`Picard` hits are `import Mathlib.RingTheory.PicardGroup`.
**Re-run these before believing the paragraph**; a hit on any of them means the
leaf may be far cheaper than it looks.

**ROUTES SEARCHED AND REFUTED, each with the check that would refute the
refutation** (1–5 recorded 2026-07-27 over the axis *everything cube-free that
is expressible at this pin*; 6–8 added later the same day over two axes the
first sweep did not range over — *dimension counting that does not need
dominance*, and *whether the leaf is needed by its consumers at all*).

1. *Dimension count* — "all fibres of `[p]` are translates of `ker[p]`
   (the shearing above proves exactly this, schematically), so
   `dim A = dim [p](A) + dim ker[p]`; if `[p]` is dominant then
   `dim ker[p] = 0`."  Blocked TWICE: mathlib has no fibre-dimension theorem
   for schemes (`grep -rn "fiber.*dimension\|dim.*fiber" Mathlib/AlgebraicGeometry/`
   → EMPTY), and *dominance of `[p]` is not available here* — in this file
   surjectivity of `[n]` is derived FROM finite fibres
   (`flat_of_finite_fibres_endo` → `flat_mulByNat` → `universallyOpen_mulByNat`
   → `surjective_mulByNat`), so using it would be circular.  Refute by
   exhibiting a cube-free proof that `[p]` is dominant.
2. *Lie algebra*, the sibling's route: `d[p] = p · id = 0` in characteristic
   `p`.  Refute by finding any other differential-geometric invariant that
   separates — note `ker[p] ⊇ ker F` is infinitesimal with
   `Lie(ker[p]) = Lie(A)`, so the tangent space at the origin has FULL
   dimension `g` and no smoothness data can bound `dim ker[p]`.  This is the
   structural reason the leaf is hard, not an accident of the write-up.
3. *Leverage the prime-to-`p` sibling.*  For `ℓ` prime to `p`, `[ℓ]` restricts
   to an AUTOMORPHISM of `ker[p]` (choose `ℓ'` with `ℓℓ' ≡ 1 mod p`; then
   `[ℓ'] ∘ [ℓ] = [1 + p·m] = id` on `ker[p]`), so it carries no dimension
   information about `ker[p]`.  Dually, `[p](A)` contains `A[ℓⁿ]` for every
   `ℓ ≠ p` — but concluding `[p](A) = A` from that needs the prime-to-`p`
   torsion to be dense, i.e. `#A[ℓ] = ℓ^{2g}`, i.e. degree theory, which does
   not exist here either.  Refute by producing that density cube-free.
4. *Specialize to dimension 1* and use this project's division polynomials.
   Refuted by the consumers: `AbelianSchemeStruct` is instantiated in
   `Fermat/FLT/ModularCurve/X0.lean` at the JACOBIAN of a modular curve, so
   `g > 1` is genuinely needed.  Refute by showing every consumer is an
   elliptic curve.
5. *Quasi-finiteness at the origin, spread by `isOpen_quasiFiniteAt`* —
   refuted before dispatch: openness alone does not propagate the locus off the
   origin, and the translations that would do it are not `K`-morphisms at
   non-rational points.
6. *Dimension counting WITHOUT dominance, via the shearing isomorphism.*  Route
   1 was refuted partly because `[p]` is not known to be dominant — but the
   shearing does not need dominance: it identifies the fibre product
   `A ×_{[p], [p]} A` with `A × ker[p]`, so `dim A + dim ker[p]` is computed
   with no reference to the image of `[p]`.  The route dies one step later
   instead: the only upper bound available for that fibre product is the closed
   immersion `A ×_{[p]} A ↪ A × A` (`A` is separated), giving
   `dim A + dim ker[p] ≤ 2 dim A`, i.e. `dim ker[p] ≤ g` — TRUE and vacuous.
   Refute by producing any upper bound for `dim (A ×_{[p]} A)` better than the
   diagonal-based one.
7. *Reduce to a smooth connected subgroup and contradict `[p] = 0` there.*
   Over `K̄`, if `dim ker[p] > 0` then `((ker[p])_red)⁰` is a positive-dimensional
   ABELIAN VARIETY `B` with `[p]|_B = 0`, so the leaf reduces to "no
   positive-dimensional abelian variety is killed by `p`".  Every way of
   contradicting that goes back through degrees or duality: `B(K̄)` is
   `ℓ`-divisible for every `ℓ ≠ p` (the prime-to-`p` sibling gives that) and
   killed by `p`, which is perfectly consistent as an abstract group — an
   infinite `𝔽_p`-vector space is uniquely `ℓ`-divisible — so the contradiction
   needs either `deg[p] = p^{2g} ≠ 1` (the cube) or `V` dual to `F` with `F`
   faithfully flat (duality).  Refute by contradicting "`B` is an abelian
   variety of positive dimension with `pB = 0`" using neither degrees nor
   duality.
8. *Avoid the leaf entirely by restricting to characteristic zero.*  Refuted by
   the consumers, and this is the one axis the first sweep did not range over at
   all: `locallyQuasiFinite_mulByNat`'s assembly below instantiates
   `finite_preimage_mulByNat_of_field` at `S.residueField (f a)` for an
   ARBITRARY point of an arbitrary base scheme `S`, so residue characteristic
   `p > 0` is genuinely in scope even when the generic fibre is over a number
   field.  Refute by
   `grep -n "finite_preimage_mulByNat_of_field (S.residueField" ` in this file
   and showing every consumer's base has characteristic zero residue fields.

**AN ALTERNATIVE CUT, recorded but NOT taken.**  The shearing makes
"`ker[p]` is finite" equivalent to the weaker-*looking*
`∃ x : A, (⇑([p]) ⁻¹' {[p] x}).Finite` — ONE finite fibre anywhere suffices.
`kerShear_kerUnshear` above is one of the two round trips; the other,
`(u,k) ↦ (u,u+k) ↦ (u,k)`, is provable by the same `pre_add` computation, and
together they make `kerShear` an isomorphism, after which a fibre transports
along a base change to `κ(x)` (quasi-finiteness being stable under base change).
It was not taken because the only cube-free way to *produce* one finite fibre is
a generic-point argument, which needs precisely the fibre-dimension theory
refuted in 1 — so the existential form would be more attackable in appearance
only.  A prover who first builds fibre dimension should take this cut instead.

**CORRECTION 3 (2026-07-27): the whole equivalence loop is FREE at this pin, and
the survey above missed the one lemma that makes it so.**
`Mathlib/AlgebraicGeometry/Limits.lean:699` carries
`instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X` — a
scheme with finite discrete underlying space is AFFINE.  Together with
`IsArtinianScheme.finite` and `IsLocallyArtinian.discreteTopology` (both in
`Artinian.lean`) that closes the circle: `topologicalKrullDim ≤ 0` ⟹
`IsLocallyArtinian` ⟹ discrete, and with `CompactSpace` ⟹ `Finite` ⟹ `IsAffine`
⟹ `IsQuasiAffine`.  So the ARTINIAN ROUTE IS STRICTLY CHEAPER as a bridge: it
needs no hand-written EGA step at all, where the (correct, and worth keeping)
`isAffine_of_isQuasiAffine_of_universallyClosed` above had to be proved by hand.
Consequence for a prover: all of {`𝒪_Z` ample, `IsQuasiAffine`, `IsAffine`,
`Finite`, `DiscreteTopology`, `topologicalKrullDim ≤ 0`} are interchangeable for
this `Z`, so prove whichever your argument produces — and do NOT spend a cycle
re-cutting the leaf into another of them.  Two shape changes have already been
made here; a third would buy nothing.  Refute by exhibiting a member of that
list that does not reach the others.

**⚠ THE PARAGRAPH THAT FOLLOWS IS SUPERSEDED — ITS FIRST HALF IS FALSE OF THIS
PROJECT, AND THE REFUTING CHECK IS ONE GREP** (2026-07-27, re-verified by the
sweep over every citation of this blocker).  It is kept verbatim because its
*second* half — that PROVING the ample-sheaf theory is a theory build — is
correct and still governs, and because it is the text every other citation
inherited.  What is wrong with it, precisely:

* "there is no monoidal structure on sheaves of modules over a scheme" is TRUE
  OF MATHLIB (`grep -rn 'MonoidalCategory\|tensorObj'
  Mathlib/Algebra/Category/ModuleCat/Sheaf/` is still EMPTY at this pin —
  re-run 2026-07-27) and FALSE OF THIS PROJECT: `Fermat.modTensor`
  (`ModularCurve/RelativePicard.lean`) is the OBJECT part of `⊗`, obtained by
  sheafifying the presheaf tensor product.
* "so `L^{⊗n}` cannot even be WRITTEN" is therefore false as an inference:
  `Fermat.modTensorPow`, `Fermat.IsAmpleSheaf` and the cube's output
  `[n]^*L ≅ L^{⊗n²}` all elaborate (`Modularity/AmpleSheaf.lean`,
  `exists_isAmpleSheaf_cube_of_isAlgClosed` above).
* Hence the standing rule "does the cut need `T` PROVEN or only STATED?"
  resolves the OPPOSITE way from the paragraph's verdict: only STATED, and the
  cut was taken — `isQuasiAffine_ker_mulByNat_of_isAlgClosed` above is now
  PROVEN over six named sheaf-theoretic leaves, none carrying abelian-variety
  content.
* An OBJECT part is all a STATEMENT needs; what the paragraph correctly
  identifies is the cost of the MORPHISM part, the associator and the unitor —
  i.e. the obligations now named one by one on the six leaves in
  `Modularity/AmpleSheaf.lean`.

**Why "ample line bundles are absent" UNDERSTATES the blocker, and why this leaf
is NOT of the "state the interface and cut" kind** (2026-07-27, SUPERSEDED —
see the correction immediately above).  The survey
above is right that `Ample`, `Pic` and invertible sheaves are missing, but the
operative fact is stronger and it is what decides feasibility: **there is no
monoidal structure on sheaves of modules over a scheme, so `L^{⊗n}` cannot even
be WRITTEN.**  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` builds
`MonoidalCategoryStruct (PresheafOfModules …)` and it is never transported to
sheaves: `grep -rn 'MonoidalCategory\|tensorObj'
Mathlib/Algebra/Category/ModuleCat/Sheaf/` is EMPTY, and that directory's
`LocallyFree.lean` supplies `IsLocallyFree` with no rank and no tensor product
(`grep -n 'rank\|Rank'` there is EMPTY too).  This matters because the standing
rule "an audit saying *atomic until theory T exists* must be asked whether the
cut needs T PROVEN or only STATED" resolves here in the unusual direction: every
step of Mumford's Application 2 puts `L`, `L^{p²}` and `𝒪_Z` in ONE equation, so
stating the interface faithfully means defining tensor powers of invertible
sheaves — a mathlib-scale build (monoidal `SheafOfModules`, then invertibility,
then ampleness), not a task-scale one.  Refute by exhibiting a faithful
sheaf-FREE encoding of "`L` is ample and `L^{p²} ≅ 𝒪_Z`", or by finding a tensor
product of sheaves of modules at this pin.

**ROUTE 9 — BASE CHANGE, "WLOG `K` ALGEBRAICALLY CLOSED" — WAS TAKEN ON
2026-07-27 AND IS THE PROOF OF THIS DECLARATION.**  It was found by the sweep
that first ranged over the base-change axis, then blocked for a day by a defect
in this family's own signatures, then unblocked by the repair recorded below.
Everything from here to the end of this docstring is the history of that route;
what it leaves open is `isQuasiAffine_ker_mulByNat_of_isAlgClosed` above.

Every classical route (Mumford §6, and refuted route 7's reduction to
`((ker[p])_red)⁰`) is written over an ALGEBRAICALLY CLOSED field, so the missing
step is "WLOG `K` algebraically closed".  That reduction is otherwise entirely
available and needs no new theory: `AbelianSchemeStruct.baseChange` and
`baseChange_mulByNat` already exist above, `ker[p]` of a base change is the base
change of `ker[p]` (pullback pasting), `Surjective` is stable under base change
(`Mathlib/AlgebraicGeometry/PullbackCarrier.lean:431`), and the descent re-enters
through declarations already in this file — `IsQuasiAffine` over `K̄` gives
`IsAffine` (the bridge above) gives `IsFinite` gives a finite point set, which
transports along the surjection into
`isFinite_ker_mulByNat_of_finite_preimage`.

What USED TO block it is that **`Spec K` was not known to be a ONE-POINT scheme
here**, so `Spec K̄ ⟶ Spec K` was not known to be surjective.  The old binder
`(K : CommRingCat.{u}) [Field K]` put a `Field` structure on the CARRIER `↑K`
that Lean could not connect to `K`'s own `CommRing` instance, and at this pin
the two are genuinely independent: under that binder, `Subsingleton ↥(Spec K)`
and `Unique ↥(Spec K)` both FAILED to synthesize while `Nonempty ↥(Spec K)`
succeeded — whereas all three succeed for `Spec (CommRingCat.of F)` with
`(F : Type u) [Field F]` and for `Spec (S.residueField s)`, which is how
`locallyQuasiFinite_mulByNat` below actually instantiates this family.  So
`hchar : ringChar K = p` constrained a field structure that need not be the one
`Spec K` was built from, and as written the leaf asked for `ker[p]` over a base
not known to be a field at all.

**THAT DEFECT IS REPAIRED (2026-07-27), AND ROUTE 9 IS THEREFORE OPEN.**  The
whole `_of_field` / `_of_field_char` family — this leaf,
`isAffine_ker_mulByNat_of_field_char`, `finite_ker_mulByNat_of_field_char`,
`isFinite_ker_mulByNat_of_field_char`, `finite_preimage_mulByNat_of_field_char`,
`finite_preimage_mulByNat_of_field` and eight more — was converted in ONE commit
from `(K : CommRingCat.{u}) [Field K]` to `(K : Type u) [Field K]` with base
`Spec (CommRingCat.of K)`.  No proof body changed.  `Subsingleton` and `Unique`
on `↥(Spec (CommRingCat.of K))` now synthesize, `hchar` now constrains the
actual base, and **route 9 goes through exactly as described above**, leaving
this leaf as "the cube over an ALGEBRAICALLY CLOSED field".

**AND IT WENT THROUGH EXACTLY AS PREDICTED, IN FOUR STEPS** (2026-07-27; the
whole descent is ~35 lines and needed exactly two new general lemmas, both
recorded above and both free of abelian-variety content):

1. `K̄ := AlgebraicClosure K` inherits the characteristic
   (`charP_of_injective_algebraMap`), and `g : Spec K̄ ⟶ Spec K` is SURJECTIVE
   for free — mathlib's low-priority instance `[Nonempty X] [Subsingleton Y]`
   fires because both spectra are one-point.  *This is the step the old
   `(K : CommRingCat.{u})` binder made impossible*, and it is the whole content
   of the repair below.
2. `ab.baseChange g` is an abelian scheme over `Spec K̄`, and
   `isPullback_ker_baseChange` (proved above, by two pastings) says its `ker[p]`
   is the base change of `ker[p]` along `g`.
3. So `φ : ker[p]_{K̄} ⟶ ker[p]_K` is surjective
   (`MorphismProperty.IsStableUnderBaseChange.of_isPullback` for `@Surjective`),
   while the leaf over `K̄` makes the source AFFINE
   (`isAffine_of_isQuasiAffine_of_universallyClosed`), hence FINITE over
   `Spec K̄` (`IsFinite.iff_isProper_and_isAffineHom`), hence a FINITE POINT SET
   (`Scheme.Hom.finite_preimage_singleton`, and `Spec K̄` is one point).
4. A surjective image of a finite set is finite, so every fibre of
   `ker[p]_K ⟶ Spec K` is finite; `isFinite_ker_mulByNat_of_finite_preimage`
   turns that into `IsFinite`, `isAffine_of_isAffineHom` into `IsAffine`, and
   mathlib's `[IsAffine X] : X.IsQuasiAffine` closes the goal.

Note step 4 re-enters the ZMT bridge rather than the affine one: the affine
bridge `isAffine_ker_mulByNat_of_field_char` sits BELOW this declaration and
consumes it, so using it here would be circular.

**`hp` and `hchar` are deliberately carried even though the statement is true
without them** (`ker[n]` is quasi-affine for every `n ≠ 0`): without them this
leaf would silently duplicate the content the prime-to-characteristic sibling
needs.  Carrying them records that this is exactly the residue the Lie-algebra
route cannot reach. -/
theorem isQuasiAffine_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    Scheme.IsQuasiAffine (pullback (ab.mulByNat p) ab.zeroSection) := by
  classical
  -- 1.  the algebraic closure, its characteristic, and the surjection of spectra
  haveI : CharP K p := hchar ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hchar' : ringChar (AlgebraicClosure K) = p := ringChar.eq (AlgebraicClosure K) p
  set g : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  -- 2.  the leaf over `K̄`, and the chain quasi-affine ⟹ affine ⟹ finite morphism
  haveI := isQuasiAffine_ker_mulByNat_of_isAlgClosed (AlgebraicClosure K)
    (ab.baseChange g) p hp hchar'
  haveI : IsProper ((ab.baseChange g).mulByNat p) := (ab.baseChange g).isProper_mulByNat p
  haveI : IsAffine (pullback ((ab.baseChange g).mulByNat p) (ab.baseChange g).zeroSection) :=
    isAffine_of_isQuasiAffine_of_universallyClosed
      (pullback.snd ((ab.baseChange g).mulByNat p) (ab.baseChange g).zeroSection)
  haveI : IsFinite (pullback.snd ((ab.baseChange g).mulByNat p)
      (ab.baseChange g).zeroSection) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  -- 3.  `ker[p]` over `K̄` is the base change of `ker[p]` over `K`, along a surjection
  set φ := pullback.map ((ab.baseChange g).mulByNat p) (ab.baseChange g).zeroSection
      (ab.mulByNat p) ab.zeroSection (pullback.fst fK g) g (pullback.fst fK g)
      (ab.baseChange_mulByNat g p) (ab.baseChange_zeroSection g) with hφdef
  have hsq : IsPullback φ
      (pullback.snd ((ab.baseChange g).mulByNat p) (ab.baseChange g).zeroSection)
      (pullback.snd (ab.mulByNat p) ab.zeroSection) g := ab.isPullback_ker_baseChange g p
  haveI : Surjective φ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hsq.flip
      inferInstance
  -- 4.  a finite point set upstairs, pushed down the surjection, and back in through ZMT
  have huniv' : (Set.univ : Set ↥(pullback ((ab.baseChange g).mulByNat p)
      (ab.baseChange g).zeroSection)).Finite := by
    refine Set.Finite.subset (Scheme.Hom.finite_preimage_singleton
      (pullback.snd ((ab.baseChange g).mulByNat p) (ab.baseChange g).zeroSection)
      (default : ↥(Spec (CommRingCat.of (AlgebraicClosure K))))) ?_
    intro x _
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subsingleton.elim _ _
  have hfinK : ∀ s : ↥(Spec (CommRingCat.of K)),
      (⇑(pullback.snd (ab.mulByNat p) ab.zeroSection) ⁻¹' {s}).Finite := by
    intro s
    refine Set.Finite.subset (huniv'.image ⇑φ) ?_
    intro x _
    obtain ⟨y, hy⟩ := Scheme.Hom.surjective φ x
    exact ⟨y, Set.mem_univ y, hy⟩
  haveI : IsFinite (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
    AbelianSchemeStruct.isFinite_ker_mulByNat_of_finite_preimage ab p hfinK
  haveI : IsAffine (pullback (ab.mulByNat p) ab.zeroSection) :=
    isAffine_of_isAffineHom (pullback.snd (ab.mulByNat p) ab.zeroSection)
  infer_instance

/-- **`ker[p]` is an AFFINE SCHEME in characteristic `p`** (PROVEN 2026-07-27
over `isQuasiAffine_ker_mulByNat_of_field_char`; it used to be the sorry itself).

`ker[p] ⟶ Spec K` is proper as a base change of `[p]` (`isProper_mulByNat`),
hence universally closed, and `Spec K` is affine — so the general bridge
`isAffine_of_isQuasiAffine_of_universallyClosed` above turns the leaf's
`IsQuasiAffine` into `IsAffine`.

**This is a CHANGE OF SHAPE, NOT a reduction of content**: for a proper
`K`-scheme, quasi-affine, affine and finite are all equivalent.  The reason to
stop at `IsQuasiAffine` upstream is that it is literally what the
ample-line-bundle argument outputs (EGA II 5.1.2); see that leaf's docstring for
the classical proof, the corrected survey of what mathlib does and does not
have, and eight refuted routes with the check that would refute each
refutation. -/
theorem isAffine_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    IsAffine (pullback (ab.mulByNat p) ab.zeroSection) := by
  haveI : IsProper (ab.mulByNat p) := ab.isProper_mulByNat p
  haveI := isQuasiAffine_ker_mulByNat_of_field_char K ab p hp hchar
  exact isAffine_of_isQuasiAffine_of_universallyClosed
    (pullback.snd (ab.mulByNat p) ab.zeroSection)

/-- **`ker[p]` has FINITELY MANY POINTS in characteristic `p`** (PROVEN
2026-07-27 over `isAffine_ker_mulByNat_of_field_char`; it used to be the sorry
itself, cut down 2026-07-27 from `finite_preimage_mulByNat_of_field_char`).

`Spec K` has a single point, so this is one finite set: the underlying space of
`ker[p]` is finite, i.e. `ker[p]` is zero-dimensional.

**The proof is the "proper + affine ⟹ finite" bridge**, and it is pure scheme
theory with no abelian-variety content left in it.  `ker[p] ⟶ Spec K` is a base
change of `[p]`, hence PROPER (`isProper_mulByNat`); the leaf says the source is
an AFFINE scheme, and `Spec K` is affine, so the morphism is an affine morphism
(`isAffineHom_of_isAffine`).  Mathlib's
`IsFinite.iff_isProper_and_isAffineHom` then makes it a FINITE morphism, which
is `LocallyQuasiFinite` and `QuasiCompact`, so
`Scheme.Hom.finite_preimage_singleton` reads off the finite fibre.

Note this is a genuinely *different* route to `IsFinite` from the one
`isFinite_ker_mulByNat_of_field_char` below takes (that one goes through
Zariski's main theorem).  Both are kept: the ZMT bridge
`isFinite_ker_mulByNat_of_finite_preimage` is stated over an arbitrary base and
is what the general-`n` chain uses, while the affine bridge is what makes the
residue match the shape the theorem of the cube produces.

For the mathematics — why `d[p] = 0` kills the cheap route, the two classical
cube proofs, the re-verified survey of what is missing from the pin, and the
eight refuted cube-free routes — see `isQuasiAffine_ker_mulByNat_of_field_char`
above, which is now the leaf (`isAffine_ker_mulByNat_of_field_char` was itself
cut down to it 2026-07-27 and is PROVEN). -/
theorem finite_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    ∀ s : Spec (CommRingCat.of K),
      (⇑(pullback.snd (ab.mulByNat p) ab.zeroSection) ⁻¹' {s}).Finite := by
  haveI : IsProper (ab.mulByNat p) := ab.isProper_mulByNat p
  haveI := isAffine_ker_mulByNat_of_field_char K ab p hp hchar
  haveI : IsFinite (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact fun s => Scheme.Hom.finite_preimage_singleton _ s

/-- **`ker[p]` is a finite group scheme in characteristic `p`** — equivalently,
`[p]` is an ISOGENY (PROVEN 2026-07-27 over `finite_ker_mulByNat_of_field_char`,
through the Zariski's-main-theorem bridge `isFinite_ker_mulByNat_of_finite_preimage`).

**What changed.**  The old leaf asked for finiteness of EVERY fibre of `[p]`.
The shearing block above proves — cube-free and over an arbitrary base — that
all fibres are finite as soon as this ONE fibre is
(`finite_preimage_mulByNat_of_isFinite_ker`).  So the whole residue became the
single statement every textbook actually proves: `ker[p]` is finite, of order
`p^{2g}`; and by `isFinite_ker_mulByNat_of_finite_preimage` even that is
reduced to a bare POINT SET being finite, `finite_ker_mulByNat_of_field_char`
above.  The chain from there to `finite_preimage_mulByNat_of_field_char` is
entirely proven.

**Where the leaf is now** (2026-07-27, fourth cut).
`finite_ker_mulByNat_of_field_char`, `isAffine_ker_mulByNat_of_field_char` and
`isQuasiAffine_ker_mulByNat_of_field_char` are all PROVEN; the sole remaining
leaf on this route is `isQuasiAffine_ker_mulByNat_of_isAlgClosed` — "`ker[p]` is
a QUASI-AFFINE scheme over an ALGEBRAICALLY CLOSED field of characteristic
`p`" — reached from the previous leaf by ROUTE 9, the base-change reduction
"WLOG `K` algebraically closed", which unlike the two cuts before it strengthens
the HYPOTHESES rather than restating the conclusion.  Quasi-affineness itself,
for a proper `K`-scheme, is EQUIVALENT to affineness and hence to
finiteness, so those two cuts changed the shape and not the content.  They were made
because `IsQuasiAffine` is literally what the ample-line-bundle argument outputs
(EGA II 5.1.2), and the remaining step to `IsAffine` is now the proven bridge
`isAffine_of_isQuasiAffine_of_universallyClosed` rather than an obligation.  The
refuted cube-free routes and the corrected missing-machinery survey live in that
leaf's docstring; read it before attacking anything here.

**So the honest remaining content is "`ker[p]` is zero-dimensional"** —
properness, Zariski's main theorem and the shearing supply everything else.

**Why this is still the cube, and why the cheap route dies here.**  The
Lie-algebra argument that proves the sibling
`finite_preimage_mulByNat_of_field_prime_to_char` computes `d[n] = n · id`; at
`n = p = ringChar K` that is ZERO, so `[p]` is not unramified and the argument
says nothing.  `[p]` really is inseparable — its kernel contains `ker F` for the
relative Frobenius `F`, an infinitesimal group scheme — so this is a limitation
of the mathematics, not of the write-up.  Two classical proofs, both blocked at
this pin:

* Mumford *Abelian Varieties* §6, Application 2 of the theorem of the cube:
  take a symmetric ample `L`, use `[p]^* L ≅ L^{p²}`, again ample for `p ≠ 0`;
  then `[p]^* L` is ample and trivial on `ker[p]`, which forces `ker[p]` to be
  zero-dimensional.
* `[p] = V ∘ F`, with `F` the relative Frobenius (finite, and a homeomorphism
  on underlying spaces) and `V` the Verschiebung.  `V` is constructed by
  duality, so this route needs `Pic⁰` and the dual abelian variety.

**MISSING MACHINERY at this pin, each claim refutable by one grep** (re-verified
2026-07-27 against the worktree's own `.lake/packages/mathlib`).
`grep -rl Ample Mathlib/AlgebraicGeometry/` returns NOTHING: there are no ample
line bundles (the only `Ample` in mathlib is `Analysis/Convex/AmpleSet.lean`).
`grep -rli picard Mathlib/AlgebraicGeometry/` returns only
`EllipticCurve/Weierstrass.lean`: there is no Picard scheme or functor
(`RingTheory/PicardGroup.lean` is about modules).
`grep -rlie "line bundle\|invertible sheaf\|InvertibleSheaf" Mathlib/AlgebraicGeometry/`
returns NOTHING, and `Mathlib/AlgebraicGeometry/Modules/` contains only
`Presheaf.lean`, `Sheaf.lean`, `Tilde.lean` — so there is no invertible-sheaf
theory to build `Pic` on.  There is no theorem of the cube
(`grep -rli "theoremOfTheCube" Mathlib/` is empty), no relative Frobenius
(`grep -rli frobenius Mathlib/AlgebraicGeometry/` is empty) and no
Cohen–Macaulay theory (`grep -rl CohenMacaulay Mathlib/` is empty).
`~/cs/FLT` has none of it either: its only `Ample`/`Picard` matches are
`import Mathlib.RingTheory.PicardGroup`.
What mathlib HAS started is abelian varieties themselves —
`Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean`, carrying
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`,
`isCommMonObj_of_isProper_of_geometricallyIntegral` and `smooth_of_grpObj`.
Re-check that directory at every pin bump.

**`hp` and `hchar` are deliberately carried even though the statement is true
without them** — `ker[n]` is finite for every `n ≠ 0` — because without them
this leaf would silently duplicate the content the sibling needs.  Carrying
them records that this is exactly the residue the Lie-algebra route cannot
reach, and makes the leaf VACUOUS in characteristic zero. -/
theorem isFinite_ker_mulByNat_of_field_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) :
    IsFinite (pullback.snd (ab.mulByNat p) ab.zeroSection) :=
  ab.isFinite_ker_mulByNat_of_finite_preimage p
    (finite_ker_mulByNat_of_field_char K ab p hp hchar)

end ShearReduction

/-- **`[p]` has finite fibres in characteristic `p`** (PROVEN 2026-07-27 over
`isFinite_ker_mulByNat_of_field_char`, via the cube-free shearing reduction).

The other half of the old `finite_preimage_mulByNat_of_field`, split out
2026-07-27.  **It is no longer a leaf**: the shearing block above reduces it,
cube-free, to the single fibre `ker[p]`, and the residue now lives in
`isFinite_ker_mulByNat_of_field_char`.

The statement is UNCHANGED — same name, same hypotheses, same conclusion — so
every consumer (`finite_preimage_mulByNat_of_field` below) resolves exactly as
before.  `hp` and `hchar` are not used by this assembly; they are passed
through to the residual leaf, which is where they are recorded as marking the
Lie-algebra route's blind spot.  The leaf remains VACUOUS in characteristic
zero, and so does this theorem's route through it.

For the mathematics — why `d[p] = 0` kills the cheap route, the two classical
cube proofs, and the verified survey of what is missing from the pin — see
`isFinite_ker_mulByNat_of_field_char` above.  It is not repeated here, so that
there is exactly one place to update when mathlib grows ample bundles. -/
theorem finite_preimage_mulByNat_of_field_char {X : Scheme.{u}}
    (K : Type u) [Field K] {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK)
    (p : ℕ) (hp : p.Prime) (hchar : ringChar K = p) (a : X) :
    (⇑(ab.mulByNat p) ⁻¹' {a}).Finite :=
  ab.finite_preimage_mulByNat_of_isFinite_ker p
    (isFinite_ker_mulByNat_of_field_char K ab p hp hchar) a

/-- **The fibres of `[n]` on an abelian VARIETY are FINITE** (PROVEN
2026-07-27 over the two declarations just above).

**Status update 2026-07-27, later the same day.**  Of those two,
`finite_preimage_mulByNat_of_field_prime_to_char` is now itself PROVEN, over
the single new leaf `nonempty_module_infKernel_of_squareZero` (the Lie algebra
of a smooth group scheme).  So the two open leaves under this declaration are
now that one and `finite_preimage_mulByNat_of_field_char`, and only the
SECOND of them needs the theorem of the cube.

This is the SECOND cube input, and it is the one the torsion CARDINALITY
arguments need.  It says exactly that `ker[n]` is a finite group scheme:
the fibre of `[n]` over a point `a` is a torsor under the kernel taken in
the fibre of `f` through `a`, so all the fibres are finite as soon as one
of them is.

**Why it is stated on point-set fibres rather than as `LocallyQuasiFinite`.**
Its consumer, `locallyQuasiFinite_mulByNat` in `Modularity/TateModule.lean`,
used to BE the leaf.  But `LocallyQuasiFinite` is (locally of finite type)
+ (quasi-finite fibres), and the first half is already free here
(`locallyOfFiniteType_mulByNat`), so the old leaf was redundantly asking a
prover for something already proven.  Mathlib's
`LocallyQuasiFinite.of_finite_preimage_singleton` needs only
`[LocallyOfFiniteType]` plus this statement, so this is the exact residue.

**Independent of `flat_mulByNat`.**  Neither leaf implies the other at this
pin: flatness would follow from finite fibres only via miracle flatness
(absent — mathlib has NO Cohen–Macaulay or depth theory at all, though it
does have `ringKrullDim` and the dimension-drop lemmas; see the survey in
`flat_of_flat_fiberMap` above), and finite fibres
do not follow from flatness at all (`f` itself is flat with positive
dimensional fibres).  Both are outputs of the theorem of the cube, and a
prover who has the cube discharges both at once.

**THE BASE IS A FIELD** (2026-07-26).  This is the residue of
`finite_preimage_mulByNat` after base change to the residue field of a
point, so it is a statement about an abelian VARIETY over `K` — the setting
of every textbook treatment — rather than about an abelian scheme over an
arbitrary base.  Nothing else was removed: the reduction below is formal.

**THE SPLIT (2026-07-27), replacing the previous "atomic at this pin"
verdict.**  This is no longer a leaf.  It is proven by strong induction on
`n` over the two declarations above, which are genuinely different
mathematical problems and want different provers (and the first of them has
since been PROVEN, over the Lie-algebra leaf
`nonempty_module_infKernel_of_squareZero`).  Writing `p = ringChar K`, the
step is:

* `(n : K) ≠ 0` — pass to `finite_preimage_mulByNat_of_field_prime_to_char`;
* `(n : K) = 0` — then `p ≠ 0` (else `K` has characteristic zero and `n = 0`),
  so `p` is prime and `p ∣ n`, say `n = p · c` with `c ≠ 0` and `c < n`.
  `mulByNat_mul` gives `[p · c] = [c] ≫ [p]`, and `finite_preimage_comp`
  combines the induction hypothesis at `c` with
  `finite_preimage_mulByNat_of_field_char` at `p`.

The old docstring said "closing it means building ample line bundles and the
theorem of the cube".  That is now known to be true of ONLY ONE of the two
halves.  The prime-to-characteristic half has a completely different and much
cheaper classical proof (the Lie algebra — see its docstring), needing no line
bundles, no `Pic` and no cube; the ample/cube machinery is confined to
`finite_preimage_mulByNat_of_field_char`.

**A caution about the characteristic-zero reading.**
`finite_preimage_mulByNat_of_field_char` is VACUOUS over a field of
characteristic zero, since `ringChar K = p` with `p` prime is then
unsatisfiable — so over such a base this statement rests on the first leaf
alone.  That does NOT retire the second leaf for this development: the
consumer `finite_preimage_mulByNat` applies this theorem to
`S.residueField (f a)`, whose characteristic is positive at the finite
places, which is precisely where the Frey curve's torsion is studied. -/
theorem finite_preimage_mulByNat_of_field {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : n ≠ 0)
    (a : X) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  suffices h : ∀ (m : ℕ), m ≠ 0 → ∀ (b : X), (⇑(ab.mulByNat m) ⁻¹' {b}).Finite from h n hn a
  clear hn a
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm b
    by_cases hmK : ((m : ℕ) : K) = 0
    · have hp0 : ringChar K ≠ 0 := by
        intro h0
        haveI : CharP K 0 := h0 ▸ (inferInstance : CharP K (ringChar K))
        haveI : CharZero K := CharP.charP_to_charZero K
        exact hm (Nat.cast_eq_zero.mp hmK)
      have hp : (ringChar K).Prime :=
        (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hp0
      obtain ⟨c, rfl⟩ : ringChar K ∣ m := (CharP.cast_eq_zero_iff K _ m).mp hmK
      have hc0 : c ≠ 0 := by rintro rfl; exact hm (Nat.mul_zero _)
      have hclt : c < ringChar K * c := by
        have h1 : 1 * c < ringChar K * c :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hc0)).mpr hp.one_lt
        rwa [one_mul] at h1
      rw [ab.mulByNat_mul]
      exact finite_preimage_comp _ _ (ih c hclt hc0)
        (finite_preimage_mulByNat_of_field_char K ab _ hp rfl) b
    · exact finite_preimage_mulByNat_of_field_prime_to_char K ab _ hmK b

open _root_.CategoryTheory.Limits in
/-- **The fibres of `[n]` are FINITE** (PROVEN 2026-07-26 over the
field-base leaf `finite_preimage_mulByNat_of_field`).

Statement unchanged — its consumer `locallyQuasiFinite_mulByNat` in
`Modularity/TateModule.lean` resolves exactly as before.

**The reduction.**  Every point of `[n] ⁻¹' {a}` lies in the fibre of `f`
through `a`, because `[n] ≫ f = f`.  That fibre is
`f.fiber (f a) = A ×_S Spec κ(f a)`, which by
`AbelianSchemeStruct.baseChange` is again an abelian scheme — now over a
FIELD — and by `AbelianSchemeStruct.baseChange_mulByNat` its `[n]` is the
restriction of `[n]` along the immersion `f.fiberι (f a)`.  So

  `[n] ⁻¹' {a} = f.fiberι (f a) '' ([n]_{fibre} ⁻¹' {a as a point of the fibre})`,

and the right-hand side is the image of a finite set.  `Scheme.Hom.asFiber`
supplies `a` as a point of its own fibre and `Scheme.Hom.range_fiberι`
identifies the range of the immersion with `f ⁻¹' {f a}`.

No abelian-variety input is used here: `hn` is passed straight through to
the field-base leaf. -/
theorem finite_preimage_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0)
    (a : A) : (⇑(ab.mulByNat n) ⁻¹' {a}).Finite := by
  have hinj : Function.Injective (f.fiberι (f a)) := (f.fiberι (f a)).isEmbedding.injective
  have hcomm : ∀ x : ↥(pullback f (S.fromSpecResidueField (f a)) : Scheme.{u}),
      pullback.fst f (S.fromSpecResidueField (f a))
          ((ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x)
        = ab.mulByNat n (pullback.fst f (S.fromSpecResidueField (f a)) x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ab.baseChange_mulByNat]
  have hfin := finite_preimage_mulByNat_of_field ↥(S.residueField (f a))
      (ab.baseChange (S.fromSpecResidueField (f a))) n hn (f.asFiber a)
  refine (hfin.image (f.fiberι (f a))).subset ?_
  rintro x (hx : ab.mulByNat n x = a)
  have hfx : f x = f a := by
    have hcm : (ab.mulByNat n ≫ f).base x = f.base x := by rw [ab.mulByNat_comp]
    simpa [hx] using hcm.symm
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (f.fiberι (f a)) := by
    rw [Scheme.Hom.range_fiberι]; exact hfx
  refine ⟨x₀, ?_, hx₀⟩
  show (ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x₀ = f.asFiber a
  apply hinj
  have e1 : f.fiberι (f a) ((ab.baseChange (S.fromSpecResidueField (f a))).mulByNat n x₀)
      = ab.mulByNat n (f.fiberι (f a) x₀) := hcomm x₀
  rw [e1, hx₀, hx, Scheme.Hom.fiberι_asFiber]

/-- **`[n]` is FLAT on an abelian scheme OVER A FIELD** (PROVEN
2026-07-27 over two leaves, with no residue).

This is the whole of the abelian-variety flatness statement, in the only
setting where the classical proof applies: the base is `Spec K` for a
field `K`, so `ab.smooth` really does make `X` regular — which is exactly
what fails over the arbitrary base `S` of `f`.

**The proof.**  `ab.proper`, `ab.smooth` and `ab.connected` are precisely
the three hypotheses that `flat_of_finite_fibres_endo` asks of the
structure morphism `fK`.  Properness of `[n]` itself is FREE
(`isProper_mulByNat`, via `IsProper.of_comp` applied to `[n] ≫ fK = fK`),
and finiteness of the fibres of `[n]` is exactly
`finite_preimage_mulByNat_of_field`.  So the two leaves meet with nothing
left over, and `hn` is passed straight through to the cube leaf — this
assembly introduces no hypothesis of its own and no mathematics of its
own.

**Where the content went.**  All abelian-variety input is in
`finite_preimage_mulByNat_of_field` (the theorem of the cube); all
commutative algebra is in `flat_of_finite_fibres_endo` (miracle
flatness).  Since 2026-07-27 the cube leaf is therefore the ONLY leaf in
the divisibility chain carrying abelian-variety content — it used to be
needed twice over, once here and once for the torsion cardinality
arguments.

`hn : n ≠ 0` is load-bearing downstream rather than here; see the
discussion in `flat_mulByNat` below. -/
theorem flat_mulByNat_of_field {X : Scheme.{u}} (K : Type u) [Field K]
    {fK : X ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct fK) (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) :=
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.connected
  haveI := ab.isProper_mulByNat n
  flat_of_finite_fibres_endo fK (ab.mulByNat n)
    (finite_preimage_mulByNat_of_field (CommRingCat.of K) ab n hn)

/-- **`[p]` is FLAT ON EVERY FIBRE, for `p` prime** (PROVEN 2026-07-27;
abelian varieties — Mumford *Abelian Varieties* §6 (Application 2 of the
theorem of the cube) and §18, Milne *Abelian Varieties* I.7, Silverman
*AEC* III.6).

This is the abelian-variety half of the old `flat_mulByNat`, and the
point of the cut is that it is a statement **over a field**: the fibre
`f.fiber s` is an abelian variety over the residue field `κ(s)`, and
`fiberMapOver (ab.mulByNat p) _ s` is `[p]` on it.

**THE OLD DOCSTRING'S CLOSING NOTE WAS STALE, AND IT WAS THE WHOLE
OBSTACLE** (corrected 2026-07-27).  It read: "the fibre carries an
abelian-variety structure, but this module does not hand you one:
`AbelianSchemeStruct` is not currently known to base-change", and it
named constructing that structure as the natural first step.
**`AbelianSchemeStruct.baseChange` has existed in this very module since
2026-07-26**, together with `AbelianSchemeStruct.baseChange_mulByNat`,
which says precisely that `[n]` commutes with the projection; the sibling
`finite_preimage_mulByNat` was already proven by exactly that route.
Refute the note in one grep:
`grep -n "def baseChange" Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`.

**The proof, in one move.**  `Scheme.Hom.fiber f s` is by definition
`pullback f (S.fromSpecResidueField s)`, so
`ab.baseChange (S.fromSpecResidueField s)` is an `AbelianSchemeStruct` on
`pullback.snd f (S.fromSpecResidueField s)` — an abelian scheme over
`Spec κ(s)`, i.e. an abelian VARIETY.  Its multiplication morphism IS the
fibre map:

  `fiberMapOver [p] _ s = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p`,

which `pullback.hom_ext` reduces to two identities: `baseChange_mulByNat`
after composing with `pullback.fst`, and `mulByNat_comp` for the
base-changed structure after composing with `pullback.snd` (`fiberMapOver`
carries the identity in that slot).  Then `flat_mulByNat_of_field`
applies with `K := S.residueField s`, and `hp.pos.ne'` supplies its
`n ≠ 0`.

**`p.Prime` is unused by this proof, and that is deliberate.**  Only
`p ≠ 0` is needed, since `flat_mulByNat_of_field` holds for every nonzero
`n`.  The hypothesis is kept because the statement is consumed by
`flat_mulByNat`'s reduction to primes, and because — as the old note
observed — a prover attacking the cube directly may want to split on
whether `p` equals the residue characteristic, the case `p ≠ ℓ` being
where `[p]` is étale.  It is a genuine hypothesis of the STATEMENT that
this particular proof happens not to need, not a hidden weakening. -/
theorem flat_fiberMap_mulByNat (ab : AbelianSchemeStruct f) (p : ℕ) (hp : p.Prime)
    (s : S) : Flat (fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s) := by
  have hkey : fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
      = show (f.fiber s : Scheme.{u}) ⟶ f.fiber s from
          (ab.baseChange (S.fromSpecResidueField s)).mulByNat p := by
    refine Limits.pullback.hom_ext ?_ ?_
    · calc fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
              ≫ Limits.pullback.fst f (S.fromSpecResidueField s)
          = Limits.pullback.fst f (S.fromSpecResidueField s) ≫ ab.mulByNat p :=
            Limits.pullback.lift_fst _ _ _
        _ = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p
              ≫ Limits.pullback.fst f (S.fromSpecResidueField s) :=
            (ab.baseChange_mulByNat (S.fromSpecResidueField s) p).symm
    · calc fiberMapOver (ab.mulByNat p) (ab.mulByNat_comp p) s
              ≫ Limits.pullback.snd f (S.fromSpecResidueField s)
          = Limits.pullback.snd f (S.fromSpecResidueField s) ≫ 𝟙 _ :=
            Limits.pullback.lift_snd _ _ _
        _ = Limits.pullback.snd f (S.fromSpecResidueField s) := Category.comp_id _
        _ = (ab.baseChange (S.fromSpecResidueField s)).mulByNat p
              ≫ Limits.pullback.snd f (S.fromSpecResidueField s) :=
            ((ab.baseChange (S.fromSpecResidueField s)).mulByNat_comp p).symm
  rw [hkey]
  exact flat_mulByNat_of_field ↥(S.residueField s) (ab.baseChange _) p hp.pos.ne'

/-- **Multiplication by a nonzero `n` on an abelian scheme is FLAT**
(abelian varieties; Mumford *Abelian Varieties* §6 (Application 2 of the
theorem of the cube) and §18, Milne *Abelian Varieties* I.7, Silverman
*AEC* III.6).

**PROVEN 2026-07-26**, over the two leaves above plus `mulByNat_mul`.
It used to be the sorry itself; the abelian-variety content is now in
`flat_fiberMap_mulByNat` and the scheme theory in
`flat_of_flat_fiberMap`.  (Statement and proof unchanged since;
the declaration merely MOVED here on 2026-07-27, below
`finite_preimage_mulByNat_of_field`, so that `flat_fiberMap_mulByNat`
could be proven over it.)

Together with `isProper_mulByNat` and `locallyOfFinitePresentation_mulByNat`
(both free) this says `[n]` is **finite locally free**, of degree `n^{2g}`
on each fibre of `f` — the classical statement that `[n]` is an isogeny.
Only the flatness was ever asked for here, because properness and finite
presentation are already available without any abelian-variety input.

**The proof, in three moves.**

1. *Reduce to primes.*  `[1] = 𝟙` (`mulByNat_one`) is flat, and
   `[p·m] = [m] ≫ [p]` (`mulByNat_mul`), so a strong induction on `n`
   using `Nat.exists_prime_and_dvd` and the fact that `Flat` is stable
   under composition reduces everything to `n` prime.  `hn : n ≠ 0` is
   what makes the induction start: it rules out the one value of `n`
   with no prime factorization to descend along.
2. *Descend to the fibres.*  `f` is smooth, hence flat and locally of
   finite presentation, and `[p]` is locally of finite presentation for
   free (`locallyOfFinitePresentation_mulByNat`).  So
   `flat_of_flat_fiberMap` applies to `[p]` as a morphism over `S`.
3. *The fibre statement* is `flat_fiberMap_mulByNat`.

**`hn` is LOAD-BEARING** — it is a genuine hypothesis, not bookkeeping.
`mulByNat 0 = f ≫ zeroSection` factors through the base, so for relative
dimension `g ≥ 1` it is not flat: its fibre over a point of the zero
section is a whole fibre of `f`, of dimension `g`, while its fibre over
any other point is empty, and flatness would force those to have the
same dimension.

**Relation to the sibling leaf.**  `Modularity/TateModule.lean` carries
`locallyQuasiFinite_mulByNat`, which asks for the QUASI-FINITENESS of the
same morphism and is the same theorem-of-the-cube input; over it that file
derives `IsFinite (mulByNat n)` by Zariski's main theorem.  The two are
deliberately *not* merged: quasi-finiteness is what the torsion
CARDINALITY arguments need, flatness is what DIVISIBILITY needs, and a
prover who has the cube gets both at once.  Neither consumes the other.
(Since 2026-07-27 they share their one leaf,
`finite_preimage_mulByNat_of_field`, so "a prover who has the cube gets
both at once" is now literally true of this file.) -/
theorem flat_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) := by
  haveI := ab.smooth
  haveI : LocallyOfFinitePresentation f := inferInstance
  haveI : Flat f := inferInstance
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [ab.mulByNat_one]; infer_instance
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, rfl⟩ := hpd
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmlt : m < p * m := by
        have h1 : 1 * m < p * m :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hm0)).mpr hp.one_lt
        simpa using h1
      haveI := ih m hmlt hm0
      haveI : LocallyOfFinitePresentation (ab.mulByNat p) :=
        ab.locallyOfFinitePresentation_mulByNat p
      haveI : Flat (ab.mulByNat p) :=
        flat_of_flat_fiberMap (ab.mulByNat p) (ab.mulByNat_comp p)
          (flat_fiberMap_mulByNat ab p hp)
      rw [ab.mulByNat_mul]
      infer_instance

/-- **`[n]` is flat and locally of finite presentation** (PROVEN
2026-07-26 over `flat_mulByNat`; the finite presentation is free).

Retained with its original name and statement so that every existing
consumer resolves unchanged; the abelian-variety content is now entirely
in `flat_mulByNat`. -/
theorem flat_locallyOfFinitePresentation_mulByNat (ab : AbelianSchemeStruct f)
    (n : ℕ) (hn : n ≠ 0) :
    Flat (ab.mulByNat n) ∧ LocallyOfFinitePresentation (ab.mulByNat n) :=
  ⟨flat_mulByNat ab n hn, ab.locallyOfFinitePresentation_mulByNat n⟩

/-- **`[n]` is UNIVERSALLY OPEN** (PROVEN over the leaf): a flat morphism
locally of finite presentation is universally open,
`AlgebraicGeometry.UniversallyOpen.of_flat` (Stacks 01UA). -/
theorem universallyOpen_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    UniversallyOpen (ab.mulByNat n) := by
  obtain ⟨h1, h2⟩ := flat_locallyOfFinitePresentation_mulByNat ab n hn
  haveI := h1
  haveI := h2
  exact UniversallyOpen.of_flat _

/-- **`[n]` is SURJECTIVE** (PROVEN over the leaf).

The image of `[n]` is OPEN because `[n]` is universally open, and CLOSED
because `[n]` is proper — and properness is free, so the leaf supplies
only the openness.  So the image is a clopen subset of `A`.

`A` itself need not be connected, so the argument is fibrewise: given
`a : A`, the fibre `f ⁻¹' {f a}` is CONNECTED (`ab.connected`, through
`Scheme.Hom.isConnected_preimage_singleton`), and it meets the image
because `[n]` fixes the zero section, whose value at `f a` lies in that
fibre.  A connected set meeting a clopen set is contained in it
(`IsPreconnected.subset_isClopen`), so `a` is in the image.

This is the only use of `ab.connected` in the divisibility chain, and it
cannot be dropped: on a disconnected commutative group scheme — say the
constant group scheme `ℤ/n` over a field — `[n]` is the zero map and is
very far from surjective. -/
theorem surjective_mulByNat (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0) :
    Surjective (ab.mulByNat n) := by
  haveI := ab.proper
  haveI := ab.connected
  haveI := ab.isProper_mulByNat n
  haveI := universallyOpen_mulByNat ab n hn
  have hop : IsOpen (Set.range ⇑(ab.mulByNat n)) :=
    ((ab.mulByNat n).isOpenMap).isOpen_range
  have hcl : IsClosed (Set.range ⇑(ab.mulByNat n)) :=
    ((ab.mulByNat n).isClosedMap).isClosed_range
  refine ⟨fun a => ?_⟩
  have hconn : _root_.IsConnected (⇑f ⁻¹' {f a}) := f.isConnected_preimage_singleton (f a)
  have hz : (ab.mulByNat n) (ab.zeroSection (f a)) = ab.zeroSection (f a) := by
    have h := ab.zeroSection_comp_mulByNat n
    have h2 := congrArg (fun φ : S ⟶ A => φ (f a)) h
    simpa using h2
  have hfz : f (ab.zeroSection (f a)) = f a := by
    have h := ab.zeroSection_comp
    have h2 := congrArg (fun φ : S ⟶ S => φ (f a)) h
    simpa using h2
  have hsub := hconn.isPreconnected.subset_isClopen ⟨hcl, hop⟩
    ⟨ab.zeroSection (f a), hfz, ⟨_, hz⟩⟩
  exact hsub rfl

open _root_.CategoryTheory.Limits in
/-- **A `K`-point lifts along a surjective morphism locally of finite
type, `K` algebraically closed** (PROVEN 2026-07-26).

This is the Nullstellensatz step, and it contains no abelian-variety
input at all — it is general scheme theory and would be at home in
mathlib.

Given `w : Spec K ⟶ Y`, base-change `φ` along `w`.  Surjectivity of `φ`
gives `Set.range (pullback.snd φ w) = w ⁻¹' Set.range φ = univ`
(`Scheme.Pullback.range_snd`), so `pullback.snd` is surjective and in
particular `pullback φ w` is NONEMPTY.  It is locally of finite type over
`Spec K`, and `K` is a field hence a Jacobson ring, so the pullback is a
JACOBSON SPACE and therefore has a closed point
(`nonempty_inter_closedPoints`).  Because `K` is algebraically closed, the
residue field at a closed point of a `K`-scheme locally of finite type is
`K` itself, so that closed point IS a `K`-point
(`AlgebraicGeometry.pointOfClosedPoint`), i.e. a section of
`pullback.snd`.  Composing it with `pullback.fst` and using
`pullback.condition` gives the required factorization.

Note what is NOT needed: no finiteness of `φ`, no flatness, no
properness. -/
theorem exists_comp_eq_of_surjective {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [Surjective φ] [LocallyOfFiniteType φ] {K : Type u} [Field K] [IsAlgClosed K]
    (w : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ u : Spec (CommRingCat.of K) ⟶ X, u ≫ φ = w := by
  haveI hsurj : Surjective (pullback.snd φ w) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, range_eq_univ, Set.preimage_univ]
  obtain ⟨q, -⟩ := hsurj.surj (IsLocalRing.closedPoint K)
  haveI : JacobsonSpace ↥(pullback φ w) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd φ w)
  obtain ⟨p, -, hp⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set ↥(pullback φ w))) ⟨q, trivial⟩ isClosed_univ.isLocallyClosed
  refine ⟨pointOfClosedPoint (pullback.snd φ w) p hp ≫ pullback.fst φ w, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    pointOfClosedPoint_comp, Category.id_comp]

/-- **Every `F̄`-point of `A` is `[n]` of another one** (PROVEN over the
single leaf `flat_locallyOfFinitePresentation_mulByNat`).

This is the scheme-level form of divisibility, and it is what
`exists_nsmul_eq_geomFibrePt` consumes.  Note that no compatibility with
the base is imposed on `w` or asserted of `u`: `u ≫ [n] = w` forces
`u ≫ f = w ≫ f` automatically, so the statement is about `A` alone. -/
theorem exists_comp_mulByNat_eq (ab : AbelianSchemeStruct f) (n : ℕ) (hn : n ≠ 0)
    {K : Type u} [Field K] [IsAlgClosed K] (w : Spec (CommRingCat.of K) ⟶ A) :
    ∃ u : Spec (CommRingCat.of K) ⟶ A, u ≫ ab.mulByNat n = w := by
  haveI := surjective_mulByNat ab n hn
  haveI := ab.locallyOfFiniteType_mulByNat n
  exact exists_comp_eq_of_surjective (ab.mulByNat n) w

end MulByNat

end Fermat
