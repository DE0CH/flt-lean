/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension

/-!
# The complement of a closed point of a smooth proper curve is affine

Classically (Hartshorne IV.1, Stacks `0BXB`) a nonempty effective divisor on a smooth
proper geometrically connected curve over a field is **ample**, so the complement of its
support is affine.  Specialised to a single closed point this is the statement that makes
the *affine chart* of a pointed curve exist — and it is the scheme-theoretic half of
"an elliptic scheme has a Weierstrass model", the other half being Riemann–Roch.

## What is here

* `IsClosedImmersion.of_section` and `isClosed_range_of_section` — a section of a
  separated morphism is a closed immersion, so its range is closed.  PROVEN.
* `range_eq_singleton_of_spec_field` — the range of a `K`-point of a scheme is a
  singleton, `K` a field.  PROVEN.  (`Spec K` is a one-point space.)
* `isClosed_singleton_of_section` — the two combined: the image of a section of a
  separated morphism from the spectrum of a field is a closed point.  PROVEN.
* `affineLineOver` — the structure morphism `𝔸¹_K ⟶ Spec K`, used only to say "over `K`".
* `coordOf`, `structHom` — the regular function a morphism `U ⟶ 𝔸¹_K` classifies, and the
  `K`-algebra structure `strX` puts on `Γ(X, U)`.  (`coordOf` was moved up here 2026-07-31 from
  the stalk section, so that the Riemann–Roch decomposition can name it.)
* `exists_toAffineLine_coordOf_eq` — **PROVEN 2026-07-31, no sorry**: every section of
  `Γ(X, U)` classifies a `K`-morphism `U ⟶ 𝔸¹_K`.  Pure `Γ ⊣ Spec` adjunction
  (`ΓSpecIso_inv_ΓSpec_adjunction_homEquiv`, `ext_to_Spec`), and it is what lets both
  Riemann–Roch sub-leaves below be about SECTIONS rather than morphisms.
* `exists_germToFunctionField_eq_of_forall_isInteger`, `functionFieldHom`,
  `structHom_comp_germToFunctionField`, `notIsIntegralElem_of_germToFunctionField` —
  **PROVEN 2026-07-31, no sorry**: the bridge `Γ(X, U) = ⋂_{x ∈ U} 𝒪_{X,x}` between the
  function field and sheaf sections, and the `K`-algebra structure on `K(X)` it is measured
  against.  Absent from the pin.
* `exists_forall_isInteger_notIsIntegralElem_functionField` — **sorry leaf, RIEMANN–ROCH, and
  after two cuts the ONLY open leaf in this file**: one element of `K(X)` lying in the local ring
  at every point other than `z` and not integral over `K`.  That is `L(n·[z]) ⊋ K` with the `n`
  suppressed.  No morphism, no `𝔸¹`, no quasi-finiteness, and no sheaf.
* `exists_notIsIntegralElem_section_compl_singleton` — **PROVEN 2026-07-31** over that leaf and
  the bridge: the same thing packaged as a SECTION of `Γ(X, X ∖ {z})`.
* `coordHom_apply_eq_eval₂`, `base_genericPoint_asIdeal_eq_bot`,
  `finite_of_isClosed_of_forall_isClosed_singleton` — **PROVEN 2026-07-31, no sorry**.  The
  middle one is the CONVERSE of the pole argument's MOVE 3: a nonconstant section sends the
  generic point of `U` to the generic point of `𝔸¹_K`.  The last is pure topology (a closed set
  of closed points in a noetherian scheme is finite).
* `isClosed_singleton_of_ne_genericPoint` — **PROVEN 2026-07-31, no sorry**: on a smooth curve,
  every point other than the generic one is CLOSED.  Dimension one, stated topologically; no
  morphism to `𝔸¹`, no polynomial, no quasi-finiteness.  It would sit just as well in
  `CurveExtension.lean` beside the other dimension facts.
* `locallyQuasiFinite_of_notIsIntegralElem_coordOf` — **PROVEN 2026-07-31, no sorry**: a
  nonconstant section classifies a QUASI-FINITE morphism.  Two cases, and neither is
  Riemann–Roch: over the generic point of `𝔸¹_K` the fibre is the generic point of `U` alone
  (`Scheme.Hom.closePoints_subset_preimage_closedPoints`, `Spec K[T]` being Jacobson, plus the
  fact that `(0)` is not a closed point); over a closed point the fibre is closed and misses the
  generic point, hence finite.
* `exists_locallyQuasiFinite_toAffineLine_compl_singleton` — **PROVEN 2026-07-31** over those
  two, in four lines: a nonconstant regular function on `X ∖ {z}`, packaged as a quasi-finite
  `K`-morphism.
* `locallyOfFiniteType_affineLineOver` — `𝔸¹_K ⟶ Spec K` is locally of finite type.
  **PROVEN 2026-07-30**; the side condition of the right-cancellation used just below.
* `isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton` — the compactification step,
  that any such function's morphism to `𝔸¹_K` is proper.  **PROVEN 2026-07-30** over ONE
  sub-leaf, the next item; it was a bare `sorry` until then.
* `valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton` — the
  EXISTENCE half of the valuative criterion for that morphism.  **PROVEN 2026-07-30** over the
  next item; the uniqueness half and all three shape hypotheses
  `IsProper.of_valuativeCriterion` asks for (`QuasiCompact`, `QuasiSeparated`,
  `LocallyOfFiniteType`) are proven at its consumer.
* `notMem_range_of_closedPoint_ne`, `stalkSpecializes_stalkClosedPointTo_Spec`,
  `stalkSpecializes_stalkClosedPointTo`(`'`), `false_of_pole` — **PROVEN 2026-07-31, no sorry**:
  the `Spec (local ring)`-point machinery the pole argument needs and the pin does not have.
  The load-bearing one is `stalkSpecializes_stalkClosedPointTo`: mathlib's
  `Scheme.stalkClosedPointTo` is natural for LOCAL ring maps only in the trivial sense, and what
  the valuative criterion needs is naturality along `R ⟶ Frac R`, which is *not* local and moves
  the closed point to the generic point.  None of the four mentions a curve.
* `notMem_range_of_valuativeLift_toAffineLine_compl_singleton` — a lift of a valuative square
  into `X` cannot hit `z`.  **PROVEN 2026-07-31** over the two sub-leaves below; formerly a bare
  `sorry` (cut 2026-07-30).
* `exists_inv_coordOf_mem_maximalIdeal_compl_singleton` — SUB-LEAF 1, cut 2026-07-31 and
  **PROVEN the same day**: `1/f` lies in `𝔪_z`, i.e. `f` genuinely has a POLE at `z`.  The
  valuation-ring dichotomy (`ValuationRing.isInteger_or_isInteger`, over
  `valuationRing_stalk_of_smoothOfRelativeDimension_one` — **no DVR and no `¬ IsField` side
  condition needed**) plus `IsFractionRing.injective` for the stalks of an integral scheme.
* `res_top_eq_appTop_topIso`, `coordHom`(`_apply_X`, `_comp_C`), `exists_res_eq_of_germ_eq`,
  `false_of_res_eq_coordOf_of_locallyQuasiFinite` — **PROVEN 2026-07-31, no sorry**: the four
  items that close the extension obstruction.  The load-bearing one is the last: an OPEN `U` of
  a proper integral `X`, infinite, carrying a `K`-morphism `g : U ⟶ 𝔸¹_K` whose classified
  function is the restriction of a GLOBAL section, cannot be quasi-finite.  No curve, no
  valuation ring and no `z` appears in it.
* `not_exists_stalkSpecializes_eq_germ_coordOf_compl_singleton` — **PROVEN 2026-07-31**, cut
  the same day out of SUB-LEAF 1: `f` DOES NOT EXTEND ACROSS `z`, i.e. `germ_{x₀} f` is not in
  the image of `𝒪_{X,z} ⟶ 𝒪_{X,x₀}`.  With it the WHOLE properness half of the affineness route
  is closed and the file's only remaining leaf is Riemann–Roch.  **The proof is NOT the fibre
  dichotomy this file used to plan**: the morphism `ĝ : X ⟶ 𝔸¹_K`, its properness and Zariski's
  main theorem are all avoided, because the pin's `isIntegral_appTop_of_universallyClosed`
  makes a global regular function on a universally closed `X` algebraic over `K` outright — so
  only the SECTION has to be glued, never the morphism.  See its docstring.
* `exists_algebraMap_eq_stalkClosedPointTo_germ_coordOf` — SUB-LEAF 2, cut 2026-07-31 and
  **PROVEN the same day, no sorry**: `f`'s value at the `L`-point lies in `R`.  PURE
  BOOKKEEPING on the commuting square — no curve, no properness, no smoothness — separated out
  precisely so that the elaborator-fighting was not entangled with SUB-LEAF 1, which is exactly
  what let it close on its own.  Two helpers came out of it, both PROVEN and both absent from
  the pin: `ι_appLE_top_eq_topIso_inv` and `appLE_top_top_eq_appTop`.  Its docstring records the
  two `simp` traps that cost the round trips.
* `isAffineOpen_compl_singleton_of_isSmoothProperCurve` — **PROVEN 2026-07-28** over those
  two, by Zariski's main theorem.  It does NOT go through ampleness; see the next section.
* `exists_isOpenImmersion_range_eq_compl_of_section` — the packaged existential a consumer
  actually wants: a ring `R` and an open immersion `Spec R ⟶ X` onto the complement of the
  image of a `K`-point.  PROVEN over the two leaves.
* `exists_surjective_coordinateRingHom_of_generators` — two elements plus a Weierstrass
  relation plus `Subring.closure … = ⊤` give a SURJECTION out of the coordinate ring.
  PROVEN, no sorry.
* `injective_of_surjective_coordinateRing` — a surjection from a Weierstrass coordinate
  ring onto a domain that is not a field is injective.  PROVEN, no sorry.  This is the
  algebraic half of "the affine chart IS a Weierstrass coordinate ring"; it means the
  geometric side has to construct only a SURJECTION, never an isomorphism.

## The affineness leaf is now DECOMPOSED — the ampleness-free route, glue proven

`isAffineOpen_compl_singleton_of_isSmoothProperCurve` is no longer a bare `sorry`.  It is
proven here over exactly two named sub-leaves, along the Zariski's-main-theorem route:

* `exists_locallyQuasiFinite_toAffineLine_compl_singleton` — **RIEMANN–ROCH**, and the only
  place it enters: a nonconstant regular function on `X ∖ {z}`, packaged as a
  `K`-morphism `X ∖ {z} ⟶ 𝔸¹_K` that is `LocallyQuasiFinite`.  **PROVEN 2026-07-31** over two
  sub-leaves of its own, `exists_notIsIntegralElem_section_compl_singleton` (Riemann–Roch, a
  SECTION) and `locallyQuasiFinite_of_notIsIntegralElem_coordOf` (nonconstant ⟹ quasi-finite).
* `isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton` — **the compactification
  step**: any such morphism is proper.  Decomposed 2026-07-30 and **CLOSED OUTRIGHT on
  2026-07-31**: everything under it, down through
  `valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton`,
  `notMem_range_of_valuativeLift_toAffineLine_compl_singleton` and
  `not_exists_stalkSpecializes_eq_germ_coordOf_compl_singleton`, is now sorry-free.

**So as of 2026-07-31 the file has exactly ONE open leaf,
`exists_forall_isInteger_notIsIntegralElem_functionField` — RIEMANN–ROCH, asking for a single
nonconstant rational function with poles only at `z` and nothing else.**  Everything else here, the whole
compactification half and the whole quasi-finiteness half, is sorry-free.

and the glue between them, which is what this file newly PROVES:
`IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's main theorem, stacks `02LS`) turns
proper + quasi-finite into finite; `IsFinite ⟹ IsIntegralHom ⟹ IsAffineHom`; and
`isAffine_of_isAffineHom` against the affine target `Spec K[T]` gives `IsAffine` of the
open subscheme, which is definitionally `IsAffineOpen`.

**Ampleness is still absent from the pin, and the corrected refuting command is stronger
than the one previously recorded here.**  This file used to say that
`grep -rl 'Ample' Mathlib/AlgebraicGeometry/` "returns only files where the word occurs
inside `example`/`sample`".  Re-run 2026-07-28: it returns **nothing at all** — the only
`Ample` in the whole of mathlib is `Mathlib/Analysis/Convex/AmpleSet.lean`, which is convex
geometry and unrelated.  So:

    grep -rn 'Ample' .lake/packages/mathlib/Mathlib/ --include=*.lean | grep -v Convex

settles it.  There is no `IsAmple`, no `VeryAmple`, no Serre criterion for affineness, no
genus, no Riemann–Roch and no coherent-sheaf cohomology; `~/cs/FLT` has none either.

**What the previous note got wrong is the conclusion drawn from that absence**, not the
absence: it treated the leaf as atomic because ampleness is missing.  But the pin *does*
carry `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, and that is the whole of the
affineness step — so the ampleness gap never had to be paid at all.  Only the two sub-leaves
above remain, and neither of them mentions a divisor.

Note for whoever takes the compactification step — **updated 2026-07-30, and the previous
note's advice is now WRONG in one respect**.  It said the intended proof goes through the
projective model and `exists_unique_extension_of_valuationRing_stalk`.  It does not have to:
the pin carries `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` with
`IsProper.of_valuativeCriterion` (stacks `0BX5`), and no `ℙ¹` and no extension theorem is
needed to *set up* the proof — only to supply the lift.  So the properness statement is now
proven outright over the valuative-existence leaf, and what a prover owes is that leaf alone.
The half of the old note that survives is the half that matters: the step that has to be paid
is that a `K`-morphism `X ⟶ 𝔸¹_K` out of a proper `X` cannot be quasi-finite, so `g` genuinely
fails to extend and `z` is a pole.  That is B2 in the new leaf's docstring, and it is worth
splitting off as a leaf of its own.
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace
open scoped Polynomial

namespace AlgebraicGeometry

/-! ### Sections of a separated morphism -/

/-- **A section of a separated morphism is a closed immersion** (PROVEN).

`s ≫ f = 𝟙` is an isomorphism, hence a closed immersion, and `IsClosedImmersion` cancels
on the right against a separated morphism (`IsClosedImmersion.of_comp`). -/
theorem IsClosedImmersion.of_section {X Y : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ X}
    [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : IsClosedImmersion s := by
  have h : IsClosedImmersion (s ≫ f) := by
    rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s f

/-- **The range of a section of a separated morphism is closed** (PROVEN). -/
theorem isClosed_range_of_section {X Y : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ X}
    [IsSeparated f] (hs : s ≫ f = 𝟙 Y) : IsClosed (Set.range s.base) := by
  haveI := IsClosedImmersion.of_section hs
  exact s.isClosedEmbedding.isClosed_range

/-- **The range of a `K`-point of a scheme is a single point**, `K` a field (PROVEN):
`Spec K` is a one-point space, so the range of any `Spec K ⟶ X` is the singleton on the
image of the unique point. -/
theorem range_eq_singleton_of_spec_field {K : Type u} [Field K] {X : Scheme.{u}}
    (s : Spec (CommRingCat.of K) ⟶ X) :
    ∃ z : X, Set.range s.base = {z} := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ⟨s.base (IsLocalRing.closedPoint K), ?_⟩
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact congrArg _ (Subsingleton.elim w _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-- **The image of a `K`-point that is a section of a separated morphism is a closed
point** (PROVEN, from the two lemmas above). -/
theorem isClosed_singleton_of_section {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of K)} {s : Spec (CommRingCat.of K) ⟶ X} [IsSeparated f]
    (hs : s ≫ f = 𝟙 _) {z : X} (hz : Set.range s.base = {z}) :
    IsClosed ({z} : Set X) :=
  hz ▸ isClosed_range_of_section hs

/-! ### The affineness leaf, and the two sub-leaves it is proven over -/

/-- **The affine line over `K`**, as its structure morphism `𝔸¹_K ⟶ Spec K`.

Only used to say "over `K`" in the two sub-leaves below.  Without it the sub-leaves would
quantify over *ring* maps `K[T] → Γ(X ∖ {z})`, which need not respect the `K`-algebra
structures at all — an adversary could compose with a wild endomorphism of `K` and satisfy
every other clause while breaking properness.  Pinning the triangle over `Spec K` is what
forbids that. -/
noncomputable def affineLineOver (K : Type u) [Field K] :
    Spec (CommRingCat.of (Polynomial K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))

/-- **The affine line is of finite type over its base field** (PROVEN 2026-07-30).

`K[T]` is generated as a `K`-algebra by `T` (`Polynomial.adjoin_X`), which is exactly
`RingHom.FiniteType (algebraMap K K[T])`; `LocallyOfFiniteType` is a
`HasRingHomProperty` for that, so `HasRingHomProperty.Spec_iff` transports it.

This is the side condition of the right-cancellation
`locallyOfFiniteType_of_comp`, and it is the only reason
`isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton` can get
`LocallyOfFiniteType g` out of its `hover` clause. -/
theorem locallyOfFiniteType_affineLineOver (K : Type u) [Field K] :
    LocallyOfFiniteType (affineLineOver K) := by
  rw [affineLineOver, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr
    ⟨⟨{Polynomial.X}, by simp [Polynomial.adjoin_X (R := K)]⟩⟩

/-- **The regular function on `U` that a morphism `U ⟶ 𝔸¹_K` classifies**: the pull-back of the
coordinate `T`.

`Spec K[T]` is affine, so a morphism out of `U` is a ring map `K[T] ⟶ Γ(U, ⊤) ≅ Γ(X, U)`, and it
is determined by the image of `T`.  This is the `f` that the pole argument talks about.

(Moved up here 2026-07-31, from the stalk section where it used to sit: the Riemann–Roch leaf's
decomposition just below has to name it, and a `def` about `𝔸¹` belongs beside `affineLineOver`
rather than among the `stalkClosedPointTo` lemmas.) -/
noncomputable def coordOf {K : Type u} [Field K] {X : Scheme.{u}} (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K))) : Γ(X, U) :=
  (Scheme.Opens.topIso U).hom.hom
    (g.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom Polynomial.X))

/-- **The `K`-algebra structure that `strX` puts on `Γ(X, U)`.**

"Nonconstant" for a section of `Γ(X, U)` means "not integral over `K` for THIS map", and
writing it down is what stops an adversary from reading `K → Γ(X, U)` as some other ring map —
the same freedom `affineLineOver` exists to forbid on the morphism side.  `coordHom_comp_C`
below is the statement that a `K`-morphism `g : U ⟶ 𝔸¹_K` is `structHom`-linear. -/
noncomputable def structHom {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) :
    CommRingCat.of K ⟶ X.presheaf.obj (Opposite.op U) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op

/-- **The restriction `Γ(X, ⊤) ⟶ Γ(X, U)` is `ι.appTop` followed by `topIso`**
(PROVEN 2026-07-31, no sorry).

This is `ι_appLE_top_eq_topIso_inv` and `appLE_top_top_eq_appTop` below, glued by
`Scheme.Hom.map_appLE`; their proofs are repeated inline rather than reused because those two
lemmas are declared *after* the sub-sub-leaf this one serves, and the leaf must precede its own
consumer. -/
theorem res_top_eq_appTop_topIso {X : Scheme.{u}} (U : X.Opens) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
      (Scheme.Opens.ι U).appTop ≫ (Scheme.Opens.topIso U).hom := by
  have h1 : (Scheme.Opens.ι U).appLE U ⊤ (by simp) = (Scheme.Opens.topIso U).inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
    simp only [Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
    congr 1
  have h2 : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) e, f.appLE ⊤ ⊤ e = f.appTop := by
    intro Y Z f e; simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have key : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (Scheme.Opens.topIso U).inv
      = (Scheme.Opens.ι U).appTop := by
    rw [← h1, Scheme.Hom.map_appLE, h2]
  rw [← key, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The classifying ring map `K[T] ⟶ Γ(X, U)` of a morphism `U ⟶ 𝔸¹_K`** — `coordOf` is its
value at `T`, and this packaging is what lets a POLYNOMIAL identity be pushed through it. -/
noncomputable def coordHom {K : Type u} [Field K] {X : Scheme.{u}} (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K))) :
    CommRingCat.of (Polynomial K) ⟶ X.presheaf.obj (Opposite.op U) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv ≫ g.appTop ≫
    (Scheme.Opens.topIso U).hom

/-- **`coordHom` sends `T` to `coordOf`** (PROVEN, `rfl`). -/
theorem coordHom_apply_X {K : Type u} [Field K] {X : Scheme.{u}} (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K))) :
    (coordHom U g).hom Polynomial.X = coordOf U g := rfl

/-- **`coordHom` is `K`-linear, for the `K`-algebra structure `strX` gives `Γ(X, U)`**
(PROVEN 2026-07-31, no sorry) — and this is the ONLY place `hover` is consumed in the
extension argument.

Read on the constants of `K[T]`, the triangle `hover` says exactly that the two ways of
turning a scalar into a section of `Γ(X, U)` — through `𝔸¹_K` and through `Spec K` — agree.
Without it `g` is a morphism of schemes over `ℤ` and its restriction `K → Γ(X, U)` need not be
the structure map at all; see `affineLineOver`. -/
theorem coordHom_comp_C {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hover : g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX) :
    CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K) ≫ coordHom U g =
      structHom strX U := by
  have h := congrArg (fun m : U.toScheme ⟶ Spec (CommRingCat.of K) => m.appTop) hover
  simp only [Scheme.Hom.comp_appTop, affineLineOver] at h
  rw [structHom, ← Category.assoc]
  have hC : (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)) =
      CommRingCat.ofHom (algebraMap K (Polynomial K)) := by
    rw [Polynomial.algebraMap_eq]
  rw [hC, coordHom, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
    res_top_eq_appTop_topIso U]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))).appTop) g.appTop,
    h, Category.assoc]

/-- **EVERY SECTION CLASSIFIES A `K`-MORPHISM TO `𝔸¹_K`** (PROVEN 2026-07-31, no sorry).

The converse of `coordOf`, and the half of the Riemann–Roch leaf that is pure adjunction rather
than mathematics: `Spec` is right adjoint to global sections, so a morphism `U ⟶ Spec K[T]` IS
a ring map `K[T] ⟶ Γ(U, ⊤)`, and one is manufactured from `f` by `Polynomial.eval₂RingHom`
against the structure map.  `ΓSpecIso_inv_ΓSpec_adjunction_homEquiv` computes its `appTop`, and
`ext_to_Spec` — two morphisms into an affine scheme agree as soon as their `appTop`s do — gives
the `≫`-clause from `Polynomial.eval₂_C`.

So a prover of the Riemann–Roch leaf owes only a SECTION, never a morphism. -/
theorem exists_toAffineLine_coordOf_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) (f : Γ(X, U)) :
    ∃ g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)),
      coordOf U g = f ∧ g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX := by
  set cU : CommRingCat.of K ⟶ Γ(U.toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Scheme.Opens.ι U ≫ strX).appTop with hcU
  set φ : CommRingCat.of (Polynomial K) ⟶ Γ(U.toScheme, ⊤) :=
    CommRingCat.ofHom
      (Polynomial.eval₂RingHom cU.hom ((Scheme.Opens.topIso U).inv.hom f)) with hφ
  set g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)) :=
    (ΓSpec.adjunction.homEquiv U.toScheme
      (Opposite.op (CommRingCat.of (Polynomial K)))) φ.op with hg
  have key : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv ≫ g.appTop = φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  have hinner : g.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom Polynomial.X)
      = (Scheme.Opens.topIso U).inv.hom f := by
    rw [← CommRingCat.comp_apply, key, hφ]
    exact Polynomial.eval₂_X _ _
  refine ⟨g, ?_, ?_⟩
  · show (Scheme.Opens.topIso U).hom.hom
      (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom Polynomial.X)) = f
    rw [hinner, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  · refine ext_to_Spec ?_
    show (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (g ≫ affineLineOver K).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Scheme.Opens.ι U ≫ strX).appTop
    rw [Scheme.Hom.comp_appTop, affineLineOver, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, key, ← hcU]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    rw [hφ, Polynomial.algebraMap_eq]
    exact Polynomial.eval₂_C _ _

/-- **A RATIONAL FUNCTION LYING IN EVERY LOCAL RING OF `U` COMES FROM A SECTION ON `U`**
(PROVEN 2026-07-31, no sorry) — i.e. `Γ(X, U) = ⋂_{x ∈ U} 𝒪_{X,x}` inside `K(X)`, for `X`
integral.

This is the bridge between the function-field language, which is what a Riemann–Roch argument
produces, and the sheaf-section language, which is what this file's consumers want.  It is
absent from the pin.

The proof is the sheaf axiom over the cover of `U` by neighbourhoods on which `f` is a section:
each `x ∈ U` contributes an open `V x ∋ x` and `t x ∈ Γ(X, V x)` with `germ_x (t x) = f`
(`TopCat.Presheaf.exists_germ_eq`, intersected with `U`).  Compatibility is where integrality is
used TWICE: any two of the `V x` MEET, because a nonempty open of an irreducible space is dense
(`nonempty_preirreducible_inter`), and on the overlap the two restrictions have the same image in
`K(X)` — namely `f` — so they are equal because `Scheme.germToFunctionField_injective` is
injective on a nonempty open.  Without irreducibility the overlap could be empty and the argument
would say nothing.

`exists_res_eq_of_germ_eq` below is the special two-open case, cut earlier the same day for the
pole argument; this is the general one and does not subsume it (that one glues two given sections
agreeing at a point, this one glues a family produced from a single rational function). -/
theorem exists_germToFunctionField_eq_of_forall_isInteger {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (f : X.functionField)
    (h : ∀ x ∈ U, ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = f) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  classical
  -- choose, for each point of `U`, an open neighbourhood inside `U` and a section equal to `f`
  have hchoice : ∀ i : ↥U, ∃ (V : X.Opens) (_ : (i : X) ∈ V) (_ : V ≤ U) (t : Γ(X, V)),
      ∀ (_ : Nonempty V), X.germToFunctionField V t = f := by
    rintro ⟨x, hxU⟩
    obtain ⟨a, ha⟩ := h x hxU
    obtain ⟨W, hxW, t, ht⟩ := X.presheaf.exists_germ_eq a
    refine ⟨W ⊓ U, ⟨hxW, hxU⟩, inf_le_right,
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op t, fun hV => ?_⟩
    haveI : Nonempty (W ⊓ U : X.Opens) := hV
    have hx' : x ∈ W ⊓ U := ⟨hxW, hxU⟩
    have h1 : X.presheaf.germ (W ⊓ U) x hx'
        (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op t) = a := by
      rw [X.presheaf.germ_res_apply]; exact ht
    have h2 := Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := W ⊓ U) hx'
      (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op t)
    rw [h1, ha] at h2
    exact h2.symm
  choose V hxV hVU t ht using hchoice
  -- the sections agree on overlaps, because both map to `f` in the function field
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V t := by
    intro i j
    haveI : Nonempty (V i) := ⟨⟨(i : X), hxV i⟩⟩
    haveI : Nonempty (V j) := ⟨⟨(j : X), hxV j⟩⟩
    have hmeet : ((V i ⊓ V j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
        ⟨(i : X), hxV i⟩ ⟨(j : X), hxV j⟩
    haveI : Nonempty ((V i ⊓ V j : X.Opens)) := ⟨⟨hmeet.choose, hmeet.choose_spec⟩⟩
    refine X.germToFunctionField_injective (V i ⊓ V j) ?_
    have e1 : X.germToFunctionField (V i ⊓ V j)
        (X.presheaf.map (Opens.infLELeft (V i) (V j)).op (t i)) = f := by
      rw [X.presheaf.germ_res_apply]
      exact ht i inferInstance
    have e2 : X.germToFunctionField (V i ⊓ V j)
        (X.presheaf.map (Opens.infLERight (V i) (V j)).op (t j)) = f := by
      rw [X.presheaf.germ_res_apply]
      exact ht j inferInstance
    exact e1.trans e2.symm
  -- glue over the cover
  have hcov : U ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨s, hs, -⟩ :=
    X.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcov t hcompat
  refine ⟨s, ?_⟩
  obtain ⟨u, hu⟩ : ((U : Set X)).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty U›
    exact ⟨i.1, i.2⟩
  set i : ↥U := ⟨u, hu⟩ with hi
  haveI : Nonempty (V i) := ⟨⟨(i : X), hxV i⟩⟩
  have hti := ht i inferInstance
  rw [← hti, ← hs i]
  exact (X.presheaf.germ_res_apply _ _ _ s).symm

/-- **The `K`-algebra structure `strX` puts on the FUNCTION FIELD** — `structHom` at `⊤`,
followed into `K(X)`.  It is what "nonconstant" is measured against in the leaf below. -/
noncomputable def functionFieldHom {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace X]
    [Nonempty (⊤ : X.Opens)] : CommRingCat.of K ⟶ X.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop ≫ X.germToFunctionField ⊤

/-- **`structHom` at any `U` agrees with `functionFieldHom`** (PROVEN, no sorry): one
`TopCat.Presheaf.germ_res`, since a germ at the generic point does not see the restriction. -/
theorem structHom_comp_germToFunctionField {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace X]
    [Nonempty (⊤ : X.Opens)] (U : X.Opens) [Nonempty U] :
    structHom strX U ≫ X.germToFunctionField U = functionFieldHom strX := by
  rw [structHom, functionFieldHom, Category.assoc, Category.assoc]
  congr 2
  exact X.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) _ _

/-- **Nonconstancy transports from the function field back to a section** (PROVEN, no sorry) —
the direction the decomposition needs, and the easy one: a monic equation satisfied by the
section is carried into `K(X)` by the ring map `germToFunctionField`.  (The converse would need
injectivity, which is true but not required here.) -/
theorem notIsIntegralElem_of_germToFunctionField {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [IrreducibleSpace X]
    [Nonempty (⊤ : X.Opens)] (U : X.Opens) [Nonempty U] (s : Γ(X, U))
    (hf : ¬ (functionFieldHom strX).hom.IsIntegralElem (X.germToFunctionField U s)) :
    ¬ (structHom strX U).hom.IsIntegralElem s := by
  rintro ⟨p, hpm, hp0⟩
  refine hf ⟨p, hpm, ?_⟩
  have hc : ((X.germToFunctionField U).hom.comp (structHom strX U).hom) =
      (functionFieldHom strX).hom :=
    congrArg CommRingCat.Hom.hom (structHom_comp_germToFunctionField strX U)
  rw [← hc, ← Polynomial.hom_eval₂, hp0, map_zero]

/-- **RIEMANN–ROCH, AND AFTER TWO CUTS THIS IS THE WHOLE OF WHAT IS ASKED OF IT: a NONCONSTANT
RATIONAL FUNCTION WITH POLES ONLY AT `z`** (sorry leaf, and the ONLY one left in this file).

No morphism, no `𝔸¹`, no quasi-finiteness, and since 2026-07-31 no SHEAF SECTION either: one
element `f` of the FUNCTION FIELD `K(X)`, lying in the local ring at every point other than `z`,
and not integral over `K`.  On a geometrically connected `X` "not integral over `K`" is exactly
"nonconstant", since the algebraic closure of `K` in `K(X)` is then `K` itself — so this is the
classical statement and nothing more.

**This is exactly `L(n·[z]) ⊋ K` for some `n`**, phrased without naming `n`: "regular away from
`z`" is the first clause and "nonconstant" is the second.  It is the shape an `ord`-based
argument produces directly, which is why the cut is here — see the inventory below, and note that
the first clause is equivalent to `0 ≤ Scheme.ord f x` for all `x ≠ z`, the stalks being DVRs
(`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`).  Either form may be used; the
`IsInteger` form is stated because it needs no coheight side conditions.

TRUE and classical.  `X` is a smooth proper geometrically connected curve over `K`, so it has a
genus `g`, and Riemann–Roch gives `dim_K L(n·[z]) = n·deg[z] − g + 1` for `n·deg[z] > 2g − 2`.
In particular `L(n·[z]) ⊋ L(0) ⊇ K` for `n` large, and any element of the difference is a
nonconstant function regular on `X ∖ {z}`.

**`hconn` IS LOAD-BEARING** — see the counterexample in
`isAffineOpen_compl_singleton_of_isSmoothProperCurve`'s docstring: on a disjoint union of two
copies of a curve, punctured in the first copy only, every regular function is constant on the
whole second copy, so `Γ(X, X ∖ {z})` is a product with a field factor and every element is
integral over `K`.

**`SmoothOfRelativeDimension 1` IS LOAD-BEARING**: at relative dimension two, `X ∖ {z}` has the
same global sections as the proper `X`, a finite extension of `K`, so every section is integral.

**`IsProper strX` IS LOAD-BEARING** in the same way — on a non-proper curve the statement is
still true but for a different reason, and the intended proof consumes properness through the
genus.

NOT VACUOUS: for `X` the projective model of an elliptic curve over `ℚ` and `z` the point at
infinity, `x` (the first Weierstrass coordinate) is such a rational function.

## WHAT THE PIN ACTUALLY HAS, read rather than grepped (2026-07-31)

The older note here said only "Riemann–Roch is absent".  That is true and useless on its own;
below is the inventory a prover needs, and the headline is that **ORDERS OF VANISHING ARE
ALREADY IN THE PIN, and every hypothesis they need is already discharged for this file's
curves.**

PRESENT — `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`, for
`[IsIntegral X] [IsLocallyNoetherian X]`:

* `AlgebraicGeometry.Scheme.ord (f : X.functionField) (z : X) : ℤ`, the order of vanishing at a
  point of codimension one, junk value `0` when `f = 0` or `coheight z ≠ 1`;
* `ord_mul`, `ord_add` (this one wants `IsDiscreteValuationRing (X.presheaf.stalk x)`),
  `ord_of_isUnit`, `le_ord_iff`, `ord_le_ord_iff`, `ord_eq_zero_of_coheight_neq_one`, `ord_zero`,
  `ord_le_smul`, and `ordHom` into `ℤᵐ⁰`.

PRESENT — `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`:

* `AlgebraicCycle X R := Function.locallyFinsupp X R` — a cycle is a function on points with
  locally finite support, using generic points to index irreducible closed subsets;
* pushforward `AlgebraicCycle.map` along a quasi-compact morphism, with `mapCoeff` built from
  `Scheme.Hom.residueDegree`.

AND EVERY SIDE CONDITION IS FREE HERE, which is the part worth knowing before starting:
`IsIntegral X` is `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`;
`IsLocallyNoetherian X` is `LocallyOfFiniteType.isLocallyNoetherian strX` (used twice in this
file already); the DVR hypothesis of `ord_add` is
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` (`CurveExtension.lean`); and the
codimension-one condition `coheight z = 1` holds at exactly the non-generic points, because
`isClosed_singleton_of_ne_genericPoint` below makes every one of them closed and
`ringKrullDim_stalk_le_of_smoothOfRelativeDimension` bounds the chains.

ABSENT, verified by reading and not only by name-grep — every `Divisor` hit under
`Mathlib/AlgebraicGeometry/` and `Mathlib/RingTheory/OrderOfVanishing/` is `nonZeroDivisors`:

* no `principalDivisor` / `div f` packaging `ord f ·` as an `AlgebraicCycle`, and no proof that
  its support is locally finite;
* no degree homomorphism on cycles, no divisor class group, no `genus`;
* no coherent-sheaf cohomology, and `grep -ri riemann` over all of `Mathlib` returns nothing in
  algebraic geometry.  `~/cs/FLT` has none of it either.

So the VALUATION-THEORETIC half of divisor theory is done and the GLOBAL half — `deg`, finiteness
of `L(D)`, and the Riemann inequality — is what has to be built.  A prover should start by
defining `L(n·[z])` directly as `{f : X.functionField | 0 ≤ ord f y for y ≠ z}` using `ord`, not
by building an order of vanishing from scratch.

ONE BRIDGE THIS LEAF WILL NEED, and it is not in the pin either: a rational function whose `ord`
is `≥ 0` at every point of an open `U` is the germ of an actual SECTION in `Γ(X, U)` — i.e.
`Γ(X, U) = ⋂_{x ∈ U} 𝒪_{X,x}` inside `K(X)`.  `exists_res_eq_of_germ_eq` below is the
two-open case of the gluing that argument needs; the general case is the same
`TopCat.Sheaf.existsUnique_gluing'` over an affine cover, plus the commutative-algebra fact that
a noetherian domain is the intersection of its localisations at primes. -/
theorem exists_forall_isInteger_notIsIntegralElem_functionField
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX] [IsIntegral X]
    [Nonempty (⊤ : X.Opens)]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X)) :
    ∃ f : X.functionField,
      (∀ x ∈ (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens),
        ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f) ∧
      ¬ (functionFieldHom strX).hom.IsIntegralElem f :=
  sorry

/-- **The same thing as a SECTION of `Γ(X, X ∖ {z})`** (PROVEN 2026-07-31 over the leaf above and
`exists_germToFunctionField_eq_of_forall_isInteger`).

This used to be the Riemann–Roch leaf itself.  It is now three lines: take the rational function,
glue it into a section — every hypothesis of the gluing bridge is exactly the leaf's first clause
— and transport nonconstancy along `germToFunctionField`.  The point of the cut is that a
Riemann–Roch prover now never touches a sheaf. -/
theorem exists_notIsIntegralElem_section_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X)) :
    ∃ f : Γ(X, (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)),
      ¬ (structHom strX (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)).hom.IsIntegralElem f := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  haveI : Infinite X := infinite_of_smoothOfRelativeDimension_one strX
  haveI : Nonempty (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) := by
    have h : (({z}ᶜ : Set X)).Nonempty :=
      ((Set.Finite.infinite_compl (Set.finite_singleton z)).nonempty)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  obtain ⟨f, hint, hni⟩ :=
    exists_forall_isInteger_notIsIntegralElem_functionField strX hconn hz
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_forall_isInteger
    (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) f hint
  exact ⟨s, notIsIntegralElem_of_germToFunctionField strX _ s (by rw [hs]; exact hni)⟩

/-- **`coordHom` IS `eval₂` AGAINST `structHom` AND `coordOf`** (PROVEN 2026-07-31, no sorry).

A ring map out of `K[T]` is determined by what it does to `K` and to `T` (`Polynomial.ringHom_ext`),
and `coordHom_comp_C`/`coordHom_apply_X` say what those are.  So a polynomial identity satisfied by
`coordOf U g` transports to the kernel of `coordHom U g` and back. -/
theorem coordHom_apply_eq_eval₂ {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hover : g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX) (p : Polynomial K) :
    (coordHom U g).hom p =
      Polynomial.eval₂ (structHom strX U).hom (coordOf U g) p := by
  have hsplit : (coordHom U g).hom = Polynomial.eval₂RingHom
      ((coordHom U g).hom.comp (Polynomial.C : K →+* Polynomial K))
      ((coordHom U g).hom Polynomial.X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  have hcc : (coordHom U g).hom.comp (Polynomial.C : K →+* Polynomial K) =
      (structHom strX U).hom :=
    congrArg CommRingCat.Hom.hom (coordHom_comp_C strX U g hover)
  conv_lhs => rw [hsplit]
  show Polynomial.eval₂ _ _ p = _
  rw [hcc, coordHom_apply_X]

/-- **A NONCONSTANT SECTION SENDS THE GENERIC POINT TO THE GENERIC POINT OF `𝔸¹_K`**
(PROVEN 2026-07-31, no sorry) — the exact CONVERSE of MOVE 3 of
`false_of_res_eq_coordOf_of_locallyQuasiFinite` far below, and proven off the same
`basicOpen`/`PrimeSpectrum.mem_basicOpen` chain.

If a polynomial `p` lay in the prime `g(η)` then `T`'s pull-back would be a non-unit in the stalk
at `η`; that stalk is the FUNCTION FIELD, so a non-unit there is `0`, and germs are injective on
an integral scheme, so `p` would already vanish in `Γ(X, U)`.  Over a field the leading
coefficient can be inverted, so a nonzero such `p` would exhibit `coordOf U g` as integral over
`K` — which is exactly what `htr` forbids. -/
theorem base_genericPoint_asIdeal_eq_bot {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) [IsIntegral U.toScheme]
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hover : g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX)
    (htr : ¬ (structHom strX U).hom.IsIntegralElem (coordOf U g)) :
    (g.base (genericPoint U.toScheme)).asIdeal = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  by_contra hpne
  have hnm : genericPoint U.toScheme ∉ (U.toScheme).basicOpen
      (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p)) := by
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact fun h => (PrimeSpectrum.mem_basicOpen p _).mp h hp
  rw [Scheme.mem_basicOpen_top] at hnm
  have hzero : g.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p) = 0 := by
    refine germ_injective_of_isIntegral U.toScheme (U := (⊤ : (U.toScheme).Opens))
      (genericPoint U.toScheme) trivial ?_
    rw [map_zero]
    exact not_not.mp fun _ => hnm (isUnit_iff_ne_zero.mpr (by simpa using ‹_›))
  have hco : (coordHom U g).hom p = 0 := by
    have hexp : (coordHom U g).hom p = (Scheme.Opens.topIso U).hom.hom
        (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p)) := rfl
    rw [hexp, hzero, map_zero]
  rw [coordHom_apply_eq_eval₂ strX U g hover] at hco
  refine htr ⟨p * Polynomial.C (p.leadingCoeff)⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv hpne, ?_⟩
  rw [Polynomial.eval₂_mul, hco, zero_mul]

/-- **EVERY POINT OF A SMOOTH CURVE OTHER THAN THE GENERIC POINT IS CLOSED** (cut 2026-07-31 out
of `locallyQuasiFinite_of_notIsIntegralElem_coordOf` just below, and **PROVEN the same day, no
sorry**).

This is DIMENSION ONE, stated topologically, and it mentions no morphism to `𝔸¹`, no polynomial
and no quasi-finiteness.  It arguably belongs in `CurveExtension.lean` beside the other
dimension facts; it is here only because that is where its consumer is.

## PROOF — a three-term specialization chain against the stalk's Krull dimension

Suppose `x` is neither generic nor closed.  Then `closure {x} ⊋ {x}`, so there is `w ≠ x` with
`x ⤳ w`, and with `η := genericPoint X` the chain `η ⤳ x ⤳ w` has THREE DISTINCT points:
`η ≠ x` is the hypothesis, `w ≠ x` is the choice, and `η ≠ w` because `x ⤳ η` together with
`η ⤳ x` forces `x = η` by `Specializes.antisymm` in a `T0` space.

**The chain is then read off in an AFFINE OPEN rather than in the stalk**, and that is the one
design decision worth recording, because the obvious route does not work: the pin has
`Scheme.range_fromSpecStalk` (the range of `Spec 𝒪_{X,w} ⟶ X` is the set of generizations of
`w`), but NO injectivity lemma for `Scheme.fromSpecStalk`, so the three points cannot be lifted
that way without proving injectivity first.  Instead pick an affine open `V ∋ w`; every
generization of `w` lies in it (`Specializes.mem_open`), so `η, x, w ∈ V`, and
`IsAffineOpen.primeIdealOf` — which IS the affine iso `V ≅ Spec Γ(X, V)` on points, hence
continuous, and injective because `IsAffineOpen.fromSpec_primeIdealOf` is a retraction — turns
the chain into a strict chain of three primes of `Γ(X, V)`, via
`PrimeSpectrum.le_iff_specializes`.  Specialization inside `V` is specialization in `X`
(`Topology.IsInducing.specializes_iff` for the open immersion).

Two applications of `Ideal.height_add_one_le_of_lt_of_isPrime` then give
`2 ≤ (primeIdealOf w).asIdeal.height`; `IsLocalization.AtPrime.ringKrullDim_eq_height` together
with `IsAffineOpen.isLocalization_stalk` identifies that height with
`ringKrullDim 𝒪_{X,w}`; and `ringKrullDim_stalk_le_of_smoothOfRelativeDimension`
(`CurveExtension.lean`) bounds it by `1`.

**`SmoothOfRelativeDimension 1` IS LOAD-BEARING and the statement is FALSE without it**: on a
smooth SURFACE the generic point of a curve on it is neither generic nor closed.

**`IsIntegral X` IS LOAD-BEARING for the statement to be about anything** — without
irreducibility there is no `genericPoint X` to except. -/
theorem isClosed_singleton_of_ne_genericPoint {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 strX] [IsIntegral X]
    {x : X} (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  by_contra hcl
  -- a point `w` strictly below `x`
  obtain ⟨w, hwc, hwx⟩ : ∃ w ∈ closure ({x} : Set X), w ≠ x := by
    by_contra h
    refine hcl ?_
    have hsub : closure ({x} : Set X) ⊆ {x} := by
      intro y hy
      by_contra hne
      exact h ⟨y, hy, hne⟩
    have hce : closure ({x} : Set X) = {x} := subset_antisymm hsub subset_closure
    rw [← hce]
    exact isClosed_closure
  have hxw : x ⤳ w := by rwa [specializes_iff_mem_closure]
  -- and the generic point strictly above
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hgw : genericPoint X ⤳ w := hgx.trans hxw
  have hgne : genericPoint X ≠ w := by
    intro h
    exact hx ((hgx.antisymm (h ▸ hxw)).eq).symm
  -- an affine open around `w`; it contains both generizations
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  have hxV : x ∈ V := hxw.mem_open V.isOpen hwV
  have hgV : genericPoint X ∈ V := hgw.mem_open V.isOpen hwV
  -- the three points, as points of `V`
  set ηV : Scheme.Opens.toScheme V := ⟨genericPoint X, hgV⟩ with hηV
  set xV : Scheme.Opens.toScheme V := ⟨x, hxV⟩ with hxVdef
  set wV : Scheme.Opens.toScheme V := ⟨w, hwV⟩ with hwVdef
  have hind : Topology.IsInducing (Scheme.Opens.ι V).base :=
    (Scheme.Opens.ι V).isOpenEmbedding.isInducing
  have hsp1 : ηV ⤳ xV := hind.specializes_iff.mp
    (show (Scheme.Opens.ι V).base ηV ⤳ (Scheme.Opens.ι V).base xV from hgx)
  have hsp2 : xV ⤳ wV := hind.specializes_iff.mp
    (show (Scheme.Opens.ι V).base xV ⤳ (Scheme.Opens.ι V).base wV from hxw)
  -- transport to `Spec Γ(X, V)` along the affine iso
  have hinj : Function.Injective (hV.primeIdealOf) := by
    intro a b hab
    have := congrArg hV.fromSpec hab
    rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
    exact Subtype.ext this
  have hcont : Continuous (hV.primeIdealOf) := by
    show Continuous fun a => hV.isoSpec.hom.base a
    exact hV.isoSpec.hom.base.hom.continuous
  have hle1 : hV.primeIdealOf ηV ≤ hV.primeIdealOf xV :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp1.map hcont)
  have hle2 : hV.primeIdealOf xV ≤ hV.primeIdealOf wV :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp2.map hcont)
  have hne1 : hV.primeIdealOf ηV ≠ hV.primeIdealOf xV := by
    intro h
    exact hx (congrArg Subtype.val (hinj h)).symm
  have hne2 : hV.primeIdealOf xV ≠ hV.primeIdealOf wV := by
    intro h
    exact hwx (congrArg Subtype.val (hinj h)).symm
  -- so a strict chain of three primes, i.e. height at least two at `w`
  haveI : (hV.primeIdealOf ηV).asIdeal.IsPrime := (hV.primeIdealOf ηV).isPrime
  haveI : (hV.primeIdealOf xV).asIdeal.IsPrime := (hV.primeIdealOf xV).isPrime
  haveI : (hV.primeIdealOf wV).asIdeal.IsPrime := (hV.primeIdealOf wV).isPrime
  have hlt1 : (hV.primeIdealOf ηV).asIdeal < (hV.primeIdealOf xV).asIdeal :=
    lt_of_le_of_ne hle1 fun h => hne1 (PrimeSpectrum.ext h)
  have hlt2 : (hV.primeIdealOf xV).asIdeal < (hV.primeIdealOf wV).asIdeal :=
    lt_of_le_of_ne hle2 fun h => hne2 (PrimeSpectrum.ext h)
  have hh1 : (hV.primeIdealOf ηV).asIdeal.height + 1 ≤ (hV.primeIdealOf xV).asIdeal.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt1
  have hh2 : (hV.primeIdealOf xV).asIdeal.height + 1 ≤ (hV.primeIdealOf wV).asIdeal.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt2
  have hh : (2 : ℕ∞) ≤ (hV.primeIdealOf wV).asIdeal.height := by
    have h1 : (1 : ℕ∞) ≤ (hV.primeIdealOf xV).asIdeal.height := le_trans (by simp) hh1
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (hV.primeIdealOf xV).asIdeal.height + 1 := by gcongr
      _ ≤ _ := hh2
  -- but the stalk at `w` is that localization, and it has dimension at most one
  letI : Algebra Γ(X, V) (X.presheaf.stalk w) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := V) ⟨w, hwV⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk w) (hV.primeIdealOf wV).asIdeal :=
    hV.isLocalization_stalk ⟨w, hwV⟩
  have heq : ringKrullDim (X.presheaf.stalk w) =
      ((hV.primeIdealOf wV).asIdeal.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  have hle : ringKrullDim (X.presheaf.stalk w) ≤ (1 : WithBot ℕ∞) :=
    ringKrullDim_stalk_le_of_smoothOfRelativeDimension (n := 1) strX w
  rw [heq] at hle
  have hfin : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) :=
    le_trans (WithBot.coe_le_coe.mpr hh) hle
  simp at hfin

/-- **A CLOSED SET OF CLOSED POINTS IN A NOETHERIAN SCHEME IS FINITE** (PROVEN 2026-07-31, no
sorry) — pure topology.

A noetherian space writes every closed set as a FINITE union of irreducible closed sets
(`NoetherianSpace.exists_finite_set_isClosed_irreducible`); a scheme is sober, so each piece is
the closure of a point of itself; and that point is closed by hypothesis, so each piece is a
singleton. -/
theorem finite_of_isClosed_of_forall_isClosed_singleton {W : Scheme.{u}} [NoetherianSpace W]
    {Z : Set W} (hZ : IsClosed Z) (h : ∀ x ∈ Z, IsClosed ({x} : Set W)) : Z.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hxt : x ∈ t := hx ▸ subset_closure rfl
  have ht' : t = {x} := by rw [← hx]; exact (h x (Set.mem_sUnion_of_mem hxt ht)).closure_eq
  rw [ht']
  exact Set.finite_singleton x

/-- **A NONCONSTANT SECTION CLASSIFIES A QUASI-FINITE MORPHISM** (sorry leaf, cut 2026-07-31 out
of `exists_locallyQuasiFinite_toAffineLine_compl_singleton` below).

NO RIEMANN–ROCH, NO GENUS, NO DIVISOR, and no puncture: this is the commutative algebra of a
curve.  It is stated at a general open `U` precisely because nothing about `{z}ᶜ` is used.

TRUE.  Pick an affine open `V ⊆ U`.  `X` is integral
(`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`), so `A := Γ(X, V)` is a
domain, and it is a finite-type `K`-algebra of Krull dimension one — `SmoothOfRelativeDimension
1` gives exactly that, via
`ringKrullDim_le_of_isStandardSmoothOfRelativeDimension` in `CurveExtension.lean`.  `f|_V` is
transcendental over `K` because `f` is and `Γ(X, V) ↪ K(X)` is injective on an integral scheme
(`germ_injective_of_isIntegral`).  So `K[T] ↪ A` with `A` a one-dimensional finite-type domain,
whence `A` is quasi-finite (indeed finite, by Noether normalisation) over `K[T]`, which is
`RingHom.QuasiFinite` of `g.appLE`, which is `LocallyQuasiFinite` by the
`HasRingHomProperty` instance for it.

**WHAT THE PROVER SHOULD LOOK AT FIRST**, because it may collapse the work: the pin has
`Algebra.QuasiFinite` and `Module.Finite.of_quasiFinite` (used already in
`infinite_of_smoothOfRelativeDimension_one`), and
`Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` reduces `RingHom.QuasiFinite` to
FINITE FIBRES of `Spec`.  Combined with `locallyQuasiFinite_iff_finite_preimage_singleton`
(which wants `IsOfFiniteType g`, free here from `hover` and
`locallyOfFiniteType_affineLineOver`) the whole leaf may be provable topologically: the fibre
over a point of `𝔸¹_K` is a proper closed subset of the irreducible curve `U`, since the
generic point is not in it — `f` transcendental is exactly the statement that `g` does not send
the generic point of `U` to a closed point, which is the CONVERSE of MOVE 3 of
`false_of_res_eq_coordOf_of_locallyQuasiFinite` below and can be read off the same
`basicOpen`/`PrimeSpectrum.mem_basicOpen` chain.

**`htr` IS LOAD-BEARING and the statement is FALSE without it**: `g` constant at `0` is a
`K`-morphism on an infinite `U`, and its single fibre is all of `U`.

**`hconn` IS LOAD-BEARING**, through `IsIntegral X`: on a reducible `X` the section may be
transcendental on one component and constant on another, and the fibre over that constant value
contains a whole component.

**`Nonempty ↥U` IS LOAD-BEARING for the statement to be about anything**; it is free at the
call site, `U = {z}ᶜ` on an infinite `X`. -/
theorem locallyQuasiFinite_of_notIsIntegralElem_coordOf
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    (U : X.Opens) [Nonempty ↥U]
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hover : g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX)
    (htr : ¬ (structHom strX U).hom.IsIntegralElem (coordOf U g)) :
    LocallyQuasiFinite g := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : Nonempty ↥(U.toScheme) := inferInstanceAs (Nonempty ↥U)
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion (Scheme.Opens.ι U)
  haveI := locallyOfFiniteType_affineLineOver K
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace strX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
  haveI : IsNoetherian X := ⟨⟩
  haveI : NoetherianSpace U.toScheme := by
    show NoetherianSpace (U : Set X)
    infer_instance
  haveI : LocallyOfFiniteType (g ≫ affineLineOver K) := by rw [hover]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (affineLineOver K)
  haveI : QuasiCompact g := inferInstance
  -- every point of `U` other than its generic point is closed, transported from `X`
  have hcl : ∀ x : U.toScheme, x ≠ genericPoint U.toScheme → IsClosed ({x} : Set U.toScheme) := by
    intro x hxne
    have hinj : Function.Injective (Scheme.Opens.ι U).base :=
      (Scheme.Opens.ι U).isOpenEmbedding.injective
    have hgen : (Scheme.Opens.ι U).base (genericPoint U.toScheme) = genericPoint X :=
      genericPoint_eq_of_isOpenImmersion (Scheme.Opens.ι U)
    have hne : (Scheme.Opens.ι U).base x ≠ genericPoint X := by
      rw [← hgen]; exact fun h => hxne (hinj h)
    have hclX : IsClosed ({(Scheme.Opens.ι U).base x} : Set X) :=
      isClosed_singleton_of_ne_genericPoint strX hne
    have hpre : ({x} : Set U.toScheme)
        = (Scheme.Opens.ι U).base ⁻¹' {(Scheme.Opens.ι U).base x} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h], fun h => hinj h⟩
    rw [hpre]
    exact hclX.preimage (Scheme.Opens.ι U).base.hom.continuous
  have hbot := base_genericPoint_asIdeal_eq_bot strX U g hover htr
  rw [locallyQuasiFinite_iff_finite_preimage_singleton]
  intro y
  by_cases hy : y = g.base (genericPoint U.toScheme)
  · -- the fibre over the GENERIC point of `𝔸¹_K` can only be the generic point of `U`, because
    -- a closed point of `U` maps to a closed point and `(0)` is not closed in `Spec K[T]`.
    refine Set.Finite.subset (Set.finite_singleton (genericPoint U.toScheme)) ?_
    intro x hx
    by_contra hxne
    have hgx : g.base x = y := hx
    have hxcl : x ∈ closedPoints U.toScheme := hcl x hxne
    have hycl : IsClosed ({y} : Set (Spec (CommRingCat.of (Polynomial K)))) := by
      have h1 := g.closePoints_subset_preimage_closedPoints hxcl
      rw [← hgx]
      exact h1
    have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hycl
    rw [hy, hbot] at hmax
    have hXne : (Ideal.span {(Polynomial.X : Polynomial K)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Polynomial.X_ne_zero
    have htop : Ideal.span {(Polynomial.X : Polynomial K)} = ⊤ := by
      by_contra hne
      exact hXne (hmax.eq_of_le hne bot_le).symm
    exact Polynomial.not_isUnit_X (Ideal.span_singleton_eq_top.mp htop)
  · -- otherwise `y` is a CLOSED point, so the fibre is closed and misses the generic point
    have hyne : y.asIdeal ≠ ⊥ := by
      intro h
      exact hy (PrimeSpectrum.ext (by rw [h, hbot]))
    haveI : y.asIdeal.IsMaximal := _root_.IsPrime.to_maximal_ideal hyne
    have hycl : IsClosed ({y} : Set (Spec (CommRingCat.of (Polynomial K)))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr ‹_›
    refine finite_of_isClosed_of_forall_isClosed_singleton
      (hycl.preimage g.base.hom.continuous) fun x hx => hcl x ?_
    intro hxg
    exact hy (by rw [← hxg]; exact (Set.mem_singleton_iff.mp hx).symm)

/-- **RIEMANN–ROCH: a nonconstant regular function on the punctured curve** (cut 2026-07-28 out
of `isAffineOpen_compl_singleton_of_isSmoothProperCurve`; **DECOMPOSED and PROVEN over its two
sub-leaves 2026-07-31**, having been a bare `sorry` until then).

This is the ONLY place Riemann–Roch enters the affineness statement.  Concretely it asks
for a `K`-morphism `g : X ∖ {z} ⟶ 𝔸¹_K` with finite fibres — equivalently, for a
nonconstant `f ∈ Γ(X, X ∖ {z})`, i.e. a rational function on `X` regular away from `z`.

TRUE and classical.  `X` is a smooth proper geometrically connected curve over `K`, so it
has a genus `g`, and Riemann–Roch gives `dim_K L(n·[z]) = n·deg[z] − g + 1` for
`n·deg[z] > 2g − 2`.  In particular `L(n·[z]) ⊋ L(0) ⊇ K` for `n` large, and any element of
the difference is a nonconstant function regular on `X ∖ {z}`.  Its fibres over `𝔸¹` are
proper closed subsets of the integral curve `X ∖ {z}`, hence finite, which is
`LocallyQuasiFinite`.

## DECOMPOSED 2026-07-31 — and the cut separates Riemann–Roch from everything else

The three paragraphs of that sketch are three different kinds of work, and only the middle one
is Riemann–Roch.  They are now three declarations, and this one is proven over them in four
lines:

* `exists_notIsIntegralElem_section_compl_singleton` — **the Riemann–Roch leaf**, and after the
  cut it asks for a SECTION and nothing else: one element of `Γ(X, X ∖ {z})` not integral over
  `K`.  No morphism, no `𝔸¹`, no quasi-finiteness.
* `exists_toAffineLine_coordOf_eq` — **PROVEN, no sorry**: every section classifies a
  `K`-morphism to `𝔸¹_K`.  This is the whole of the "package it as a morphism" work, and it is
  pure `Γ ⊣ Spec` adjunction; it is also what discharges the `≫`-clause below.
* `locallyQuasiFinite_of_notIsIntegralElem_coordOf` — **the second leaf**: nonconstant implies
  quasi-finite.  Commutative algebra of a one-dimensional finite-type domain, with no
  Riemann–Roch in it, and stated at a general open because the puncture is irrelevant to it.

So a prover of Riemann–Roch never has to touch a scheme morphism, and a prover of
quasi-finiteness never has to touch a genus.  The two are independent and can have separate
owners.

**Why `LocallyQuasiFinite` rather than "nonconstant".**  The pin has no notion of a
nonconstant morphism, and quasi-finiteness is the form Zariski's main theorem consumes
directly.  On an integral curve the two agree: a constant morphism has a one-point image
with infinite fibre, and `X ∖ {z}` is infinite by
`infinite_of_smoothOfRelativeDimension_one`.  That equivalence is no longer folklore in this
file: the ⟸ direction is the second sub-leaf, and the ⟹ direction is PROVEN as
`false_of_res_eq_coordOf_of_locallyQuasiFinite` further down.

**`hconn` IS LOAD-BEARING** — see the counterexample in
`isAffineOpen_compl_singleton_of_isSmoothProperCurve`'s docstring: on a disjoint union of
two copies of a curve, punctured in the first copy only, any regular function is constant on
the whole second copy, so no quasi-finite `g` exists.

**`SmoothOfRelativeDimension 1` IS LOAD-BEARING**: at relative dimension two, `X ∖ {z}` has
the same global sections as the proper `X` (a finite extension of `K`), so every `g` is
constant and none is quasi-finite.

**The `≫`-clause IS LOAD-BEARING**: without it `g` is only a morphism of schemes over `ℤ`,
and its restriction `K → Γ(X ∖ {z})` need not be the structure map, which breaks the
finite-type hypotheses of the sibling leaf.  See `affineLineOver`.

NOT VACUOUS: for `X` the projective model of an elliptic curve over `ℚ` and `z` the point at
infinity, `x` (the first Weierstrass coordinate) is such a function.

WHAT WOULD REFUTE THE "MISSING FROM THE PIN" DIAGNOSIS: a Riemann–Roch theorem, a genus, or
a theory of linear systems, anywhere in `Fermat/`, `.lake/packages/mathlib` or `~/cs/FLT`.
Re-searched 2026-07-31: absent from all three; see the Riemann–Roch sub-leaf's docstring for
the sharper form of that search, which does turn up divisors. -/
theorem exists_locallyQuasiFinite_toAffineLine_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X)) :
    ∃ g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)),
      LocallyQuasiFinite g ∧
        g ≫ affineLineOver K =
          Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : Infinite X := infinite_of_smoothOfRelativeDimension_one strX
  haveI : Infinite ↥(⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) :=
    (Set.Finite.infinite_compl (Set.finite_singleton z)).to_subtype
  obtain ⟨f, hf⟩ := exists_notIsIntegralElem_section_compl_singleton strX hconn hz
  obtain ⟨g, hcoord, hover⟩ := exists_toAffineLine_coordOf_eq strX _ f
  exact ⟨g, locallyQuasiFinite_of_notIsIntegralElem_coordOf strX hconn _ g hover
    (hcoord ▸ hf), hover⟩

/-! ### The classifying local homomorphism of a `Spec (local ring)`-point, and its naturality

`Scheme.stalkClosedPointTo f : 𝒪_{X, f(𝔪)} ⟶ R` is mathlib's packaging of "a morphism
`Spec R ⟶ X` out of a LOCAL ring is a point of `X` plus a local homomorphism out of its stalk".
The three lemmas below are what the pole argument needs from it and are absent from the pin;
all three are PROVEN here with no sorry, and none of them mentions a curve.  -/

/-- **A morphism out of the spectrum of a local ring misses a CLOSED point exactly when its
closed point is not sent there** (PROVEN 2026-07-31, no sorry).

Every prime of a local ring is contained in the maximal ideal, so every point of `Spec R`
specializes to the closed point (`IsLocalRing.specializes_closedPoint`); continuous maps preserve
specialization, and `{z}` being closed is stable under specialization.  So a single point has to
be ruled out, not a whole range — this is step B1 of
`notMem_range_of_valuativeLift_toAffineLine_compl_singleton`.

`IsClosed {z}` IS LOAD-BEARING: for a non-closed `z` the conclusion is false — take `X = Spec R`
itself, `l = 𝟙`, and `z` the generic point of a DVR. -/
theorem notMem_range_of_closedPoint_ne {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
    (l : Spec R ⟶ X) {z : X} (hz : IsClosed ({z} : Set X))
    (hm : l.base (IsLocalRing.closedPoint R) ≠ z) : z ∉ Set.range l.base := by
  rintro ⟨p, hp⟩
  refine hm ?_
  have hsp : l.base p ⤳ l.base (IsLocalRing.closedPoint R) :=
    (IsLocalRing.specializes_closedPoint p).map l.base.hom.continuous
  rw [hp] at hsp
  have := hsp.mem_closed hz rfl
  simpa using this

/-- **The affine case of the naturality below** (PROVEN 2026-07-31, no sorry): on `Spec R` for
`R` local, the specialization map from the closed point to the prime `α⁻¹𝔪_S`, followed by the
classifying map of `Spec.map α`, is `α` itself.

Both sides are maps out of `(Spec R).presheaf.stalk (closedPoint R)`, so
`TopCat.Presheaf.stalk_hom_ext` reduces to opens containing the closed point — and there is only
one, `⊤` (`IsLocalRing.closed_point_mem_iff`).  There the two sides are
`germ_stalkClosedPointTo_Spec` and `germ_stalkClosedPointIso_hom`, both of which say
`(ΓSpecIso R).hom`. -/
theorem stalkSpecializes_stalkClosedPointTo_Spec {R S : CommRingCat.{u}}
    [IsLocalRing R] [IsLocalRing S] (α : R ⟶ S) :
    (Spec R).presheaf.stalkSpecializes
        (IsLocalRing.specializes_closedPoint
          ((Spec.map α).base (IsLocalRing.closedPoint S))) ≫
      Scheme.stalkClosedPointTo (Spec.map α) =
      (stalkClosedPointIso R).hom ≫ α := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  obtain rfl : U = ⊤ := IsLocalRing.closed_point_mem_iff.mp hU
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  rw [Scheme.germ_stalkClosedPointTo_Spec α]
  rw [← Category.assoc, germ_stalkClosedPointIso_hom]

/-- **THE CLASSIFYING LOCAL HOMOMORPHISM IS NATURAL IN THE LOCAL RING, ALONG SPECIALIZATION**
(PROVEN 2026-07-31, no sorry).

For `l : Spec R ⟶ X` and ANY ring map `α : R ⟶ S` with `S` local, the square

    𝒪_{X, l(𝔪_R)} --stalkClosedPointTo l--> R
        |                                   |
   stalkSpecializes                         α
        v                                   v
    𝒪_{X, (Spec α ≫ l)(𝔪_S)} ------------> S

commutes.  **`α` is NOT assumed local, and that is the whole point of the lemma**: the case the
pole argument needs is `α = algebraMap R L` into the fraction field, which sends `𝔪_S = 0` back
to `(0)`, so `Spec α` hits the GENERIC point of `Spec R` and the two closed-point images differ.
A local `α` would give the trivial statement with `stalkSpecializes` the identity.

The proof is `stalkClosedPointTo_comp` to split off `Spec.map α`, then
`Scheme.Hom.stalkSpecializes_stalkMap` to move the specialization across `l`, then the affine
case above. -/
theorem stalkSpecializes_stalkClosedPointTo {X : Scheme.{u}} {R S : CommRingCat.{u}}
    [IsLocalRing R] [IsLocalRing S] (α : R ⟶ S) (l : Spec R ⟶ X)
    (h : l.base ((Spec.map α).base (IsLocalRing.closedPoint S)) ⤳
      l.base (IsLocalRing.closedPoint R)) :
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (Spec.map α ≫ l) =
      Scheme.stalkClosedPointTo l ≫ α := by
  rw [Scheme.stalkClosedPointTo_comp (Spec.map α) l,
    Scheme.Hom.stalkSpecializes_stalkMap_assoc l _ _
      (IsLocalRing.specializes_closedPoint ((Spec.map α).base (IsLocalRing.closedPoint S))),
    stalkSpecializes_stalkClosedPointTo_Spec α, Scheme.stalkClosedPointTo, Category.assoc]

/-- **The same statement with the composite named separately** (PROVEN 2026-07-31, no sorry).

This is not cosmetic.  A consumer holds the composite in the form its own hypothesis gives it —
here `hl₁ : Spec.map (algebraMap R L) ≫ l = i₁ ≫ ι` — and the two descriptions of the SAME
morphism give two syntactically different points, hence two different `X.presheaf.stalk _`, and
`rw` cannot bridge them inside a dependent type.  Taking the equation as a hypothesis and
`subst`ing it does. -/
theorem stalkSpecializes_stalkClosedPointTo' {X : Scheme.{u}} {R S : CommRingCat.{u}}
    [IsLocalRing R] [IsLocalRing S] (α : R ⟶ S) (l : Spec R ⟶ X) (m : Spec S ⟶ X)
    (hm : Spec.map α ≫ l = m)
    (h : m.base (IsLocalRing.closedPoint S) ⤳ l.base (IsLocalRing.closedPoint R)) :
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo m =
      Scheme.stalkClosedPointTo l ≫ α := by
  subst hm
  exact stalkSpecializes_stalkClosedPointTo α l h

/-- **THE POLE CONTRADICTION, IN ABSTRACT FORM** (PROVEN 2026-07-31, no sorry) — step B2 of
`notMem_range_of_valuativeLift_toAffineLine_compl_singleton` with every trace of the curve, of
`𝔸¹` and of the valuative square removed.

Read it as: `w` is `1/f` at `z`, `v` is `f` at the generic point, `r` is `f`'s value on `Spec R`.
Pushing `w · v = 1` through `θ` and using the compatibility square turns it into
`algebraMap R L (ψ w · r) = 1`; `algebraMap R L` is injective because `R` is a domain with
fraction field `L`, so `ψ w` is a UNIT of `R`; and `ψ` is local, so `w` would be a unit of the
stalk — contradicting `w ∈ 𝔪`.

**`IsLocalHom ψ.hom` IS LOAD-BEARING and the statement is FALSE without it**: drop it and take
`ψ = 0`… more precisely, any `ψ` killing `𝔪` into a unit makes `ψ w · r = 1` consistent.  It is
supplied for free by `Scheme.isLocalHom_stalkClosedPointTo`.

**`IsFractionRing R L` IS LOAD-BEARING**: only injectivity of `R ⟶ L` is used, but without it
`ψ w · r = 1` cannot be concluded from its image in `L`. -/
theorem false_of_pole {X : Scheme.{u}} {R L : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    {z x₀ : X} (hsp : x₀ ⤳ z)
    (ψ : X.presheaf.stalk z ⟶ CommRingCat.of R) [IsLocalHom ψ.hom]
    (θ : X.presheaf.stalk x₀ ⟶ CommRingCat.of L)
    (hcompat : X.presheaf.stalkSpecializes hsp ≫ θ = ψ ≫ CommRingCat.ofHom (algebraMap R L))
    (v : X.presheaf.stalk x₀) (r : R) (hr : θ.hom v = algebraMap R L r)
    (w : X.presheaf.stalk z) (hwm : w ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z))
    (hwid : (X.presheaf.stalkSpecializes hsp).hom w * v = 1) : False := by
  have h2 : θ.hom ((X.presheaf.stalkSpecializes hsp).hom w) = algebraMap R L (ψ.hom w) := by
    have := congrArg (fun (φ : X.presheaf.stalk z ⟶ CommRingCat.of L) => φ.hom w) hcompat
    simpa using this
  have h1 : algebraMap R L (ψ.hom w * r) = algebraMap R L 1 := by
    rw [map_mul, map_one, ← h2, ← hr, ← map_mul, hwid, map_one]
  have h3 : ψ.hom w * r = 1 := IsFractionRing.injective R L h1
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hwm)
    (‹IsLocalHom ψ.hom›.map_nonunit _ (IsUnit.of_mul_eq_one _ h3))

/-! ### The extension obstruction: a global regular function on a proper curve is algebraic

The four items below are what closes the "`f` does not extend across `z`" sub-sub-leaf, and
none of them mentions a valuation ring, a DVR, `𝔪_z`, properness of a morphism to `𝔸¹`, or
Zariski's main theorem.  The route they realise is SHORTER than the extend-then-ZMT dichotomy
this file used to plan, and the reason is one lemma of the pin that the plan overlooked:
`isIntegral_appTop_of_universallyClosed` (`Morphisms/Proper.lean`) says the global sections of
a universally closed scheme over an affine base are INTEGRAL over it.  So an extension `F` of
`f` is algebraic over `K` outright, `g` classifies a root of a nonzero polynomial, and `g` is
therefore constant — no fibre dichotomy, no `IsFinite.of_isProper_of_locallyQuasiFinite`, and
no need to build the morphism `ĝ : X ⟶ 𝔸¹_K` at all (only the SECTION `F` is needed). -/

/-- **Two sections of an INTEGRAL scheme with the same germ at one common point glue**
(PROVEN 2026-07-31, no sorry).

On an integral scheme a germ determines a section (`germ_injective_of_isIntegral`), so equality
of germs at the single point `x₀` upgrades to equality on EVERY open contained in both domains
— which is exactly the compatibility that `TopCat.Sheaf.existsUnique_gluing'` wants.  Only the
restriction of the glued section to `U` is returned, since that is all the consumer uses.

`IsIntegral X` IS LOAD-BEARING: without irreducibility two sections can agree at `x₀` and
disagree elsewhere on `U ⊓ V`, and nothing glues. -/
theorem exists_res_eq_of_germ_eq {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens}
    (hcover : (⊤ : X.Opens) ≤ U ⊔ V) {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (f : Γ(X, U)) (s : Γ(X, V))
    (h : X.presheaf.germ U x₀ hxU f = X.presheaf.germ V x₀ hxV s) :
    ∃ F : Γ(X, ⊤), X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op F = f := by
  classical
  have key : ∀ (W : X.Opens) (h1 : W ≤ U) (h2 : W ≤ V), x₀ ∈ W →
      X.presheaf.map (homOfLE h1).op f = X.presheaf.map (homOfLE h2).op s := by
    intro W h1 h2 hxW
    refine germ_injective_of_isIntegral X x₀ hxW ?_
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact h
  let 𝒰 : Bool → X.Opens := fun b => Bool.rec V U b
  let sf : ∀ b, Γ(X, 𝒰 b) := fun b => Bool.rec s f b
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 𝒰 sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact (key _ inf_le_right inf_le_left ⟨hxV, hxU⟩).symm
    · exact key _ inf_le_left inf_le_right ⟨hxU, hxV⟩
    · rfl
  have hcov : (⊤ : X.Opens) ≤ iSup 𝒰 := by
    rw [iSup_bool_eq]
    exact hcover
  obtain ⟨F, hFspec, -⟩ :=
    X.sheaf.existsUnique_gluing' 𝒰 ⊤ (fun _ => homOfLE le_top) hcov sf hcompat
  exact ⟨F, hFspec true⟩

/-- **IF THE CLASSIFIED FUNCTION EXTENDS TO A GLOBAL SECTION, `g` CANNOT BE QUASI-FINITE**
(PROVEN 2026-07-31, no sorry) — the whole of the sub-sub-leaf's mathematics, with the puncture,
the specialization and the stalks removed: only an OPEN `U` of a proper integral `X`, infinite,
and a `K`-morphism `g : U ⟶ 𝔸¹_K` whose classified function is the restriction of a global one.

THE ARGUMENT, in four moves:

1. `isIntegral_appTop_of_universallyClosed strX` (pin, `Morphisms/Proper.lean`): `Γ(X, ⊤)` is
   INTEGRAL over `K`.  So `F` satisfies a monic `p ∈ K[T]`.
2. `coordHom_comp_C` transports that identity along the classifying map: `p` is in the kernel
   of `coordHom U g`, because a ring map out of `K[T]` is `eval₂` of what it does to `K` and to
   `T` (`Polynomial.ringHom_ext`), and those are the restriction `Γ(X, ⊤) ⟶ Γ(X, U)` and `f`.
3. Hence `T`'s pull-back to the basic open of `p` is `0`, so `g` sends the GENERIC point of `U`
   into `V(p)`; as `p ≠ 0` and `K[T]` is a PID, that prime is MAXIMAL, i.e. a closed point.
4. A continuous map sends generizations to generizations, so the image of the whole of `U` is
   contained in the closure of that closed point — a single point.  Its fibre is all of `U`,
   which is infinite, while `Scheme.Hom.finite_preimage_singleton` makes it finite.

**`IsProper strX` IS LOAD-BEARING**, through `UniversallyClosed` in move 1 — on an affine curve
`Γ(X, ⊤)` is not algebraic over `K` and the extension carries no information.

**`Infinite ↥U` IS LOAD-BEARING and the statement is FALSE without it**: on a finite `U` a
constant `g` is perfectly quasi-finite.

**`hover` IS LOAD-BEARING**: it is the only hypothesis tying `g` to the `K`-structure, and
move 2 is where it is consumed.  See `affineLineOver`. -/
theorem false_of_res_eq_coordOf_of_locallyQuasiFinite {K : Type u} [Field K] {X : Scheme.{u}}
    (strX : X ⟶ Spec (CommRingCat.of K)) [IsProper strX] [IsIntegral X]
    (U : X.Opens) [Infinite ↥U]
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    [LocallyQuasiFinite g] [QuasiCompact g]
    (hover : g ≫ affineLineOver K = Scheme.Opens.ι U ≫ strX)
    (F : Γ(X, ⊤))
    (hF : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op F = coordOf U g) :
    False := by
  classical
  haveI : Nonempty ↥U := inferInstance
  haveI : Nonempty ↥(U.toScheme) := inferInstanceAs (Nonempty ↥U)
  haveI : Infinite ↥(U.toScheme) := inferInstanceAs (Infinite ↥U)
  -- MOVE 1: `F` is integral over `K`.
  have hint : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed strX
  obtain ⟨p, hpm, hp0⟩ := hint F
  -- MOVE 2: the same polynomial dies in the classifying map of `g`.
  have hpsi : (coordHom U g).hom p = 0 := by
    have hsplit : (coordHom U g).hom = Polynomial.eval₂RingHom
        ((coordHom U g).hom.comp (Polynomial.C : K →+* Polynomial K))
        ((coordHom U g).hom Polynomial.X) :=
      Polynomial.ringHom_ext (fun a => by simp) (by simp)
    have hcc := congrArg CommRingCat.Hom.hom (coordHom_comp_C strX U g hover)
    rw [hsplit]
    show Polynomial.eval₂ _ _ p = 0
    rw [coordHom_apply_X, ← hF]
    have hK : (coordHom U g).hom.comp (Polynomial.C : K →+* Polynomial K) =
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ strX.appTop).hom := hcc
    rw [hK, ← Polynomial.hom_eval₂, hp0, map_zero]
  -- MOVE 3: so `T`'s pull-back vanishes, and the image of the generic point is a closed point.
  have hzero : g.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p) = 0 := by
    have hexp : (coordHom U g).hom p =
        (Scheme.Opens.topIso U).hom.hom
          (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p)) := rfl
    rw [hexp] at hpsi
    have h := congrArg (Scheme.Opens.topIso U).inv.hom hpsi
    rw [map_zero, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h
    exact h
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion (Scheme.Opens.ι U)
  set η : U.toScheme := genericPoint U.toScheme with hη
  set y : Spec (CommRingCat.of (Polynomial K)) := g.base η with hy
  have hpy : p ∈ y.asIdeal := by
    have hb : (Spec (CommRingCat.of (Polynomial K))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p) =
        PrimeSpectrum.basicOpen p := basicOpen_eq_of_affine _
    by_contra hcon
    have hmem : y ∈ (Spec (CommRingCat.of (Polynomial K))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p) := by
      rw [hb]; exact (PrimeSpectrum.mem_basicOpen p y).mpr hcon
    have hmem2 : η ∈ (U.toScheme).basicOpen
        (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom p)) := by
      rw [← Scheme.preimage_basicOpen_top]; exact hmem
    rw [hzero, Scheme.basicOpen_zero] at hmem2
    exact hmem2
  have hpne : p ≠ 0 := hpm.ne_zero
  have hbot : y.asIdeal ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hpy
    exact hpne hpy
  haveI : y.asIdeal.IsMaximal := _root_.IsPrime.to_maximal_ideal hbot
  have hyclosed : IsClosed ({y} : Set (Spec (CommRingCat.of (Polynomial K)))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr ‹_›
  -- MOVE 4: so `g` is constant, and its one fibre is both all of `U` and finite.
  have hconst : ∀ u : U.toScheme, g.base u = y := by
    intro u
    have h1 : η ⤳ u := (genericPoint_spec U.toScheme).specializes trivial
    have h2 : y ⤳ g.base u := h1.map g.base.hom.continuous
    simpa using h2.mem_closed hyclosed rfl
  have hfin := g.finite_preimage_singleton y
  have huniv : (⇑g ⁻¹' {y}) = Set.univ := by
    ext u
    simp [hconst u]
  rw [huniv] at hfin
  exact (Set.infinite_univ (α := ↥(U.toScheme))) hfin

/-- **`f` DOES NOT EXTEND ACROSS `z`** (cut 2026-07-31 out of
`exists_inv_coordOf_mem_maximalIdeal_compl_singleton` immediately below, which is proven over
it; this is the WHOLE of the mathematics that leaf contained.  **PROVEN 2026-07-31 the same
day, no sorry**, over the four items immediately above — so the affineness route's properness
half is now closed outright and the file's only remaining leaf is Riemann–Roch.)

Read it as `f ∉ 𝒪_{X,z}`, stated without the function field: `germ_{x₀} f` is not in the image
of the specialization map `𝒪_{X,z} ⟶ 𝒪_{X,x₀}`.  On an integral `X` that image is exactly
`𝒪_{X,z}` viewed inside `𝒪_{X,x₀} ⊆ K(X)` (both maps are injective), so the two readings agree
— see `exists_inv_coordOf_mem_maximalIdeal_compl_singleton`'s proof, which does the conversion.

**NO VALUATION RING, NO MAXIMAL IDEAL, NO RECIPROCAL.**  Everything about DVRs, `𝔪_z` and
`1/f` that the parent leaf carried has been discharged; what is left is a single
non-membership, and it is the only place `hqf` and `IsProper strX` are consumed.

## PROOF (2026-07-31), AND IT DOES NOT BUILD `ĝ` AT ALL

The plan this docstring used to record — extend `g` to `ĝ : X ⟶ 𝔸¹_K`, prove `ĝ` proper by
cancelling against `affineLineOver K`, then run a fibre dichotomy ending in
`IsFinite.of_isProper_of_locallyQuasiFinite` and `Module.Finite K K[T]` — is CORRECT but was
strictly more work than necessary, and it is not what is implemented.  The pin already carries
`isIntegral_appTop_of_universallyClosed` (`Morphisms/Proper.lean`): the global sections of a
universally closed scheme over an affine base are INTEGRAL over it.  That collapses the
dichotomy, because the "`ĝ` dominant" branch is then impossible outright rather than being
excluded case by case, and the MORPHISM `ĝ` is never needed — only the SECTION.

So the three steps actually taken are:

* the hypothesis `a : 𝒪_{X,z}` with `stalkSpecializes a = germ_{x₀} f` gives a section `s` on
  some open `V ∋ z` (`X.presheaf.exists_germ_eq`) whose germ at `x₀` is `germ_{x₀} f` — note
  `x₀ ∈ V` for free, `V` being open and `x₀ ⤳ z`;
* `U ⊔ V = ⊤`, since `U = {z}ᶜ` and `z ∈ V`, so `exists_res_eq_of_germ_eq` above glues `s` and
  `f` into `F ∈ Γ(X, ⊤)` restricting to `f`.  Equality of the two germs at the SINGLE point
  `x₀` suffices because `X` is integral;
* `false_of_res_eq_coordOf_of_locallyQuasiFinite` above finishes: `F` is algebraic over `K`, so
  `g` is constant, so its single fibre is the infinite `U` — and a quasi-finite quasi-compact
  morphism has finite fibres.

`QuasiCompact g` is obtained here exactly as in
`isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton` below: `X` is a NOETHERIAN scheme
(`CompactSpace` from `QuasiCompact strX`, `IsLocallyNoetherian` from
`LocallyOfFiniteType.isLocallyNoetherian`), hence so is the open `U`, and
`quasiCompact_of_noetherianSpace_source` applies.

**`hqf` IS LOAD-BEARING and the statement is FALSE without it**: `g` constant at `0` gives
`f = 0`, which extends across `z` by `0`.

**`IsProper strX` IS LOAD-BEARING**, and it is consumed twice: through `UniversallyClosed` for
the integrality of `Γ(X, ⊤)`, and through `QuasiCompact`/`LocallyOfFiniteType` for
`QuasiCompact g`.  On an affine curve `f` may extend across `z`.

**`hconn` IS LOAD-BEARING**, through `IsIntegral X` — without irreducibility there is no
generic point to compare germs at, the gluing step has no meaning, and `g` need not be constant
on the whole of `U` even when its classified function is algebraic.

**`SmoothOfRelativeDimension 1 strX` IS LOAD-BEARING**, and ONLY through
`infinite_of_smoothOfRelativeDimension_one`: it is what makes `U` infinite, which is the last
move.  On a zero-dimensional `X` the statement is false — every function extends. -/
theorem not_exists_stalkSpecializes_eq_germ_coordOf_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X))
    (g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)))
    (hqf : LocallyQuasiFinite g)
    (hover : g ≫ affineLineOver K =
      Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX)
    {x₀ : X} (hsp : x₀ ⤳ z)
    (hx₀ : x₀ ∈ (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) :
    ¬ ∃ a : X.presheaf.stalk z,
        (X.presheaf.stalkSpecializes hsp).hom a =
          (X.presheaf.germ _ x₀ hx₀).hom (coordOf _ g) := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : Infinite X := infinite_of_smoothOfRelativeDimension_one strX
  haveI : Infinite ↥(⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) :=
    (Set.Finite.infinite_compl (Set.finite_singleton z)).to_subtype
  haveI := hqf
  -- `QuasiCompact g`, exactly as in the consumer two declarations below.
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace strX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
  haveI : IsNoetherian X := ⟨⟩
  haveI : NoetherianSpace
      (Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) := by
    show NoetherianSpace (({z}ᶜ : Set X))
    infer_instance
  haveI : QuasiCompact g := inferInstance
  rintro ⟨a, ha⟩
  -- `a` is the germ of a section `s` on some open `V ∋ z`, and `x₀ ∈ V` since `x₀ ⤳ z`.
  obtain ⟨V, hzV, s, hs⟩ := X.presheaf.exists_germ_eq a
  have hx₀V : x₀ ∈ V := hsp.mem_open V.isOpen hzV
  have hgerm : (X.presheaf.germ _ x₀ hx₀) (coordOf _ g) = (X.presheaf.germ V x₀ hx₀V) s := by
    have h1 : (X.presheaf.germ V x₀ hx₀V) s
        = (X.presheaf.stalkSpecializes hsp).hom ((X.presheaf.germ V z hzV) s) := by
      rw [← CommRingCat.comp_apply, X.presheaf.germ_stalkSpecializes]
    rw [h1, hs, ha]
  -- `U ⊔ V = ⊤` because `U = {z}ᶜ` and `z ∈ V`, so `s` and `f` glue.
  have hcover : (⊤ : X.Opens) ≤ (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⊔ V := by
    rintro x -
    rcases eq_or_ne x z with rfl | hx
    · exact Or.inr hzV
    · exact Or.inl hx
  obtain ⟨F, hF⟩ := exists_res_eq_of_germ_eq hcover hx₀ hx₀V (coordOf _ g) s hgerm
  exact false_of_res_eq_coordOf_of_locallyQuasiFinite strX _ g hover F hF

/-- **SUB-LEAF 1 — `f` HAS A POLE AT `z`** (cut 2026-07-31 out of
`notMem_range_of_valuativeLift_toAffineLine_compl_singleton`; **PROVEN the same day** over the
single sub-leaf immediately above, which now carries all of its mathematics).

Concretely: `1/f` lies in the maximal ideal of `𝒪_{X,z}`, stated without ever writing `1/f` —
`w` is the reciprocal, and the clause `stalkSpecializes w · germ_{x₀} f = 1` says so inside
`𝒪_{X,x₀}`, which is where both live.  **No valuation ring, no `L`, no lift `l` appears**: the
statement mentions only `X`, `z`, `g` and a generization `x₀` of `z` inside `U`.

WHY `x₀` IS THE GENERIC POINT, which is what makes the statement usable.  `x₀ ⤳ z`, `z` is
closed and `x₀ ≠ z` (it lies in `{z}ᶜ`).  On the integral curve `X` the only proper generization
of a closed point is the generic point, so `𝒪_{X,x₀} = X.functionField` and the displayed
identity is literally `w = f⁻¹` in the function field.  The statement is phrased at a general
`x₀` only so that the consumer does not have to prove that identification.

## PROOF (2026-07-31) — the valuation-ring dichotomy, over the sub-leaf above

`𝒪_{X,z}` is a VALUATION RING (`valuationRing_stalk_of_smoothOfRelativeDimension_one`,
`CurveExtension.lean`) with fraction field `K(X)` (mathlib's
`IsFractionRing (X.presheaf.stalk x) X.functionField` for integral `X`), so
`ValuationRing.isInteger_or_isInteger` applied to `φ`, the image of `f` in `K(X)`, gives
`φ ∈ 𝒪_{X,z}` or `φ⁻¹ ∈ 𝒪_{X,z}`.  The sub-leaf kills the first, so `φ⁻¹ = algebraMap w` for
some `w`; and `w ∉ 𝒪_{X,z}ˣ`, since a unit `w` would make `φ = algebraMap (w⁻¹)` an integer
after all.  That is `w ∈ 𝔪_z`.

**No DVR is needed — only `ValuationRing`.**  The old plan went through
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, which needs
`¬ IsField 𝒪_{X,z}` (i.e. `z` is not the generic point) as a side condition.  The dichotomy
above needs none of that: at the generic point the stalk IS `K(X)`, every element is an
integer, and the sub-leaf is simply false there — so the exclusion of the generic point is
carried by the sub-leaf and never has to be proven separately.

The transport back into `𝒪_{X,x₀}` is `IsFractionRing.injective` for `𝒪_{X,x₀} ⟶ K(X)`
together with `TopCat.Presheaf.stalkSpecializes_comp` (the specialization `𝒪_{X,z} ⟶ 𝒪_{X,x₀}`
followed by `𝒪_{X,x₀} ⟶ K(X)` IS `𝒪_{X,z} ⟶ K(X)`) — which is also what turns the sub-leaf's
stalk-level non-membership into `¬ IsLocalization.IsInteger`.

**`hqf`, `IsProper strX` and `hconn` are all LOAD-BEARING**, and after this cut all three are
consumed inside the sub-leaf rather than here; see its docstring for the counterexamples.
`hconn` is additionally used here, through `IsIntegral X`, for the `IsFractionRing` and
`IsDomain` instances on the stalks. -/
theorem exists_inv_coordOf_mem_maximalIdeal_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X))
    (g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)))
    (hqf : LocallyQuasiFinite g)
    (hover : g ≫ affineLineOver K =
      Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX)
    {x₀ : X} (hsp : x₀ ⤳ z)
    (hx₀ : x₀ ∈ (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) :
    ∃ w : X.presheaf.stalk z, w ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (X.presheaf.stalkSpecializes hsp).hom w *
        (X.presheaf.germ _ x₀ hx₀).hom (coordOf _ g) = 1 := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : ValuationRing (X.presheaf.stalk z) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one strX z
  set fx₀ : X.presheaf.stalk x₀ := (X.presheaf.germ _ x₀ hx₀).hom (coordOf _ g) with hfx₀
  set φ : X.functionField := algebraMap (X.presheaf.stalk x₀) X.functionField fx₀ with hφ
  -- The specialization `𝒪_{X,z} ⟶ 𝒪_{X,x₀}` followed by `𝒪_{X,x₀} ⟶ K(X)` IS `𝒪_{X,z} ⟶ K(X)`.
  have htri : ∀ a : X.presheaf.stalk z,
      algebraMap (X.presheaf.stalk x₀) X.functionField
          ((X.presheaf.stalkSpecializes hsp).hom a) =
        algebraMap (X.presheaf.stalk z) X.functionField a := by
    intro a
    show (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes hsp).hom a) =
      (X.presheaf.stalkSpecializes _).hom a
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  -- The sub-leaf, transported across `IsFractionRing.injective`.
  have hni : ¬ IsLocalization.IsInteger (X.presheaf.stalk z) φ := by
    rintro ⟨a, ha⟩
    refine not_exists_stalkSpecializes_eq_germ_coordOf_compl_singleton
      strX hconn hz g hqf hover hsp hx₀ ⟨a, ?_⟩
    refine IsFractionRing.injective (X.presheaf.stalk x₀) X.functionField ?_
    rw [htri a, ha]
  have hφ0 : φ ≠ 0 := by
    intro h
    exact hni (by rw [h]; exact IsLocalization.isInteger_zero)
  -- The valuation-ring dichotomy: `φ ∉ 𝒪_{X,z}`, so `φ⁻¹ ∈ 𝒪_{X,z}`.
  obtain hint | ⟨w, hw⟩ :=
    ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) (K := X.functionField) φ
  · exact absurd hint hni
  refine ⟨w, ?_, ?_⟩
  · -- `w` is not a unit: a unit `w` would make `φ = algebraMap w⁻¹` an integer after all.
    rw [IsLocalRing.mem_maximalIdeal]
    rintro ⟨u, rfl⟩
    refine hni ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
    calc algebraMap (X.presheaf.stalk z) X.functionField
            ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z)
        = algebraMap (X.presheaf.stalk z) X.functionField
            ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (φ⁻¹ * φ) := by
          rw [inv_mul_cancel₀ hφ0, mul_one]
      _ = (algebraMap (X.presheaf.stalk z) X.functionField
            ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) *
          algebraMap (X.presheaf.stalk z) X.functionField
            ((u : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z)) * φ := by
          rw [hw]; ring
      _ = φ := by rw [← map_mul]; simp
  · -- `w · f = 1` in `𝒪_{X,x₀}`, checked in `K(X)`, where it is `φ⁻¹ · φ = 1`.
    refine IsFractionRing.injective (X.presheaf.stalk x₀) X.functionField ?_
    rw [map_mul, map_one, htri w, hw, ← hφ, inv_mul_cancel₀ hφ0]

/-- **The restriction `Γ(X, U) ⟶ Γ(U, ⊤)` along the inclusion IS `topIso U`'s inverse**
(PROVEN 2026-07-31, no sorry).

Both sides are `X.presheaf.map` of a morphism `op U ⟶ op (U.ι ''ᵁ ⊤)` in the poset `(X.Opens)ᵒᵖ`,
written with `homOfLE` on one side and `eqToHom` on the other.  A poset has subsingleton hom-sets,
so `congr 1` closes the gap — but only after `Scheme.Opens.ι_appLE` and the definition of
`Scheme.Opens.topIso` have exposed both as `X.presheaf.map _`; `simp` alone does NOT do it, and
`congr 1` applied to the full composite instead produces a bogus type-equality goal. -/
theorem ι_appLE_top_eq_topIso_inv {X : Scheme.{u}} (U : X.Opens) (e) :
    (Scheme.Opens.ι U).appLE U ⊤ e = (Scheme.Opens.topIso U).inv := by
  rw [Scheme.Opens.ι_appLE]
  rw [Scheme.Opens.topIso]
  simp only [Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  congr 1

/-- **`appLE ⊤ ⊤` is `appTop`** (PROVEN 2026-07-31, no sorry) — the `f ⁻¹ᵁ ⊤ = ⊤` bookkeeping
that `Scheme.Hom.appLE_eq_app` does not do on its own. -/
theorem appLE_top_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (e) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

/-- **SUB-LEAF 2 — `f`'s VALUE AT THE `L`-POINT COMES FROM `R`** (cut 2026-07-31,
**PROVEN 2026-07-31**).

PURE BOOKKEEPING: no curve, no properness, no smoothness, no valuation ring, no `IsFractionRing`
— just the commuting square `hcomm` read on global sections.  It is separated out because the
identification of `Γ`-level data with stalk-level data is exactly the part that fights the
elaborator, and it should not be entangled with the mathematics in SUB-LEAF 1.

THE PROOF, in four rewrites, all of them in the pin:

1. `Scheme.germ_stalkClosedPointTo (i₁ ≫ ι) U hx₀` turns
   `germ_U ≫ stalkClosedPointTo (i₁ ≫ ι)` into `(i₁ ≫ ι).app U ≫ (…) ≫ (ΓSpecIso (of L)).hom`.
   Normalise the `(…)` with `Scheme.Hom.app_eq_appLE` and `Scheme.Hom.appLE_map` to land on
   `(i₁ ≫ ι).appLE U ⊤ _ ≫ (ΓSpecIso (of L)).hom`.
2. `Scheme.Hom.appLE_comp_appLE` splits that as `ι.appLE U ⊤ _ ≫ i₁.appLE ⊤ ⊤ _`, and
   `Scheme.Opens.ι_appLE` identifies the first factor with `(Scheme.Opens.topIso U).inv` — the
   two differ only by which morphism of the poset `X.Opens` is written, and a poset has
   subsingleton hom-sets.  So the whole thing is `topIso.inv ≫ i₁.appTop ≫ (ΓSpecIso _).hom`,
   and `topIso.inv` cancels the `topIso.hom` inside `coordOf`.
3. `Scheme.comp_appTop` applied to `hcomm` gives
   `i₁.appTop (g.appTop t) = (Spec.map (ofHom (algebraMap R L))).appTop (i₂.appTop t)` for
   `t = (ΓSpecIso (of K[T])).inv T`.
4. `Scheme.ΓSpecIso_naturality (ofHom (algebraMap R L))` turns
   `(ΓSpecIso (of L)).hom ∘ (Spec.map _).appTop` into `algebraMap R L ∘ (ΓSpecIso (of R)).hom`.

So the witness is forced: `r = (ΓSpecIso (of R)).hom (i₂.appTop ((ΓSpecIso (of K[T])).inv T))`,
i.e. `T`'s pull-back along `i₂`, which is what "the value lies in `R`" means.

HOW IT WAS FINISHED, later the same day: exactly by the second of the two suggestions the
previous note left — step 2 is now the standalone lemma `ι_appLE_top_eq_topIso_inv` above, whose
`congr 1` closes on subsingleton poset hom-sets, together with `appLE_top_top_eq_appTop`.  Two
further traps, recorded because both cost a round trip:

* `simpa using <congrArg of the morphism-level identity>` does NOT produce the element-level
  form — `simp` normalises `topIso.inv` to `X.presheaf.map (eqToHom ⋯)` on both sides and then
  reports a type mismatch between two printed-identical terms.  Use
  `rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply, CommRingCat.comp_apply]` instead;
  `rw` keeps `topIso.inv` intact.
* `simpa using <congrArg of ΓSpecIso_naturality>` simplifies that hypothesis all the way to
  `True`, since `simp` proves the naturality square outright.  State step 4 as its own `have`
  with the two sides written out and prove it by `rw`.

**`hcomm` IS LOAD-BEARING and the statement is FALSE without it**: it is the ONLY hypothesis
relating `g` to `R` at all.  Without it `i₁` may send `T` to any element of `L` whatever, in
particular to one with a pole, and `r` need not exist.

**`IsLocalRing R` IS LOAD-BEARING for the statement to typecheck** — `stalkClosedPointTo`
is only defined for a local ring — and `IsLocalRing (of L)` comes free from `Field L`. -/
theorem exists_algebraMap_eq_stalkClosedPointTo_germ_coordOf
    {K : Type u} [Field K] {X : Scheme.{u}} (U : X.Opens)
    (g : U.toScheme ⟶ Spec (CommRingCat.of (Polynomial K)))
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {L : Type u} [Field L] [Algebra R L]
    (i₁ : Spec (CommRingCat.of L) ⟶ U.toScheme)
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hcomm : i₁ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ i₂)
    (hx₀ : (i₁ ≫ Scheme.Opens.ι U).base (IsLocalRing.closedPoint (CommRingCat.of L)) ∈ U) :
    ∃ r : R, (Scheme.stalkClosedPointTo (i₁ ≫ Scheme.Opens.ι U)).hom
        ((X.presheaf.germ U _ hx₀).hom (coordOf U g)) = algebraMap R L r := by
  set t := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv.hom Polynomial.X with ht
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (i₂.appTop.hom t), ?_⟩
  -- STEP 2: the restriction `Γ(X, U) ⟶ Γ(Spec L, ⊤)` of the composite factors as
  -- `topIso.inv ≫ i₁.appTop`.
  have hfac : (i₁ ≫ Scheme.Opens.ι U).appLE U ⊤
      (Scheme.preimage_eq_top_of_closedPoint_mem (i₁ ≫ Scheme.Opens.ι U) hx₀).ge =
      (Scheme.Opens.topIso U).inv ≫ i₁.appTop := by
    rw [← ι_appLE_top_eq_topIso_inv U (by simp), ← appLE_top_top_eq_appTop i₁ (by simp)]
    exact (Scheme.Hom.appLE_comp_appLE i₁ (Scheme.Opens.ι U) U ⊤ ⊤ _ _).symm
  -- STEP 1: `germ ≫ stalkClosedPointTo` is that restriction followed by `ΓSpecIso`.
  have key : X.presheaf.germ U _ hx₀ ≫ Scheme.stalkClosedPointTo (i₁ ≫ Scheme.Opens.ι U) =
      (Scheme.Opens.topIso U).inv ≫ i₁.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [Scheme.germ_stalkClosedPointTo (i₁ ≫ Scheme.Opens.ι U) U hx₀]
    rw [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      ← Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, hfac, Category.assoc]
  -- STEP 3: `hcomm` on global sections.
  have h3 : i₁.appTop.hom (g.appTop.hom t) =
      (Spec.map (CommRingCat.ofHom (algebraMap R L))).appTop.hom (i₂.appTop.hom t) := by
    have h := congrArg
      (fun φ : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (Polynomial K)) => φ.appTop.hom t)
      hcomm
    simpa using h
  -- STEP 4: naturality of `ΓSpecIso`.
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R L))).appTop.hom (i₂.appTop.hom t))
      = algebraMap R L ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (i₂.appTop.hom t)) := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    rfl
  have hco : (Scheme.Opens.topIso U).inv.hom (coordOf U g) = g.appTop.hom t := by
    rw [ht, coordOf, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  have keyel : (Scheme.stalkClosedPointTo (i₁ ≫ Scheme.Opens.ι U)).hom
      ((X.presheaf.germ U _ hx₀).hom (coordOf U g)) =
      (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
        (i₁.appTop.hom ((Scheme.Opens.topIso U).inv.hom (coordOf U g))) := by
    rw [← CommRingCat.comp_apply, key, CommRingCat.comp_apply, CommRingCat.comp_apply]
  rw [keyel, hco, h3, h4]

/-- **THE POLE AT `z`, in valuative form: a lift of a valuative square into `X` cannot hit `z`**
(**PROVEN 2026-07-31** over the two sub-leaves immediately above; formerly a bare `sorry`, cut
2026-07-30 as the ONLY residue of
`isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton`, which is now proven over the
existence lemma below, which is in turn proven over this).

Given a valuation ring `R` with fraction field `L`, a point `i₁ : Spec L ⟶ X ∖ {z}`, a
`Spec R ⟶ 𝔸¹_K` that agrees with it through `g` (that is `hcomm` — see the FAITHFULNESS note,
it is not optional), and a lift `l : Spec R ⟶ X` of the resulting square over `strX`, the
range of `l` misses `z`.

This is where ALL the mathematics of properness now sits.  Everything categorical around it —
building the square, extracting `l`, factoring through the open, and both triangles — is proven
in `valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton` below.

TRUE, in two substeps.

**B1 — only the closed point can be the problem.**  In `Spec R` every prime is contained in
the maximal ideal, so every point specializes to the closed point `m`; `l.base` is continuous
and `{z}` is closed, so `z ∈ Set.range l.base ↔ l.base m = z`.  One point to rule out, not a
range.

**B2 — the pole rules it out.**  If `l.base m = z` then `Scheme.Hom.stalkMap l m` is a LOCAL
homomorphism `𝒪_{X,z} ⟶ 𝒪_{Spec R, m} ≅ R` (`R` is local, so the stalk at its closed point is
`R`).  Let `f ∈ Γ(U)` be `g`'s pull-back of `T`.  `X` is integral
(`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` in `CurveExtension.lean`
— this is where `hconn` is consumed), so `Γ(U)` and `𝒪_{X,z}` both sit inside
`X.functionField`, with `IsFractionRing (X.presheaf.stalk z) X.functionField`.  And `𝒪_{X,z}`
is a DISCRETE VALUATION RING
(`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, same file).  So if
`f ∉ 𝒪_{X,z}` then `f⁻¹ ∈ 𝔪_z`, hence `stalkMap l m f⁻¹ ∈ 𝔪_R`, so `f`'s image has NEGATIVE
valuation in `R` — while `hcomm` says that image is `i₂`'s pull-back of `T`, which lies in `R`.
Contradiction.

**What B2 rests on, and it is worth a leaf of its own: `f ∉ 𝒪_{X,z}`, i.e. `g` DOES NOT EXTEND
ACROSS `z`.**  That statement mentions `X` and `g` only — no valuation ring — and it is the
only place `hqf` is consumed.  Its proof is a dichotomy on a hypothetical extension
`ĝ : X ⟶ 𝔸¹_K` with `Scheme.Opens.ι U ≫ ĝ = g`:

* `ĝ ≫ affineLineOver K = strX`, because the two agree on `U`, which is DENSE
  (`isDominant_of_finite_compl`, `CurveExtension.lean`) — so `ĝ` is a `K`-morphism, hence
  proper by `IsProper.of_comp` cancelling against the separated `affineLineOver K`;
* if some fibre of `ĝ` is infinite it is all of the irreducible curve `X`, so `g` is constant
  on the infinite `U` (`infinite_of_smoothOfRelativeDimension_one`), contradicting `hqf`;
* otherwise `ĝ` is quasi-finite, hence FINITE by
  `IsFinite.of_isProper_of_locallyQuasiFinite`, so `affineLineOver K` is proper AND affine,
  hence finite, i.e. `K[T]` is a finite `K`-module — false, `Polynomial.basisMonomials`
  being a basis indexed by `ℕ`.

**That last contradiction is cleaner than the one this file used to record.**  The old note
said a finite surjection from a universally closed `X` would make `affineLineOver K`
universally closed, "which it is not" — leaving a prover to prove that `𝔸¹` is not universally
closed over `K`, which is real work.  Going through `Module.Finite K K[T]` avoids it entirely.

## FAITHFULNESS AUDIT

**`hcomm` IS LOAD-BEARING and the statement is FALSE without it.**  This was caught by
audit, not by the compiler, and the first draft of this leaf omitted it.  `hl₁` only says
`l`'s generic point lands in `U`, and `hl₂` only ties `l` to `i₂` through the BASE `Spec K`;
neither says anything about the value of `T`.  Witness: `X = ℙ¹_K`, `z = ∞`, `R = K[[t]]`,
`L = K((t))`, `l` the standard map hitting `∞` at the closed point and the generic point of
`ℙ¹` at the generic point.  Then `hl₁` holds with `i₁` the generic point of `U`, and `hl₂`
holds for any `K`-morphism `i₂` whatever, since both `strX` and `affineLineOver K` land in
`Spec K` and everything in sight is a `K`-morphism.  So `z ∈ Set.range l.base` with every
other hypothesis satisfied.  It is `hcomm` — `f`'s value at the generic point IS `i₂`'s value
of `T`, hence lies in `R` — that excludes this.

`hqf` is load-bearing for the same reason it is in the consumer: `g` constant at `0` satisfies
everything else, and its lift may perfectly well hit `z`.

NOT VACUOUS: `ValuativeCommSq g` is inhabited — `U`'s local rings are valuation rings
(`valuationRing_stalk_of_smoothOfRelativeDimension_one`) — and the consumer below instantiates
this leaf at every one of them.

## PROOF (2026-07-31) — B1 and B2's assembly are now PROVEN; only the two sub-leaves remain

The plan above is realised verbatim, over the machinery introduced earlier in this file:

* **B1** is `notMem_range_of_closedPoint_ne` (PROVEN), which reduces the range to the single
  point `l (𝔪_R)`.  After that `subst` puts `z = l (𝔪_R)` and the rest is about that point.
* the pole itself is SUB-LEAF 1, `exists_inv_coordOf_mem_maximalIdeal_compl_singleton`,
  instantiated at `x₀ := (i₁ ≫ ι)(𝔪_L)`.  That `x₀ ⤳ l (𝔪_R)` is
  `IsLocalRing.specializes_closedPoint` pushed through the continuous `l.base` (after rewriting
  by `hl₁`); that `x₀ ∈ U` is `Scheme.Opens.range_ι`.
* the value is SUB-LEAF 2, `exists_algebraMap_eq_stalkClosedPointTo_germ_coordOf`, which is
  pure bookkeeping on `hcomm` and needs none of the curve hypotheses.
* the compatibility square between the two classifying homomorphisms is
  `stalkSpecializes_stalkClosedPointTo'` (PROVEN), and **`hl₁` enters ONLY here** — as the
  equation identifying `Spec.map (algebraMap R L) ≫ l` with `i₁ ≫ ι`.
* the contradiction is `false_of_pole` (PROVEN).

**`hl₂` IS NOT CONSUMED**, and the binder is therefore written `_hl₂`.  That is not a claim that
it is redundant for the mathematics — it is part of the valuative-square data the consumer holds
anyway — only that this route does not read it.  A future prover of either sub-leaf may not use
it either: SUB-LEAF 1 does not mention `l` at all, and SUB-LEAF 2 does not mention `strX`. -/
theorem notMem_range_of_valuativeLift_toAffineLine_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X))
    (g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)))
    (hqf : LocallyQuasiFinite g)
    (hover : g ≫ affineLineOver K =
      Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX)
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {L : Type u} [Field L] [Algebra R L] [IsFractionRing R L]
    (i₁ : Spec (CommRingCat.of L) ⟶
      Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens))
    (i₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Polynomial K)))
    (hcomm : i₁ ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ i₂)
    (l : Spec (CommRingCat.of R) ⟶ X)
    (hl₁ : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ l =
      i₁ ≫ Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens))
    (_hl₂ : l ≫ strX = i₂ ≫ affineLineOver K) :
    z ∉ Set.range l.base := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : IsLocalRing R := inferInstance
  refine notMem_range_of_closedPoint_ne l hz ?_
  intro hm
  subst hm
  have hsp : (i₁ ≫ Scheme.Opens.ι (⟨({l.base (IsLocalRing.closedPoint (CommRingCat.of R))}ᶜ :
        Set X), hz.isOpen_compl⟩ : X.Opens)).base
        (IsLocalRing.closedPoint (CommRingCat.of L)) ⤳
      l.base (IsLocalRing.closedPoint (CommRingCat.of R)) := by
    rw [← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.base.hom.continuous
  have hx₀mem : (i₁ ≫ Scheme.Opens.ι (⟨({l.base (IsLocalRing.closedPoint (CommRingCat.of R))}ᶜ :
      Set X), hz.isOpen_compl⟩ : X.Opens)).base
      (IsLocalRing.closedPoint (CommRingCat.of L)) ∈
      (⟨({l.base (IsLocalRing.closedPoint (CommRingCat.of R))}ᶜ : Set X),
        hz.isOpen_compl⟩ : X.Opens) := by
    have hrange : (i₁ ≫ Scheme.Opens.ι (⟨({l.base (IsLocalRing.closedPoint (CommRingCat.of R))}ᶜ :
        Set X), hz.isOpen_compl⟩ : X.Opens)).base
        (IsLocalRing.closedPoint (CommRingCat.of L)) ∈
        Set.range (Scheme.Opens.ι (⟨({l.base (IsLocalRing.closedPoint (CommRingCat.of R))}ᶜ :
          Set X), hz.isOpen_compl⟩ : X.Opens)).base :=
      ⟨i₁.base (IsLocalRing.closedPoint (CommRingCat.of L)), rfl⟩
    rwa [Scheme.Opens.range_ι] at hrange
  have hcompat := stalkSpecializes_stalkClosedPointTo' (CommRingCat.ofHom (algebraMap R L)) l _
    hl₁ hsp
  obtain ⟨w, hwm, hwid⟩ := exists_inv_coordOf_mem_maximalIdeal_compl_singleton
    strX hconn hz g hqf hover hsp hx₀mem
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_stalkClosedPointTo_germ_coordOf _ g i₁ i₂ hcomm hx₀mem
  exact false_of_pole hsp (Scheme.stalkClosedPointTo l)
    (Scheme.stalkClosedPointTo (i₁ ≫ Scheme.Opens.ι _)) hcompat
    ((X.presheaf.germ _ _ hx₀mem).hom (coordOf _ g)) r hr w hwm hwid

/-- **The valuative lift: a valuation ring mapping to `𝔸¹_K` whose generic point lands in
`X ∖ {z}` lands there entirely** (**PROVEN 2026-07-30** over the leaf immediately above, which
is the only thing left under it).

This is the EXISTENCE half of the valuative criterion for `g`, and after the cut it is the
whole geometric content of properness: the uniqueness half and all three shape hypotheses of
`IsProper.of_valuativeCriterion` are proven at the consumer.  See its docstring for which
lemma discharges which.

TRUE.  Unfolded, a `ValuativeCommSq g` is a valuation ring `R` with fraction field `L`
together with `i₁ : Spec L ⟶ X ∖ {z}` and `i₂ : Spec R ⟶ 𝔸¹_K` agreeing over `Spec R`'s
generic point, and the task is to produce `Spec R ⟶ X ∖ {z}`.

## THE PROOF, in four steps; three of them are here and only step B is a leaf

**A. Lift into `X`.**  Push `i₁` forward along `Scheme.Opens.ι` and `i₂` along
`affineLineOver K`.  The resulting square over `strX` commutes — that is `hover` plus
`S.commSq` and nothing else — and `IsProper strX` gives `ValuativeCriterion strX` by
rewriting with `IsProper.eq_valuativeCriterion`.  So there is `l : Spec R ⟶ X` with
`Spec.map (algebraMap R L) ≫ l = i₁ ≫ ι` and `l ≫ strX = i₂ ≫ affineLineOver K`.

**B. `l` misses `z`.**  THIS IS THE CONTENT, and it is the leaf
`notMem_range_of_valuativeLift_toAffineLine_compl_singleton` above; see there for the pole
argument and for why its `hcomm` hypothesis is load-bearing.

**C. Factor through `U`.**  `IsOpenImmersion.lift (Scheme.Opens.ι U) l ⟨B⟩`, with
`IsOpenImmersion.lift_fac` for the factorisation.  The range condition needs only that `U` is
`{z}ᶜ`, via `Scheme.Opens.range_ι`.

**D. The two triangles, and `fac_right` is the one trap here.**  `fac_left` follows by
cancelling the mono `Scheme.Opens.ι U`.  `fac_right` CANNOT be got the same way —
`affineLineOver K` is not a mono, so knowing `(lift ≫ g) ≫ affineLineOver K = i₂ ≫
affineLineOver K` is useless.  What works instead: the two morphisms `Spec R ⟶ 𝔸¹_K` agree
after composing with `Spec.map (algebraMap R L)` (that is `fac_left` plus `S.commSq`), both are
morphisms between AFFINE schemes, so `Spec.preimage` turns them into ring maps
`K[T] ⟶ R`; `Spec.map_injective` transports the equality to those, and `algebraMap R L` is
injective because `R` is a domain with fraction field `L`
(`IsFractionRing.injective`) — so the two ring maps agree and `Spec.map_preimage` closes it.
Note the last rewrite must not touch `S.i₂`, which occurs in `l`'s own type: rewriting it
gives an ill-typed motive.

## Faithfulness

`hconn` and `hqf` are not consumed here — they are consumed inside step B's leaf, which is
also where `SmoothOfRelativeDimension 1 strX` is used.  What this proof consumes is
`IsProper strX` (step A) and `hover` (steps A and D). -/
theorem valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X))
    (g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)))
    (hqf : LocallyQuasiFinite g)
    (hover : g ≫ affineLineOver K =
      Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX) :
    ValuativeCriterion.Existence g := by
  intro S
  -- STEP A: push the square forward along `Scheme.Opens.ι` and `affineLineOver K`, and lift
  -- into `X` by the valuative criterion for the proper `strX`.
  have hVC : ValuativeCriterion strX := by
    have h : IsProper strX := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : CommSq (S.i₁ ≫ Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens))
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) strX (S.i₂ ≫ affineLineOver K) := by
    constructor
    rw [Category.assoc, ← hover, ← Category.assoc, S.commSq.w, Category.assoc]
  obtain ⟨⟨l, hfl, hfr⟩⟩ := (hVC ⟨S.R, S.K, _, _, hsq⟩).some.toInhabited
  -- STEP B: the lift misses `z`.  This is the leaf.
  have hmiss : z ∉ Set.range l.base :=
    notMem_range_of_valuativeLift_toAffineLine_compl_singleton
      strX hconn hz g hqf hover S.i₁ S.i₂ S.commSq.w l hfl hfr
  -- STEP C: factor through the open `U`.
  have hrange : Set.range l.base ⊆
      Set.range (Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)).base := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    rintro (rfl : x = z)
    exact hmiss hx
  -- STEP D: the two triangles.
  have hfac := IsOpenImmersion.lift_fac
    (Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) l hrange
  have hleft : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫
      IsOpenImmersion.lift _ l hrange = S.i₁ := by
    refine (cancel_mono
      (Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens))).mp ?_
    rw [Category.assoc, hfac, hfl]
  refine ⟨⟨IsOpenImmersion.lift _ l hrange, hleft, ?_⟩⟩
  -- `fac_right` cannot cancel `affineLineOver K`, which is not a mono.  Instead the two
  -- morphisms of AFFINE schemes agree after `Spec.map (algebraMap R L)`, and `algebraMap R L`
  -- is injective, so the ring maps behind them are equal.
  have key : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫
      (IsOpenImmersion.lift _ l hrange ≫ g) =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := by
    rw [← Category.assoc, hleft, S.commSq.w]
  have hpre : Spec.preimage (IsOpenImmersion.lift _ l hrange ≫ g) = Spec.preimage S.i₂ := by
    have h2 : Spec.map (Spec.preimage (IsOpenImmersion.lift _ l hrange ≫ g) ≫
          CommRingCat.ofHom (algebraMap S.R S.K)) =
        Spec.map (Spec.preimage S.i₂ ≫ CommRingCat.ofHom (algebraMap S.R S.K)) := by
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
      exact key
    have h3 := Spec.map_injective h2
    refine CommRingCat.hom_ext (RingHom.ext fun x => IsFractionRing.injective S.R S.K ?_)
    have h4 := congrArg
      (fun (f : CommRingCat.of (Polynomial K) ⟶ CommRingCat.of S.K) => f.hom x) h3
    simpa using h4
  rw [← Spec.map_preimage (IsOpenImmersion.lift _ l hrange ≫ g), hpre, Spec.map_preimage]

/-- **The compactification step: a quasi-finite `K`-morphism `X ∖ {z} ⟶ 𝔸¹_K` is proper**
(sorry leaf, cut 2026-07-28 out of
`isAffineOpen_compl_singleton_of_isSmoothProperCurve`).

TRUE.  Write `U = X ∖ {z}` and let `f ∈ Γ(X, U)` be the function `g` classifies.  The
intended proof is the valuative criterion, in two steps:

1. **`g` does not extend across `z`.**  If it did, the extension `ĝ : X ⟶ 𝔸¹_K` would be a
   `K`-morphism out of a proper `X`, hence proper (`IsProper.of_comp`, which cancels
   `IsProper` on the right
   against the separated `𝔸¹_K ⟶ Spec K`), and still quasi-finite, hence FINITE by
   `IsFinite.of_isProper_of_locallyQuasiFinite`.  A finite surjection onto `𝔸¹_K` from a
   universally closed `X` would make `𝔸¹_K ⟶ Spec K` universally closed, which it is not.
   So `f` has a genuine pole at `z`.
2. **The valuative criterion.**  Given a valuation ring `R` with fraction field `L` and a
   square `Spec L ⟶ U`, `Spec R ⟶ 𝔸¹_K`, properness of `X` over `K` lifts it to
   `Spec R ⟶ X`.  That lift cannot send the closed point of `Spec R` to `z`: the induced
   map on stalks `𝒪_{X,z} ⟶ R` is local, while `f` has negative valuation at `z` and its
   image in `L` lies in `R`.  So the lift factors through `U`, which is the required
   filler.

`exists_unique_extension_of_valuationRing_stalk` in `CurveExtension.lean` is PROVEN with no
sorry and supplies the extension machinery for step 1; the DVR-stalk hypothesis it needs is
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, also PROVEN there.

**`hqf` IS LOAD-BEARING and the statement is FALSE without it**: take `g` the constant
morphism `X ∖ {z} ⟶ 𝔸¹_K` at `0` (i.e. `f = 0`).  It is a `K`-morphism, and it is not
proper — it factors through the closed immersion `Spec K ↪ 𝔸¹_K`, so if it were proper then
`X ∖ {z} ⟶ Spec K` would be proper too (`IsProper` cancels on the right against a separated
morphism), making the affine-by-conclusion `X ∖ {z}` a proper positive-dimensional
`K`-scheme.  It is not: it is infinite and affine.

**`hover` IS LOAD-BEARING**: see `affineLineOver`.  Without it `g` need not be of finite
type over the base at all.

**`hz` IS LOAD-BEARING for a trivial reason**: `{z}ᶜ` must be open for `U` to be a scheme.

**`IsProper strX` IS LOAD-BEARING**: it is exactly what step 1 and step 2 both consume.  On
a non-proper curve the statement fails — remove two points instead of one and `g` extends
over the second puncture's neighbourhood without being proper.

NOT VACUOUS: `exists_locallyQuasiFinite_toAffineLine_compl_singleton` supplies a `g`
satisfying every hypothesis, and the projective model of an elliptic curve over `ℚ`
punctured at infinity, with `f = x`, witnesses the conclusion (there `g` is finite of
degree two).

## DECOMPOSED 2026-07-30 — everything except the valuative lift is now PROVEN

This declaration is no longer a bare `sorry`.  It is proven below over the single sub-leaf
`valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton`, along the
route the two steps above describe, and everything that is *not* step 2's lift is discharged
here: the pin's `IsProper.of_valuativeCriterion` (stacks `0BX5`) asks for `QuasiCompact`,
`QuasiSeparated` and `LocallyOfFiniteType` on `g` plus the two halves of the criterion, and
four of those five are free once one knows where to look.

* `LocallyOfFiniteType g` — from `hover` and `locallyOfFiniteType_of_comp`, the right
  cancellation, whose side condition is `LocallyOfFiniteType (affineLineOver K)`.  That is
  proven just above as `locallyOfFiniteType_affineLineOver`.
* `IsSeparated g` — from `hover` and `IsSeparated.of_comp`, which is UNCONDITIONAL: separated
  morphisms cancel on the left with no hypothesis on the second factor.
* `QuasiSeparated g` — an instance of `IsSeparated g` (`Morphisms/Separated.lean`).
* `QuasiCompact g` — `X` is a NOETHERIAN SCHEME, so its open `U` has a noetherian space and
  `quasiCompact_of_noetherianSpace_source` applies.  `IsNoetherian X` is
  `IsLocallyNoetherian X` (from `LocallyOfFiniteType.isLocallyNoetherian` against the
  noetherian `Spec K`) together with `CompactSpace X` (from `QuasiCompact strX`, both of
  which `IsProper strX` supplies).
* the UNIQUENESS half — `IsSeparated.valuativeCriterion`, from `IsSeparated g` again.

So the whole residue is the EXISTENCE half, and the sub-leaf is stated as exactly that.
`hconn` and `hqf` are not consumed here; they are exactly the hypotheses the sub-leaf needs,
and it is where the pole argument lives. -/
theorem isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X))
    (g : Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ⟶
        Spec (CommRingCat.of (Polynomial K)))
    (hqf : LocallyQuasiFinite g)
    (hover : g ≫ affineLineOver K =
      Scheme.Opens.ι (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) ≫ strX) :
    IsProper g := by
  haveI := locallyOfFiniteType_affineLineOver K
  -- `X` is a noetherian scheme, hence so is the open `U = X ∖ {z}`.
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace strX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
  haveI : IsNoetherian X := ⟨⟩
  haveI : NoetherianSpace
      (Scheme.Opens.toScheme (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) := by
    show NoetherianSpace (({z}ᶜ : Set X))
    infer_instance
  -- the three shape hypotheses of `IsProper.of_valuativeCriterion`
  haveI : QuasiCompact g := inferInstance
  haveI : LocallyOfFiniteType (g ≫ affineLineOver K) := by rw [hover]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (affineLineOver K)
  haveI : IsSeparated (g ≫ affineLineOver K) := by rw [hover]; infer_instance
  haveI : IsSeparated g := IsSeparated.of_comp g (affineLineOver K)
  haveI : QuasiSeparated g := inferInstance
  exact IsProper.of_valuativeCriterion g (ValuativeCriterion.iff.mpr
    ⟨valuativeCriterionExistence_of_locallyQuasiFinite_toAffineLine_compl_singleton
      strX hconn hz g hqf hover,
      IsSeparated.valuativeCriterion g⟩)

/-- **The complement of a closed point of a smooth proper geometrically connected curve
over a field is affine** (**PROVEN 2026-07-28** over the two sub-leaves immediately above —
this declaration has no `sorry` of its own any more).

TRUE and classical: `[z]` is a nonempty effective divisor on the integral projective curve
`X`, hence ample, hence the complement of its support is affine (Hartshorne IV.1, or the
Serre criterion applied to `O(n·[z])`).

**`hconn` IS LOAD-BEARING and the statement is FALSE without it.**  Take `X` the disjoint
union of two copies of a smooth proper curve and `z` a closed point of the first.  `X` is
still smooth of relative dimension one and still proper, `{z}` is still closed, and the
complement still contains the whole second copy — which is proper and positive-dimensional,
hence not affine, and an open subscheme with a proper positive-dimensional *component*
cannot be affine (its global sections would have to separate the points of that component,
but they are constant on it by properness).  Connectedness is exactly what forbids that.

**`SmoothOfRelativeDimension 1` IS LOAD-BEARING and the statement is FALSE without it.**
At relative dimension two the complement of a point on an abelian surface has the same
global sections as the surface (`K`, by properness), so it is not affine — not even
quasi-affine.  This is the same hypothesis, and the same counterexample, that separates
the curve case from the abelian-surface case in `exists_affineComplement_zeroSection`.

**`hz` IS LOAD-BEARING for a trivial reason**: `{z}ᶜ` has to be open before it can be an
affine *open*, and a scheme is only `T0`, so a point need not be closed.  In every intended
application `z` is the image of a rational point, and `isClosed_singleton_of_section`
supplies `hz`.

**`IsProper` is used by the intended ROUTE, not by the truth of the statement**: a smooth
connected curve that is *not* proper is already affine-by-compactification, since then the
compactification has a second missing point.  Do not drop it without a proof — the route
below goes through the projective model.

NOT VACUOUS: for `E` an elliptic curve over `ℚ`, `proj E` with `z` the point at infinity
satisfies every hypothesis, and the conclusion holds there with the affine chart
`Spec ℚ[E]` — see `exists_affineChart_projInfty` in
`Fermat/FLT/ModularCurve/EllipticScheme.lean`, which is PROVEN.  So the hypothesis set is
inhabited and the conclusion is not satisfiable only by junk.

WHAT WOULD REFUTE THE "MISSING FROM THE PIN" DIAGNOSIS: any declaration under
`Mathlib/AlgebraicGeometry/` concluding `IsAffineOpen` (or `IsAffine`) for an open
subscheme from a condition on its complement, or any ampleness of divisors.  Searched
2026-07-28 over `Fermat/`, `.lake/packages/mathlib` and `~/cs/FLT`: absent from all
three.

## PROOF (2026-07-28): Zariski's main theorem, not ampleness

The ampleness gap recorded above is real and is still open in the pin, but it never had to
be paid: `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` supplies the whole affineness
step.  Given the two sub-leaves — a quasi-finite `K`-morphism `g : X ∖ {z} ⟶ 𝔸¹_K`, and its
properness — `IsFinite.of_isProper_of_locallyQuasiFinite` (stacks `02LS`) makes `g` finite,
`IsFinite` extends `IsIntegralHom` which extends `IsAffineHom`, and `isAffine_of_isAffineHom`
against the affine target `Spec K[T]` gives `IsAffine` of the open subscheme — which is
what `IsAffineOpen` unfolds to.

The hypothesis analysis above is unchanged and still describes where each hypothesis is
consumed; all four are now consumed through the two sub-leaves rather than directly. -/
theorem isAffineOpen_compl_singleton_of_isSmoothProperCurve
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    {z : X} (hz : IsClosed ({z} : Set X)) :
    IsAffineOpen (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) := by
  obtain ⟨g, hqf, hover⟩ :=
    exists_locallyQuasiFinite_toAffineLine_compl_singleton strX hconn hz
  haveI := hqf
  haveI : IsProper g :=
    isProper_of_locallyQuasiFinite_toAffineLine_compl_singleton strX hconn hz g hqf hover
  haveI : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  exact isAffine_of_isAffineHom g

/-- **The complement of the image of a `K`-point of a smooth proper geometrically connected
curve is the range of an open immersion from an affine scheme** (PROVEN over the leaf
above).

This is the shape a consumer wants: it hands back a bare commutative ring together with an
open immersion of its spectrum onto the complement, which is exactly
`exists_affineComplement_zeroSection`'s conclusion.

**The `K`-ALGEBRA STRUCTURE AND THE STRUCTURE-MORPHISM CONJUNCT (added 2026-07-30) are
free, and they are what makes the statement usable over a base field that is not `ℚ`.**
Over `ℚ` a consumer could read the compatibility `ι ≫ strX = Spec (algebraMap ℚ R)` off
`hom_ext_spec_rat` — any two morphisms to `Spec ℚ` agree, `ℚ` being initial in `CommRing` —
so the conclusion did not have to carry it.  No other field is initial, so over a general
`K` the composite `ι ≫ strX` is *a* morphism to `Spec K` and has to be pinned.  It costs
nothing here: `Scheme.Spec` is fully faithful, so `ι ≫ strX` IS `Spec.map` of a unique ring
map `K → R` (`Spec.preimage`), and DECLARING that map to be the `K`-algebra structure of `R`
makes the conjunct `Spec.map_preimage`.  The algebra structure is therefore not a choice an
adversary could vary: it is the one induced by the chart's own structure morphism. -/
theorem exists_isOpenImmersion_range_eq_compl_of_section
    {K : Type u} [Field K] {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX]
    (hconn : GeometricallyConnected strX)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ strX = 𝟙 _) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra K R) (ι : Spec (CommRingCat.of R) ⟶ X),
      IsOpenImmersion ι ∧
        ι ≫ strX = Spec.map (CommRingCat.ofHom (algebraMap K R)) ∧
        Set.range ι.base = (Set.range s.base)ᶜ := by
  obtain ⟨z, hzr⟩ := range_eq_singleton_of_spec_field s
  have hz : IsClosed ({z} : Set X) := isClosed_singleton_of_section hs hzr
  have hU : IsAffineOpen (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens) :=
    isAffineOpen_compl_singleton_of_isSmoothProperCurve strX hconn hz
  letI alg : Algebra K Γ(X, (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)) :=
    (Spec.preimage (hU.fromSpec ≫ strX)).hom.toAlgebra
  refine ⟨Γ(X, (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)), inferInstance, alg,
    hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [show CommRingCat.ofHom
        (algebraMap K Γ(X, (⟨({z}ᶜ : Set X), hz.isOpen_compl⟩ : X.Opens)))
        = Spec.preimage (hU.fromSpec ≫ strX) from CommRingCat.ofHom_hom _,
      Spec.map_preimage]
  · rw [hU.range_fromSpec, hzr]
    rfl

end AlgebraicGeometry

/-! ### Recognising a Weierstrass coordinate ring from a surjection

The affine chart of a pointed genus-one curve is a Weierstrass coordinate ring.  That
statement splits cleanly in two, and only the FIRST half is Riemann–Roch:

1. the chart's ring is *generated by two elements satisfying a Weierstrass relation* —
   equivalently, some `E.toAffine.CoordinateRing` maps ONTO it.  This is where `L(2[O])`,
   `L(3[O])` and the seven-monomials-in-a-six-dimensional-space count live.
2. any such surjection is automatically INJECTIVE.  This half is pure commutative algebra
   and is proven below, so a prover at the chart need only produce the surjection.

And the *word* "equivalently" in item 1 is itself now discharged, by
`exists_surjective_coordinateRingHom_of_generators` below: two elements plus a relation plus
`Subring.closure … = ⊤` really do assemble into a surjection out of
`E.toAffine.CoordinateRing`, via `AdjoinRoot.lift`.  PROVEN 2026-07-28, no sorry.  So a
Riemann–Roch prover never has to touch `AdjoinRoot` or mathlib's coordinate-ring API at all:
it produces `x`, `y` and the relation, and everything else on both sides — surjectivity here,
injectivity below — is already paid for.
-/

/-- **A surjection from a Weierstrass coordinate ring onto a domain that is not a field is
injective** (PROVEN 2026-07-28) — so such a surjection is automatically a ring
isomorphism.

This is the algebraic half of "the affine chart of a pointed genus-one curve is a
Weierstrass coordinate ring": it removes the need for the geometric side to prove anything
about the KERNEL of the map it constructs.

The proof is Krull dimension in elementary form.  `C := E.toAffine.CoordinateRing` is a
free `k[X]`-module of rank two (`WeierstrassCurve.Affine.CoordinateRing.basis`), hence
integral over `k[X]`, hence `R` — a quotient of `C` — is integral over `k[X]` too.  Now
suppose the kernel contains some `a ≠ 0`.  The constant coefficient `c` of the minimal
polynomial of `a` over `k[X]` is nonzero (otherwise `divX` of it would be a monic
annihilator of strictly smaller degree, `C` being a domain and `a ≠ 0`), and
`c = -(a · …)` lies in the kernel.  So the kernel `P` of `k[X] → R` is a NONZERO prime;
`k[X]` is a PID, so `P` is maximal and `k[X]/P` is a field; and `R` is a domain integral
over a field, hence itself a field (`isField_of_isIntegral_of_isField'`) — contradicting
`hR`.

**`hR` IS LOAD-BEARING and the statement is FALSE without it**: `φ` may be the quotient
by any maximal ideal, e.g. `E.toAffine.CoordinateRing → k` evaluating at a `k`-rational
point of `E`.  That is a surjection onto a domain and is very far from injective.  What
`hR` says geometrically is that the target is a CURVE and not a point.

**`IsDomain R` IS LOAD-BEARING** in the same way — without it `φ` could be the quotient by
any ideal at all — and it is free in the intended application, where `Spec R` is an open
subscheme of an integral scheme.

NOT VACUOUS: for `E` elliptic over `ℚ`, the identity of `E.toAffine.CoordinateRing`
satisfies every hypothesis (the coordinate ring is a domain and is not a field, being a
one-dimensional domain), and the conclusion holds. -/
theorem injective_of_surjective_coordinateRing {k : Type u} [Field k]
    (E : WeierstrassCurve k) {R : Type v} [CommRing R] [IsDomain R] (hR : ¬ IsField R)
    (φ : E.toAffine.CoordinateRing →+* R) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  classical
  haveI hfin : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine)
  haveI : Algebra.IsIntegral k[X] E.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  letI : Algebra E.toAffine.CoordinateRing R := φ.toAlgebra
  letI : Algebra k[X] R := (φ.comp (algebraMap k[X] E.toAffine.CoordinateRing)).toAlgebra
  haveI : IsScalarTower k[X] E.toAffine.CoordinateRing R :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral k[X] R := by
    refine ⟨fun r => ?_⟩
    obtain ⟨x, rfl⟩ := hφ r
    exact (Algebra.IsIntegral.isIntegral (R := k[X]) x).map
      (IsScalarTower.toAlgHom k[X] E.toAffine.CoordinateRing R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hane
  have hint : IsIntegral k[X] a := Algebra.IsIntegral.isIntegral a
  have hmon : (minpoly k[X] a).Monic := minpoly.monic hint
  have hae : (Polynomial.aeval a) (minpoly k[X] a) = 0 := minpoly.aeval _ _
  -- the constant coefficient of the minimal polynomial is nonzero
  have hc : (minpoly k[X] a).coeff 0 ≠ 0 := by
    intro h0
    have hpx : Polynomial.X * (minpoly k[X] a).divX = minpoly k[X] a := by
      have h := Polynomial.X_mul_divX_add (minpoly k[X] a)
      rw [h0, map_zero, add_zero] at h
      exact h
    have hlead : (minpoly k[X] a).divX.leadingCoeff = 1 := by
      have h : (minpoly k[X] a).leadingCoeff = (minpoly k[X] a).divX.leadingCoeff := by
        conv_lhs => rw [← hpx]
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X, one_mul]
      rw [← h]; exact hmon
    have hmon' : (minpoly k[X] a).divX.Monic := hlead
    have hae' : (Polynomial.aeval a) (minpoly k[X] a).divX = 0 := by
      have hz : a * (Polynomial.aeval a) (minpoly k[X] a).divX = 0 := by
        conv_rhs => rw [← hae, ← hpx]
        simp
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hane
      · exact h
    exact absurd (minpoly.min k[X] a hmon' hae')
      (not_le.mpr (Polynomial.degree_divX_lt hmon.ne_zero))
  -- and it lies in the kernel of `k[X] → R`
  have hkey : algebraMap k[X] E.toAffine.CoordinateRing ((minpoly k[X] a).coeff 0)
      = -(a * (Polynomial.aeval a) (minpoly k[X] a).divX) := by
    have h := congrArg (Polynomial.aeval a) (Polynomial.X_mul_divX_add (minpoly k[X] a))
    rw [hae] at h
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    linear_combination h
  have hker : (algebraMap k[X] R) ((minpoly k[X] a).coeff 0) = 0 := by
    show φ (algebraMap k[X] E.toAffine.CoordinateRing ((minpoly k[X] a).coeff 0)) = 0
    rw [hkey, map_neg, map_mul, ha, zero_mul, neg_zero]
  -- so that kernel is a nonzero prime of a PID, hence maximal
  set P : Ideal k[X] := RingHom.ker (algebraMap k[X] R) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hPne : P ≠ ⊥ := by
    intro h
    have hmem : (minpoly k[X] a).coeff 0 ∈ P := RingHom.mem_ker.mpr hker
    rw [h, Ideal.mem_bot] at hmem
    exact hc hmem
  haveI : P.IsMaximal := _root_.IsPrime.to_maximal_ideal hPne
  letI : Field (k[X] ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (k[X] ⧸ P) R :=
    (Ideal.Quotient.lift P (algebraMap k[X] R) (fun _ hx => hx)).toAlgebra
  haveI : IsScalarTower k[X] (k[X] ⧸ P) R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral (k[X] ⧸ P) R := Algebra.IsIntegral.tower_top (R := k[X])
  exact hR (isField_of_isIntegral_of_isField' (R := k[X] ⧸ P) (Field.toIsField _))

/-- **Two generators satisfying a Weierstrass relation give a SURJECTION out of the
Weierstrass coordinate ring** (PROVEN 2026-07-28, no sorry) — the exact converse packaging
of `injective_of_surjective_coordinateRing` above.

Together the two mean that a Riemann–Roch prover at a pointed genus-one curve owes *only*
the elements: produce `x`, `y` and the relation, and the ring isomorphism
`R ≃+* E.toAffine.CoordinateRing` follows with no further work on either the kernel or the
image.

The proof is `AdjoinRoot.lift` applied to the two-stage evaluation
`k[X][Y] → R`, `X ↦ x`, `Y ↦ y`, `C ↦ c`; `hrel` is exactly the statement that
`E.toAffine.polynomial` evaluates to `0` there, and `hgen` says the image subring is
everything.

**BASE GENERALISED FROM `ℚ` TO AN ARBITRARY COMMUTATIVE RING `k`, AND THE `k`-LINEARITY
CONJUNCT ADDED, 2026-07-30.**  Nothing in the proof used anything about `ℚ`; what the
`ℚ`-only phrasing *did* buy is recorded in the paragraph the generalisation deletes, which
read: *"`c` NEEDS NO COMPATIBILITY CLAUSE, and that is not an oversight.  A ring
homomorphism out of `ℚ` is unique when it exists … so there is no freedom for an adversary
to supply a 'wrong' `c`."*  That is true of `ℚ` and of no other base, so the conclusion now
carries `hφ : ∀ a, φ (algebraMap k _ a) = c a` — i.e. `φ` is `k`-linear when `c` IS the
`k`-algebra structure map of `R`.  It is free: `AdjoinRoot.lift` sends `of f (C a)` to
`i (C a) = c a` by `AdjoinRoot.lift_of`, and `of f ∘ C` is the algebra map of the
coordinate ring by the scalar tower `k → k[X] → CoordinateRing`.

**`hgen` IS LOAD-BEARING and the statement is FALSE without it**: take `R` any `k`-algebra
strictly larger than the subring generated by some Weierstrass pair — e.g.
`R = E.toAffine.CoordinateRing[t]`, with `x`, `y` the images of the coordinates.  The
relation still holds and no surjection exists, since `φ` would then have to hit `t`.

**`hrel` IS LOAD-BEARING** trivially: without it there is no reason for any map out of
`AdjoinRoot E.toAffine.polynomial` to exist at all.

NOT VACUOUS: `R = E.toAffine.CoordinateRing` itself, with `c = algebraMap`, `x = X`,
`y = Y`, satisfies both hypotheses and the conclusion holds with the identity. -/
theorem exists_surjective_coordinateRingHom_of_generators {k : Type u} [CommRing k]
    {R : Type u} [CommRing R]
    (E : WeierstrassCurve k) (c : k →+* R) (x y : R)
    (hrel : y ^ 2 + (c E.a₁ * x + c E.a₃) * y
      = x ^ 3 + c E.a₂ * x ^ 2 + c E.a₄ * x + c E.a₆)
    (hgen : Subring.closure (Set.range c ∪ {x, y}) = ⊤) :
    ∃ φ : E.toAffine.CoordinateRing →+* R, Function.Surjective φ ∧
      ∀ a : k, φ (algebraMap k E.toAffine.CoordinateRing a) = c a := by
  classical
  set i : k[X] →+* R := Polynomial.eval₂RingHom c x with hi
  have hroot : (E.toAffine.polynomial).eval₂ i y = 0 := by
    simp only [WeierstrassCurve.Affine.polynomial, hi, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom]
    linear_combination hrel
  refine ⟨AdjoinRoot.lift i y hroot, ?_, ?_⟩
  · rw [← RingHom.range_eq_top, eq_top_iff, ← hgen]
    refine Subring.closure_le.mpr ?_
    rintro r (⟨q, rfl⟩ | rfl | rfl)
    · exact ⟨AdjoinRoot.of _ (Polynomial.C q), by simp [hi]⟩
    · exact ⟨AdjoinRoot.of _ Polynomial.X, by simp [hi]⟩
    · exact ⟨AdjoinRoot.root _, by simp⟩
  · intro a
    have hof : algebraMap k E.toAffine.CoordinateRing a
        = AdjoinRoot.of E.toAffine.polynomial (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k k[X] E.toAffine.CoordinateRing,
        AdjoinRoot.algebraMap_eq]
      simp
    rw [hof, AdjoinRoot.lift_of, hi]
    simp
