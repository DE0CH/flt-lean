/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced

/-!
# Coherent pushforward along a proper morphism: `f_*𝒪_X = 𝒪_S`, and the rigidity lemma

For a **proper flat** morphism of finite presentation `f : X ⟶ S` whose fibres are
**geometrically connected and geometrically reduced**, the unit
`𝒪_S ⟶ f_*𝒪_X` is an isomorphism, and stays one after every base change
(Hartshorne III.12, Mumford *Abelian Varieties* §5, Stacks 0E6R / 0BUG).  This is the
single classical input behind every rigidity statement about abelian schemes, and it is
absent from `Mathlib` at this pin, from `~/cs/FLT`, and from this project — checked
2026-07-27 by grepping all three for `higherDirectImage`, `directImage` and any
cohomology-and-base-change API: there are **zero hits**, and `Mathlib` has no higher
direct images of quasi-coherent sheaves at all.

**That absence claim is about POSITIVE degree only, and a 2026-07-28 re-check narrowed it.**
In degree zero `Mathlib` *does* have flat base change, as `pushoutSection` and
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` in
`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`, which give
`Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤) ≅ Γ(X ×_S T, ⊤)` for `X` qcqs over an affine base and `T ⟶ S` flat.
That is what closed the whole fibrewise half of this file.  Anyone reading the paragraph above
as "no base change of any kind exists" will rebuild machinery that is already here — the grep to
run is for `pushoutSection`, not for `directImage`.

## What is here

* `AlgebraicGeometry.HasTrivialPushforward f` — the statement `𝒪_S ≅ f_*𝒪_X`, written as
  "`f.app U` is an isomorphism for every open `U ⊆ S`".  That is literally the assertion
  that the map of sheaves `𝒪_S ⟶ f_*𝒪_X` — whose component at `U` *is* `f.app U`, by
  `Scheme.Hom.app` — is an isomorphism, so no separate sheaf-level definition is needed.
* `AlgebraicGeometry.HasUniversallyTrivialPushforward f` — the same, universally.  The
  universal form is the one the rigidity lemma consumes: its proof base-changes `f` along
  an arbitrary `Y ⟶ S`, and `𝒪_S = f_*𝒪_X` alone does not survive that (it does under
  flatness + geometric connectedness + geometric reducedness, which is exactly what the
  main theorem below asserts).
* `isIso_appTop_of_isIso_app_affineOpens` — **PROVEN**: `f.appTop` is an isomorphism as soon
  as `f.app U` is for every *affine* open `U ⊆ S`.  Pure sheaf theory (`f.app U` is the
  component at `U` of `𝒪_S ⟶ f_*𝒪_X`, and the affine opens are a basis), and it is what
  lets the remaining leaf be stated over an affine base.
* `isIso_appTop_of_isProper_over_field` — **PROVEN, no leaf under it** (2026-07-28):
  `H⁰(Z, 𝒪_Z) = K` for `Z` proper, geometrically connected and geometrically reduced over a field
  `K`.  **Its hypothesis was `[Field K]`, which made the statement FALSE** — for
  `K : CommRingCat` that binder is a field structure on the carrier *type*, unrelated to `K`'s
  ring structure; see the falsity audit on the declaration for the `ZMod 4` counterexample.  It
  now carries `hK : IsField K`.  Proven en route, and useful on their own:
  * `exists_eq_sq_mul_of_isIntegral` — a reduced ring is von Neumann regular at every element
    integral over a field;
  * `isField_of_isIntegral_of_forall_isIdempotentElem` — hence such a ring with no nontrivial
    idempotents is a field, with **no finiteness and no irreducibility**, which is what
    `Mathlib`'s `isField_of_universallyClosed` needs `[IsIntegral X]` for;
  * `isIdempotentElem_appTop_eq_zero_or_one` — `Γ` of a connected reduced scheme has no
    nontrivial idempotents;
  * `isField_appTop_of_universallyClosed` and
    `isIso_appTop_of_universallyClosed_of_isAlgClosed` — `Γ(Z, ⊤)` is a field, and equals `K`
    when `K` is algebraically closed.
* `isIso_appTop_of_isIso_appTop_baseChange` — **PROVEN** (2026-07-28): flat base change for `H⁰`
  along a field extension, in transfer form.  **Contrary to what this docstring used to say,
  `Mathlib` HAS the base-change machinery for global sections** —
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` in
  `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` gives
  `Γ(Z, ⊤) ⊗_K L ≅ Γ(Z ×_K Spec L, ⊤)` directly.  What `Mathlib` lacks is *higher* direct
  images, which is a different statement; the note below about "zero hits" is about those.
  Supporting lemmas, both PROVEN: `isIso_of_isPushout_of_isField` (faithfully flat descent of
  isomorphisms along a field extension, in pushout form) and
  `bijective_algebraMap_of_bijective_includeLeft` (a `K`-algebra whose base change to `L` is `L`
  is `K`).
* `isIso_appTop_of_isIso_appTop_fiber` — **PROVEN** (2026-07-28): degree-zero cohomology and
  base change.  For `f` proper, flat and of finite presentation over an **affine** base,
  `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism as soon as `κ(s) ⟶ Γ(X_s, ⊤)` is one for every
  `s ∈ S`.  Geometric connectedness and reducedness do not appear: they enter only through
  the fibrewise hypothesis.  Proven over the two leaves below plus a fully proven
  commutative-algebra assembly (Nakayama on the cokernel; the equational criterion for
  flatness on the kernel):
  * `module_finite_appTop_of_isProper` — **PROVEN** (2026-07-28): `Γ(X, ⊤)` is a finite
    `Γ(S, ⊤)`-module — Grothendieck's finiteness theorem for a proper morphism, in degree
    `0` — over the single leaf `finiteType_appTop_of_isProper`, since
    `finite = integral + finite type` and the integral half is already in the pin
    (`isIntegral_appTop_of_universallyClosed`).  **RESTATED 2026-07-29** to carry the
    fibrewise hypothesis `h`, inherited from the leaf below.
  * `finiteType_appTop_of_isProper` — was the LEAF (2026-07-28), **REFUTED AND RESTATED
    2026-07-29**, **PROVEN 2026-07-30** over `adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber`
    below: `Γ(X, ⊤)` is a finite-TYPE `Γ(S, ⊤)`-algebra **under the fibrewise hypothesis `h`**.
    Without `h` the statement is FALSE over a non-noetherian base — audit block (A) in its
    docstring gives the witness in full (a wild multiple fibre of `(E × P¹)/(ℤ/2)` in char `2`
    puts `t`-torsion in `H¹(𝒪)`, and `R = k[t, x₁, x₂, …]/(t·xᵢ)` turns that torsion into a
    non-finitely-generated `Tor₁` inside `Γ(X, 𝒪_X)`).  With `h` it is the constant-`h⁰` case
    of cohomology and base change, true over an arbitrary base, and all three call sites
    already had `h`.  Audit block (D) carries the two results the proof came out of: (D1) the
    obvious shortcut — derive `A = R` from integrality plus `A = R + 𝔪A` and skip the Nakayama
    block — is REFUTED by `A = ℤ_p ⋉ ℚ_p`, so the leaf could not be dodged by re-ordering the
    file; (D2) the route that worked, via the proper surjection `X ⟶ Spec R[a]`.
  * `adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` — **PROVEN** (2026-07-30) over
    `mem_smul_adjoin_of_appTop_fiberι_eq_zero` below: `R[a] = R·1 + 𝔪·R[a]` for every
    `a : Γ(X, ⊤)` and every maximal `𝔪`.  This is leaf 3's degree-zero base-change injectivity
    with `Γ(X, ⊤)` replaced by a **finite** subalgebra of it, which is what makes it reachable
    without limit theory: integrality makes `R[a]` a finite `R`-module, so
    `eq_bot_of_fg_of_le_smul_of_forall_isMaximal` applies to it and nothing needs
    `Module.Finite ↥Γ(S,⊤) ↥Γ(X,⊤)`.
  * `mem_smul_adjoin_of_appTop_fiberι_eq_zero` — **PROVEN** (2026-07-30) over the leaf below:
    a section of `R[a]` that RESTRICTS TO ZERO on the fibre `X_s` lies in `𝔪·R[a]`.  All the
    theorem above adds is the lift-and-subtract step, which the maximal-ideal ↔ point
    dictionary (`exists_point_ker_Γevaluation_eq_of_isMaximal`,
    `surjective_appTop_fiberι_comp_appTop`, both PROVEN 2026-07-30) discharges.
  * `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero` — **LEAF** (RE-CUT 2026-07-30 out of
    the theorem above), and as of that re-cut **the ONLY leaf in this file**: if `a` itself
    restricts to zero on `X_s` then `a ∈ 𝔪·R[a]`.  It carries both of the leaves this file
    had before, and they are three-line corollaries of it — the general `x ∈ R[a]` form
    because **`x` is its own `a`** (apply the leaf to `x`, then `R[x] ≤ R[a]`), and the
    `Γ(X, ⊤)` form (`mem_smul_top_of_appTop_fiberι_eq_zero`) because `R[a] ≤ ⊤`.  The two
    were never two obligations: the old docstrings had checked only that the `Γ(X, ⊤)`
    statement does not imply the `R[a]` statement (it does not — `𝔪A ∩ R[a] ⊆ 𝔪·R[a]` is
    refuted by audit block (D1)) and concluded neither subsumed the other, missing that the
    implication is free in the other direction.  Its docstring says what remains geometrically
    (the fibres of `Spec R[a] ⟶ S` are single `κ(𝔪)`-points; show they are REDUCED), records
    exactly where integrality alone stops, warns against the abstract weakening
    `a ∈ 𝔪·Γ(X, ⊤)`, which is false, and warns against generalising to an arbitrary subalgebra
    `B`, which is not known and which the corollaries above do not use.
  * `surjective_quotientMap_appTop_of_isIso_appTop_fiber` — **PROVEN** (2026-07-28) over the
    leaf below: `R/𝔪 ⟶ A/𝔪A` is SURJECTIVE at every maximal ideal.  All this adds to the
    leaf is linear algebra over the field `R/𝔪` — a nonzero vector in a space of dimension
    at most one spans it — with the injection `R/𝔪 ↪ A/𝔪A` coming from lying over.
  * `rank_quotient_appTop_le_one_of_isIso_appTop_fiber` — **PROVEN** (2026-07-28):
    `dim_{R/𝔪} A/𝔪A ≤ 1` at every maximal ideal, equivalently the degree-zero comparison
    map `A ⊗_R κ(s) ⟶ H⁰(X_s, 𝒪)` is INJECTIVE.  This is Hartshorne III.12.11(a) /
    EGA III 7.8.6 in degree `0`, i.e. the *whole* of cohomology and base change left in this
    file, and it is now cut into the two leaves below plus a proven bridge
    (`rank_quotient_le_one_of_fibre_span`).  The introduction to that block carries the
    obstruction analysis — why no point-set, localization, completion or Stein-factorization
    argument closes it — and a 2026-07-28 pin re-check run in **mathlib's** vocabulary
    rather than this project's.
  * `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` — **PROVEN** (2026-07-30) over
    `mem_smul_top_of_appTop_fiberι_eq_zero` below, by the same dictionary: the equation
    `Γ(X, ⊤) = R·1 + 𝔪·Γ(X, ⊤)` at every maximal `𝔪`, i.e. Nakayama's input.
  * `mem_smul_top_of_appTop_fiberι_eq_zero` — **PROVEN** (2026-07-30) over
    `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero` above, since `R[a] ≤ ⊤`: a global
    section that RESTRICTS TO ZERO on the fibre `X_s` lies in `𝔪·Γ(X, ⊤)`; in sheaf language
    `Γ(X, 𝔪𝒪_X) ⊆ 𝔪·Γ(X, 𝒪_X)`.  **Its docstring carries a Čech/`Tor` analysis (2026-07-30)
    which is now a RECORD rather than a task — it is a route to this statement only, and
    `R[a]` is a subalgebra of `ker d` rather than a term of the complex, so it does not
    transfer to the leaf.**  What it establishes: for the Čech
    complex of a finite affine cover, the FIBRE CLAUSE is free from `h` — it is exactly
    `Tor₁(F₁/range d, κ(𝔪)) = 0` — and this leaf is exactly `Tor₁(range d, κ(𝔪)) = 0`, which
    differs from it by ONE application of the local criterion.  So the whole remaining gap is
    **finite presentation of the Čech cokernel, i.e. Grothendieck finiteness in POSITIVE
    degree** (`H¹(X, 𝒪_X)` for a two-element cover), not a limit theory.  It also records two
    free cases: a `𝔪` generated by a nonzerodivisor needs no cohomology at all (flatness makes
    `𝒪_X ≅ t𝒪_X`), and `𝔪` may always be replaced by a finitely generated sub-ideal.
    The **elementary route** recorded on the equation above remains as it was —
    localise, dévissage of `Γ(X, J𝒪_X)` along a
    composition series, and an induction on `dim R` using a nonzerodivisor (with the
    `𝔪`-power torsion handled separately in the depth-zero case).  That route uses **no
    higher cohomology, no Grothendieck complex and no theorem on formal functions**; it does
    need a NOETHERIAN base.  **Corrected 2026-07-29:** this used to read "the same gap
    already recorded for `finiteType_appTop_of_isProper`, so one limit-theory build unlocks
    both remaining leaves".  The two gaps are NOT the same.  This leaf already carries `h`,
    so its statement is TRUE over an arbitrary base — the noetherian hypothesis is a
    limitation of the *route*, and a limit/approximation argument really would close it.
    `finiteType_appTop_of_isProper`'s missing noetherian hypothesis was FATAL: without `h`
    that statement is false over a non-noetherian base (witness in its docstring), and no
    limit theory could ever have closed it.  `h` has now been added there too, which makes
    the two gaps genuinely the same kind — but only after the repair, not before.
  * `exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` — **PROVEN**
    (2026-07-29) over the leaf above, by the witness `C₀ = C₁ = Γ(X, ⊤)`, `d = 0` that its
    own non-vacuity paragraph had already identified.  It used to be the leaf, in the shape
    "there are `R`-modules and a `d : C₀ ⟶ C₁` with `range d` FLAT, `Γ(X, ⊤) ≃ₗ ker d`, and
    the same `d` computing `H⁰` of every fibre after reduction mod `𝔪`".  The complex, the
    flatness clause and the `LinearEquiv` were bookkeeping around the equation above.
  * `exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber` — **PROVEN**
    (2026-07-28) over the leaf above.  It used to BE the leaf, demanding Grothendieck's
    finite free complex; that shape turned out to be strictly more than the consumer needs.
    Finite freeness is a vehicle for one conclusion, `ker d ∩ 𝔪C₀ ≤ 𝔪·ker d`, and that
    follows from flatness of `range d` alone with no finiteness whatever
    (`inf_smul_top_le_smul_ker_of_flat_range`).  Once the leaf is known, `A ≅ R` and the
    complex may be taken to be `R^1 ⟶ R^0`.
  * `inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le` — **PROVEN** (2026-07-28), pure
    commutative algebra with no geometry in it at all: for `d : R^{n₀} ⟶ R^{n₁}` between
    finite free modules, if `K/𝔪K ⟶ ker(d mod 𝔪)` is surjective at every maximal ideal then
    it is injective.  Tor-theoretically: the hypothesis is `Tor₁(R^{n₁}/range d, R/𝔪) = 0`,
    which makes that finitely presented module flat by the local criterion, hence `range d`
    flat, hence `Tor₁(range d, R/𝔪) = 0`, which is the conclusion.  No noetherian hypothesis
    is needed.  This one could be upstreamed unchanged.

  Two leaves that used to sit here are now **PROVEN** (2026-07-28), both from elementary
  consequences of `h` rather than from III.12.11:
  * `bijective_quotientMap_appTop_of_isIso_appTop_fiber` — the injective half is
    `comap_map_appTop_eq_of_isIso_appTop_fiber`, i.e. LYING OVER: `h` forces `f` surjective
    (`surjective_of_isIso_appTop_fiber`), hence `Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤)` surjective
    (`surjective_comap_appTop_of_isAffine`), hence `φ⁻¹(𝔪A) = 𝔪`.
  * `module_flat_appTop_of_isIso_appTop_fiber` — III.12.11(b) is **not needed anywhere**.
    Its only consumer wanted `Module.Flat R A` in order to get `φ` injective, and injectivity
    comes far more cheaply from flatness of the MORPHISM: a flat surjective morphism is
    faithfully flat on stalks, so `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is injective
    (`injective_appTop_of_flat_of_surjective`).  With surjectivity of `φ` from Nakayama, `φ`
    is bijective and `A ≃ₗ[R] R` is flat outright.

  The commutative algebra — `eq_bot_of_fg_of_le_smul_of_forall_isMaximal`,
  `surjective_algebraMap_of_finite_of_forall_isMaximal`,
  `injective_algebraMap_of_flat_of_ker_le_jacobson` and
  `bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap` — is proven here and is
  pure `RingTheory`; it could be hoisted to a shim file unchanged.
* `isIso_appTop_of_isProper_of_flat_of_isAffine` — **PROVEN** over those two, by feeding the
  first into the second (every fibre is a base change of `f`).
* `isIso_appTop_of_isProper_of_flat` — **PROVEN** over it, by the affine reduction.
* `hasUniversallyTrivialPushforward_of_isProper_of_flat` — **PROVEN** over it too.  Both
  of the theorem's quantifiers turned out to be bookkeeping rather than mathematics: all
  five hypotheses are stable under base change, and an open restriction `f ∣_ U` is itself
  a base change (`isPullback_morphismRestrict`), so `∀ U, IsIso (f.app U)` *and* the
  `universally` wrapper both reduce to the single global-sections statement above.
* `hasUniversallyTrivialPushforward_of_isProper_of_smooth` — PROVEN from the leaf above
  together with `AlgebraicGeometry.GeometricallyReduced.of_smooth`.  This is the form
  every consumer in this development actually applies, because an abelian scheme and a
  smooth proper curve are both given as *smooth* rather than as *flat with reduced
  fibres*.
* `HasTrivialPushforward.existsUnique_comp_eq` and
  `existsUnique_comp_eq_of_hasTrivialPushforward` — **PROVEN** (two independently
  developed forms of one statement, merged from two branches): an `S`-morphism from `X`
  to an AFFINE scheme factors uniquely through `S`.  This is the corollary of
  `p_*𝒪_X = 𝒪_S` that the rigidity lemma consumes, and it is pure `Γ ⊣ Spec` formalism.
* `existsUnique_comp_snd_eq_of_spec` and `exists_comp_snd_eq_of_isAffine` — **PROVEN**:
  the rigidity lemma for an AFFINE target, where it needs neither the contracted slice
  nor connectedness of `q`.
* `exists_comp_snd_eq_of_isAffine_pullback` — PROVEN: **rigidity with a target AFFINE OVER
  THE BASE**, i.e. whenever `Y ×_S Z` is affine (in particular for `[IsAffine Y]`
  `[IsAffineHom r]`).  This is the form the classical proof consumes.
* `surjective_of_hasUniversallyTrivialPushforward`, `eq_of_comp_eq_of_hasTrivialPushforward`
  and `eq_of_comp_snd_eq` — **PROVEN**: `𝒪_S = p_*𝒪_X` universally makes `p` SURJECTIVE
  (base change along `Spec κ(s) ⟶ S`; an empty fibre would give `κ(s) ≅ Γ(∅, ⊤) = 0`), and
  surjectivity upgrades the affine-target injectivity to an arbitrary target, so
  `pullback.snd p q` is an EPIMORPHISM.  This is the uniqueness the gluing step runs on.
* `isPullback_sliceOverOpen` — **PROVEN**: `X ×_S V` is the part of `X ×_S Y` over `V`, i.e.
  `sliceOverOpen` sits in a cartesian square over `V.ι`; in particular it is an open
  immersion.
* `exists_comp_snd_eq_of_slice_const` — the RIGIDITY LEMMA (Mumford *AV* §4;
  BLR *Néron Models* 8.4 in the relative case), PROVEN over the single leaf below.
* `exists_comp_snd_eq_of_open_cover` — **PROVEN**: local factorizations through the
  projection, over an open cover of `Y`, glue to a global one.  Overlaps agree by
  `eq_of_comp_snd_eq`; the assembly is `Scheme.Cover.glueMorphisms` on
  `Y.openCoverOfIsOpenCover`, checked against the pullback of that cover along
  `pullback.snd p q` via `isPullback_sliceOverOpen`.
* `exists_isAffineOver_cover_of_slice_const` — **PROVEN** from the pointwise form below, by
  indexing the cover by the points of `Y`.
* `exists_isAffineOver_nbhd_of_slice_const` — **PROVEN** from the leaf below by
  `IsOpenImmersion.lift`: at each point `y : Y` there is an open `V ∋ y` over which `m`
  factors through a scheme affine over the base.
* `exists_isAffineOpen_slice_nbhd_of_slice_const` — **PROVEN** (2026-07-28): at each
  `y : Y` there are an open `V ∋ y` in `Y` and an open `U ⊆ Z` with `V ×_S U` affine and
  `range (X ×_S V ⟶ Z) ⊆ U`.  This is where properness of `pullback.snd`, the section `σ`
  and `[GeometricallyConnected q]` are consumed.  Its properness half is
  `isOpen_setOf_slice_mapsTo` (the tube lemma, PROVEN), its packaging is
  `mem_sliceGoodLocus_of_mem_sliceContractedLocus` (PROVEN), the converse identification
  of the two loci is `sliceContractedLocus_of_sliceGoodLocus` (PROVEN, and the place where
  `hpush` is spent), the base point is `slice_const_of_section` (PROVEN, over
  `isPullback_sliceIncl`: the slice cut out by a section is the base change of that
  section), and the clopen argument is `mem_sliceGoodLocus_of_slice_const` (PROVEN).
* `isClosed_sliceContractedLocus_fiber` — **PROVEN** (2026-07-28): the locus of `y : Y`
  whose slice `m` contracts to a point is CLOSED IN EACH FIBRE of `q`.  This is the
  semicontinuity half, and it closes the rigidity lemma: **the whole rigidity cone is free of
  `sorry` apart from the `hpush` hypothesis it takes in.**  (This bullet used to name
  `isIso_appTop_of_isProper_of_flat` as "the only `sorry` anywhere in this file's cone".
  That was false in both halves and is corrected here, 2026-07-28: that theorem is PROVEN,
  by a tactic proof containing no `sorry`.  Anyone dispatched at the old name finds nothing
  to do.  **Re-counted 2026-07-30:** this bullet then named the open leaves as
  `finiteType_appTop_of_isProper` and
  `surjective_quotientMap_appTop_of_isIso_appTop_fiber`, and the second has since been
  PROVEN, and `finiteType_appTop_of_isProper` has been proven since; then
  `adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` and
  `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`, and **both of those have since been
  proven too** (2026-07-30, second pass).  It then named
  `mem_smul_adjoin_of_appTop_fiberι_eq_zero` and `mem_smul_top_of_appTop_fiberι_eq_zero`, the
  fibre-vanishing forms of the same two statements, and **both of those are now proven as well**
  (2026-07-30, third pass) over the single one-element leaf
  `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero`, which is the current set and has one
  member.  Read it off the compiler's warning set, not off this bullet.)  The mechanism is that the
  projection away from
  `X ×_S X` is an OPEN map once restricted to a fibre of `q`, because everything there is
  flat over the field `κ(s)`; the input is `Mathlib`'s
  `instance [IsIntegral Y] [Subsingleton Y] : UniversallyOpen f` — *any* morphism to the
  spectrum of a field is universally open — packaged here as
  `universallyOpen_of_isPullback_residueField`.  **No flatness hypothesis on `p` is needed
  or used.**

## `geometricallyReduced_of_smooth` WAS A DUPLICATE LEAF, and has been deleted (2026-07-27)

This file used to carry its own sorried `geometricallyReduced_of_smooth`, described as
"small and separate".  Both halves of that description were wrong, and the leaf was
redundant:

* it is **not small** — mathlib's `IsRegularLocalRing` API is two files with no
  `IsRegularLocalRing → IsDomain` and no link to smoothness at all, so the classical
  "smooth ⟹ regular ⟹ reduced" route has *both* implications missing at this pin;
* it was **already decomposed elsewhere in this project**, in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`, where
  `GeometricallyReduced.of_smooth` is PROVEN over the ring-theoretic leaf
  `Algebra.Smooth.isReduced_of_isField` — which is where the content actually lives, and
  which carries a full absence audit.

So this file now imports that one and consumes `GeometricallyReduced.of_smooth`.  Anyone
tempted to restate a smoothness-to-reducedness fact here should grep
`isReduced_of_smooth_over_field` first.
* `eq_comp_of_rigidity_axes` — PROVEN from the rigidity lemma: a morphism
  `A ×_S A ⟶ B` vanishing on both axes vanishes.  This is the form in which rigidity is
  used to prove that a pointed morphism of abelian schemes is a homomorphism.

## The cut of the rigidity lemma, and why it is where it is (2026-07-27)

The affine-target case is **not** a special case that has to wait for the topology: it is
complete, and it consumes the ENTIRE pushforward hypothesis.  What the section `σ`, the
properness of the projection and the connectedness of the fibres of `q` are actually for is
the single statement *"`m` maps each `q`-fibre into a piece of `Z` that is affine over the
base"* — the topological argument runs there and nowhere else.  So the leaf splits into

1. **the covering** (`exists_isAffineOver_cover_of_slice_const`) — genuinely the classical
   argument: `pullback.snd p q` is proper (base change of `p`), so the image of
   `m ⁻¹(Z ∖ U)` is closed in `Y` and misses `σ(S)`; the resulting open `V` is where the
   affine case applies, and `GeometricallyConnected q` is what makes the `V`s cover `Y`
   rather than a proper clopen part of it (see the FAITHFULNESS NOTE — with `Y` two points
   they do not);
2. **the gluing** (`exists_comp_snd_eq_of_open_cover`) — bookkeeping, but not free: the local
   factorizations agree on overlaps because `HasUniversallyTrivialPushforward p` makes the
   factorization through the projection UNIQUE (`exists_comp_snd_eq_of_isAffine` is stated as
   an `∃!` for exactly this reason).

**UPDATE (2026-07-27): (2) IS CLOSED, AND (1) HAS BEEN LOCALISED TO A POINT.**  The gluing
is proven, and what it cost is recorded because it is the reusable part: the uniqueness it
needs is the statement that `pullback.snd p q` is an EPIMORPHISM OF SCHEMES, which does NOT
follow from `HasTrivialPushforward` alone (Hartogs: `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ 0}` for a
non-surjective `j`).  It follows from the UNIVERSAL form, which forces `p` to be surjective
by base change along `Spec κ(s) ⟶ S` — an empty fibre would make the field `κ(s)` a zero
ring.  Surjectivity then upgrades `eq_of_comp_eq_of_isAffine` to an arbitrary target
because it makes two candidate factorizations agree on points, hence have the same
preimage of each affine open of `Z`.  So the `∃!` in the affine case is not merely
convenient — the general uniqueness is a theorem with real content, and it is now
`eq_of_comp_snd_eq`.

(1) has in turn been peeled twice.  First to `exists_isAffineOver_nbhd_of_slice_const` —
the same statement at ONE point of `Y` — plus a proven assembly that indexes the cover by
the points of `Y`; then to `exists_isAffineOpen_slice_nbhd_of_slice_const`, which drops the
morphism data entirely and asks only for two OPENS (`V ∋ y` in `Y` and `U` in `Z`) with
`V ×_S U` affine and `m(X ×_S V) ⊆ U`, the factorizing morphism being recovered by
`IsOpenImmersion.lift`.  The remaining leaf therefore carries exactly the geometry
(properness ⟹ closed map; the `GeometricallyConnected` clopen argument) and none of the
bookkeeping.

**UPDATE (2026-07-28): THE RIGIDITY LEMMA IS CLOSED.**  `IsProper ⟹ IsClosedMap` for the
base-changed projection is `isOpen_setOf_slice_mapsTo`, the `GeometricallyConnected` clopen
argument is `mem_sliceGoodLocus_of_slice_const`, and
`exists_isAffineOpen_slice_nbhd_of_slice_const` is PROVEN from them.  The step the earlier
notes did not identify is the OTHER half of "clopen": the contracted locus must be closed
in each fibre of `q`.  That is not packaging but genuine geometry — semicontinuity of
"constant along the slice" — and it is proven as
`isClosed_sliceContractedLocus_fiber`, by restricting to the scheme-theoretic fibre, where
the projection away from `X ×_S X` becomes an open map because everything is flat over the
residue FIELD `κ(s)`.

Note the earlier note above got the shape of half (2) wrong, and the error is worth keeping
visible: "running (1) at every point of that locus shows it is also closed in each fibre"
is FALSE — running (1) again gives openness a second time, never closedness.  Closedness is
the semicontinuity statement and needs the flat-over-a-field input; there is no way to get
it out of properness alone.

The leaves are stated with `sliceOverOpen p q V : X ×_S V ⟶ X ×_S Y`, the canonical map
induced by an open `V ⊆ Y`.

## FAITHFULNESS NOTE on the rigidity lemma: the second factor MUST be connected

The rigidity lemma is often quoted with `Y` an arbitrary `S`-scheme.  In that generality
it is **FALSE**, and the counterexample is one line: take `S = Spec k`, `X = ℙ¹`,
`Y = Spec k ⊔ Spec k = {y₀, y₁}`, `Z = ℙ¹`, and `m : X ×_S Y ⟶ Z` equal to a constant on
`X × {y₀}` and to the identity on `X × {y₁}`.  Every hypothesis holds — `X` is proper with
`H⁰(X, 𝒪) = k`, `Z` is separated, `m` contracts the slice over `y₀` — and `m` does not
factor through `Y`.  What fails is that the locus of `y` whose slice is contracted is open
and closed but not everything.

So `exists_comp_snd_eq_of_slice_const` carries `[GeometricallyConnected q]`.  That costs
nothing at the point of use: in the abelian-scheme application both factors are the same
abelian scheme `A`, whose `AbelianSchemeStruct.connected` field is exactly this
hypothesis.

## Statement of the pushforward theorem, and why it is stated universally

`HasTrivialPushforward` is not stable under base change on its own — `f_*𝒪_X` need not
commute with base change for a general proper `f`.  It does when `f` is flat with
geometrically connected and geometrically reduced fibres, because then `f_*𝒪_X` is
locally free of rank one with formation commuting with base change (cohomology and base
change, Hartshorne III.12.11 / Grauert), and the unit is an isomorphism fibrewise by
`H⁰(X_s, 𝒪) = κ(s)` for a proper, geometrically connected, geometrically reduced `X_s`.
That is why the theorem below concludes the UNIVERSAL form directly: the universality is
not a strengthening bolted on afterwards, it is what the proof produces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-! ### The pushforward condition -/

/-- **`𝒪_S ⟶ f_*𝒪_X` is an isomorphism**, written as: `f.app U : Γ(S, U) ⟶ Γ(X, f⁻¹U)` is
an isomorphism for every open `U ⊆ S`.

`f.app U` is by definition the component at `U` of the map of sheaves `𝒪_S ⟶ f_*𝒪_X`
carried by `f`, so this really is the statement `f_*𝒪_X = 𝒪_S` and not a weakening of
it. -/
def HasTrivialPushforward (f : X ⟶ S) : Prop :=
  ∀ U : S.Opens, IsIso (f.app U)

/-- `HasTrivialPushforward` packaged as a `MorphismProperty`, so that `Mathlib`'s
`MorphismProperty.universally` can be applied to it. -/
def hasTrivialPushforwardProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ HasTrivialPushforward f

/-- **`𝒪_S ⟶ f_*𝒪_X` is an isomorphism, and remains one after every base change.**

This is the hypothesis the rigidity lemma needs: its proof base-changes the proper
morphism along an arbitrary test scheme, and `f_*𝒪_X = 𝒪_S` for one `f` says nothing
about the base changes of `f`. -/
def HasUniversallyTrivialPushforward (f : X ⟶ S) : Prop :=
  hasTrivialPushforwardProperty.universally f

theorem HasUniversallyTrivialPushforward.hasTrivialPushforward {f : X ⟶ S}
    (hf : HasUniversallyTrivialPushforward f) : HasTrivialPushforward f :=
  MorphismProperty.universally_le _ f hf

/-! ### Morphisms to an affine target factor through the base

The `Γ ⊣ Spec` half of the rigidity argument.  Nothing here needs properness, flatness or
any hypothesis on the fibres: `IsIso (p.app ⊤)` alone already makes
`(p ≫ ·) : (S ⟶ Z) → (X ⟶ Z)` a bijection for every affine `Z`, because both sides are
`Hom` out of a global-sections ring and `p.app ⊤` is the comparison between them. -/

/-- **`(p ≫ ·)` is injective on morphisms into an affine scheme**, as soon as
`p.app ⊤ : Γ(S, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism.

A morphism into an affine scheme is determined by its action on global sections
(`ext_of_isAffine`), and `(p ≫ c).app ⊤ = c.app ⊤ ≫ p.app ⊤`, so the claim is exactly that
`p.app ⊤` is a monomorphism. -/
theorem eq_of_comp_eq_of_isAffine {X S Z : Scheme.{u}} {p : X ⟶ S} [IsIso p.appTop]
    [IsAffine Z] {c₁ c₂ : S ⟶ Z} (h : p ≫ c₁ = p ≫ c₂) : c₁ = c₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  exact (cancel_mono p.appTop).mp h'

/-- **AN `S`-MORPHISM FROM `X` TO AN AFFINE SCHEME FACTORS UNIQUELY THROUGH `S`** — the
corollary of `p_*𝒪_X = 𝒪_S` that the rigidity lemma runs on.

The factorization is written down explicitly rather than extracted from an abstract
adjunction argument: the ring map is `φ = m.app ⊤ ≫ (p.app ⊤)⁻¹ : Γ(Z, ⊤) ⟶ Γ(S, ⊤)`, and
the morphism is `S ⟶ Spec Γ(S, ⊤) ⟶ Spec Γ(Z, ⊤) ≅ Z`.  The verification is then
`Scheme.toSpecΓ_naturality` twice, once in each direction, with `Spec.map_comp` in between.

Only `HasTrivialPushforward` at the single open `⊤` is used.  Note that the corresponding
statement for a target merely *affine over `S`* is `exists_comp_snd_eq_of_isAffine_pullback`
below, which is obtained from this one by a base change rather than by a relative `Spec`
(`Mathlib` has no relative `Spec` at this pin). -/
theorem HasTrivialPushforward.existsUnique_comp_eq {X S Z : Scheme.{u}} {p : X ⟶ S}
    (hp : HasTrivialPushforward p) [IsAffine Z] (m : X ⟶ Z) :
    ∃! c : S ⟶ Z, p ≫ c = m := by
  haveI : IsIso p.appTop := hp ⊤
  have key : p ≫ (S.toSpecΓ ≫ Spec.map (m.appTop ≫ inv p.appTop) ≫ Z.isoSpec.inv) = m := by
    rw [← Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  exact ⟨_, key, fun c hc => eq_of_comp_eq_of_isAffine (p := p) (by rw [hc, key])⟩

/-! ### Reduction to an affine base

`IsIso (f.app U)` is a statement about the ⊤-component of a map of **sheaves** on `S`, namely
`f.c : 𝒪_S ⟶ f_*𝒪_X`.  So it is local on `S`, and the reduction of the theorem below to the
case of an affine base is pure sheaf theory, with no geometry in it at all. -/

/-- **`f.appTop` IS AN ISOMORPHISM AS SOON AS `f.app U` IS FOR EVERY AFFINE OPEN `U ⊆ S`**
(PROVEN).

`f.app U` is the component at `U` of `f.c : 𝒪_S ⟶ f_*𝒪_X`, a morphism of sheaves of rings on
`S` (the target is a sheaf by `TopCat.Sheaf.pushforward_sheaf_of_sheaf`).  The affine opens are
a basis of `S` (`Scheme.isBasis_affineOpens`), so componentwise bijectivity on them gives
bijectivity on every stalk — injectivity by `stalkFunctor_map_injective_of_isBasis`, surjectivity
because every germ is represented on a basis open (`exists_mem_germ_eq_of_isBasis`) — and a
morphism of sheaves that is a stalkwise isomorphism is an isomorphism on every open, in
particular on `⊤` (`app_isIso_of_stalkFunctor_map_iso`).

This is the step that lets the cohomological content below be stated over an **affine** base,
where `Γ(S, ⊤)` is an honest ring and `Γ(X, ⊤)` an honest module over it. -/
theorem isIso_appTop_of_isIso_app_affineOpens (f : X ⟶ S)
    (h : ∀ U ∈ S.affineOpens, IsIso (f.app U)) : IsIso f.appTop := by
  let G : TopCat.Sheaf CommRingCat S :=
    ⟨f.base _* X.presheaf, TopCat.Sheaf.pushforward_sheaf_of_sheaf f.base X.sheaf.2⟩
  let α : S.sheaf ⟶ G := ⟨f.c⟩
  have hb : TopologicalSpace.Opens.IsBasis S.affineOpens := S.isBasis_affineOpens
  have hbij : ∀ x : S, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.1) := by
    intro x
    constructor
    · refine TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hb ?_ x
      intro U hU
      haveI := h U hU
      exact (ConcreteCategory.bijective_of_isIso (f.app U)).1
    · intro t
      obtain ⟨U, hxU, hU, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hb G.1 x t
      haveI := h U hU
      obtain ⟨s', rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.app U)).2 s
      exact ⟨S.presheaf.germ U x hxU s',
        TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α.1 s'⟩
  haveI : ∀ x : S, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.1) :=
    fun x => (ConcreteCategory.isIso_iff_bijective _).mpr (hbij x)
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso α ⊤

/-! ### The two halves: the fibrewise computation, and cohomology and base change

The classical proof of `f_*𝒪_X = 𝒪_S` has exactly two moving parts, and they are independent
of one another:

* **over a field** — `H⁰(Z, 𝒪_Z) = K` for `Z` proper, geometrically connected and
  geometrically reduced over `K` (`isIso_appTop_of_isProper_over_field`).  No flatness and no
  cohomology in positive degree; this half is **DONE** (2026-07-28), and its only base change
  is the harmless one to `K̄`, which `Mathlib`'s flat-base-change API for `Γ` supplies;
* **cohomology and base change** — for `f` proper, flat and of finite presentation over an
  affine base, `𝒪_S ⟶ f_*𝒪_X` is an isomorphism as soon as it is one on every fibre
  (`isIso_appTop_of_isIso_appTop_fiber`, now **PROVEN** over three narrower leaves).  This
  half never sees geometric connectedness or reducedness: they enter *only* through the
  fibrewise hypothesis.

`isIso_appTop_of_isProper_of_flat_of_isAffine` is PROVEN by feeding the first into the second,
which is why the two are cut apart here rather than proved together. -/

/-! #### The fibrewise half: `H⁰(Z, 𝒪_Z) = K`

The route actually taken here is **shorter than the classical five-step one** recorded in earlier
versions of this docstring, and in particular it never needs `Γ(Z, ⊤)` to be *finite* over `K`,
nor `Z` to be irreducible.  It is:

1. `K ⟶ A := Γ(Z, ⊤)` is **integral** — `isIntegral_appTop_of_universallyClosed`, free from
   `Mathlib`, and the only place properness is used.
2. `A` is **reduced** (`Z` is), and has **no nontrivial idempotents** (`Z` is connected):
   an idempotent `e` splits `Z` into the two disjoint opens `Z.basicOpen e` and
   `Z.basicOpen (1 - e)`, which cover because an idempotent of a *local* ring is `0` or `1`
   (`IsLocalRing.isUnit_or_isUnit_one_sub_self`).
3. Hence `A` is a **field**: a reduced ring is *von Neumann regular* at every element integral
   over a field (`exists_eq_sq_mul_of_isIntegral`), so `a = a²t`, `at` is idempotent, and
   `at = 1` is the inverse.  This replaces the classical "`K[a]` is a finite reduced algebra,
   hence a product of fields" and needs no finiteness.
4. Over an **algebraically closed** field this already finishes: a field integral over an
   algebraically closed field *is* that field
   (`IsAlgClosed.ringHom_bijective_of_isIntegral`).  That is
   `isIso_appTop_of_universallyClosed_of_isAlgClosed`.
5. The general case is reduced to (4) by base-changing to `K̄`, which is where the geometric
   hypotheses are consumed and where the one remaining leaf sits.
-/

open Polynomial in
/-- The inductive step of `exists_eq_sq_mul_of_isIntegral`: if `a^k * (a * d + c) = 0` with `c`
a nonzero scalar, then `a = a² t`.

Reducedness turns `a ^ k * b = 0` into `a * b = 0` — because `(a * b) ^ (k + 1)
= a * (a ^ k * b) * b ^ k = 0` — and `a * (a * d + c) = 0` is `a² d + a c = 0`, which is
`a = a² * (-(d / c))` after dividing by the unit `c`. -/
theorem exists_eq_sq_mul_of_pow_mul_add_eq_zero {K A : Type*} [Field K] [CommRing A]
    [_root_.IsReduced A] [Algebra K A] {a d : A} {c : K} (hc : c ≠ 0) {k : ℕ}
    (h : a ^ k * (a * d + algebraMap K A c) = 0) : ∃ t : A, a = a ^ 2 * t := by
  set b : A := a * d + algebraMap K A c with hb
  have hnil : IsNilpotent (a * b) := by
    refine ⟨k + 1, ?_⟩
    have hpow : (a * b) ^ (k + 1) = a ^ k * b * (a * b ^ k) := by
      rw [mul_pow, pow_succ, pow_succ]; ring
    rw [h, zero_mul] at hpow
    exact hpow
  have hab : a * b = 0 := hnil.eq_zero
  refine ⟨-(d * algebraMap K A c⁻¹), ?_⟩
  have hcinv : algebraMap K A c * algebraMap K A c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hexp : a ^ 2 * d + a * algebraMap K A c = 0 := by rw [← hab, hb]; ring
  have h2 : a * (algebraMap K A c * algebraMap K A c⁻¹) = a ^ 2 * -(d * algebraMap K A c⁻¹) := by
    have hmul := congrArg (· * algebraMap K A c⁻¹) hexp
    simp only [zero_mul, add_mul] at hmul
    linear_combination hmul
  rwa [hcinv, mul_one] at h2

open Polynomial in
/-- **A REDUCED RING IS VON NEUMANN REGULAR AT EVERY ELEMENT INTEGRAL OVER A FIELD** (PROVEN):
if `A` is reduced and `a : A` is integral over a field `K`, then `a = a² t` for some `t : A`.

This is the elementary substitute for "a finite reduced algebra over a field is a product of
fields", and it is what makes `isField_of_isIntegral_of_forall_isIdempotentElem` need no
finiteness hypothesis at all.

**Proof.**  Induct on `p.natDegree` for a monic `p` killing `a`, in the strengthened form
"`a ^ k * p(a) = 0` for some `k`".  If `p.coeff 0 ≠ 0`, write `p = X * p.divX + C (p.coeff 0)`
and apply `exists_eq_sq_mul_of_pow_mul_add_eq_zero`.  If `p.coeff 0 = 0`, then `p = X * p.divX`,
so `a ^ (k + 1) * p.divX(a) = 0` and `p.divX` has smaller degree.  The two cases are exhaustive
because a nonzero polynomial of degree `0` is a nonzero constant. -/
theorem exists_eq_sq_mul_of_isIntegral {K A : Type*} [Field K] [CommRing A] [_root_.IsReduced A]
    [Algebra K A] {a : A} (ha : _root_.IsIntegral K a) : ∃ t : A, a = a ^ 2 * t := by
  suffices H : ∀ n : ℕ, ∀ p : K[X], p.natDegree ≤ n → p ≠ 0 → ∀ k : ℕ,
      a ^ k * aeval a p = 0 → ∃ t : A, a = a ^ 2 * t by
    obtain ⟨p, hmonic, hp⟩ := ha
    refine H p.natDegree p le_rfl hmonic.ne_zero 0 ?_
    simpa [aeval_def] using hp
  intro n
  induction n with
  | zero =>
    intro p hpn hp k hk
    have hpc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hpn)
    have hc : p.coeff 0 ≠ 0 := fun h => hp (by rw [hpc, h, map_zero])
    refine exists_eq_sq_mul_of_pow_mul_add_eq_zero (a := a) (d := 0) hc (k := k) ?_
    rw [mul_zero, zero_add]
    rw [hpc] at hk
    simpa using hk
  | succ n ih =>
    intro p hpn hp k hk
    by_cases hc : p.coeff 0 = 0
    · have hX : X * p.divX = p := by
        have hd := Polynomial.X_mul_divX_add p
        rwa [hc, map_zero, add_zero] at hd
      have hdiv : p.divX ≠ 0 := fun h => hp (by rw [← hX, h, mul_zero])
      have hdeg : p.divX.natDegree ≤ n := by
        have hnd : p.divX.natDegree = p.natDegree - 1 :=
          Polynomial.natDegree_divX_eq_natDegree_tsub_one
        omega
      refine ih p.divX hdeg hdiv (k + 1) ?_
      have key : a ^ (k + 1) * aeval a p.divX = a ^ k * aeval a p := by
        conv_rhs => rw [← hX]
        rw [map_mul, aeval_X]; ring
      rw [key]; exact hk
    · refine exists_eq_sq_mul_of_pow_mul_add_eq_zero (a := a) (d := aeval a p.divX) hc (k := k) ?_
      have hsplit : aeval a p = a * aeval a p.divX + algebraMap K A (p.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add p]
        rw [map_add, map_mul, aeval_X, aeval_C]
      rwa [← hsplit]

/-- **A REDUCED RING INTEGRAL OVER A FIELD WITH NO NONTRIVIAL IDEMPOTENTS IS A FIELD** (PROVEN).

Note what is *absent*: no finiteness, no irreducibility, no Noetherian hypothesis.  Von Neumann
regularity (`exists_eq_sq_mul_of_isIntegral`) gives `a = a² t`; then `a * t` is idempotent, so it
is `0` or `1`; it cannot be `0` (that forces `a = a * (a * t) = 0`), so `t` inverts `a`. -/
theorem isField_of_isIntegral_of_forall_isIdempotentElem {K A : Type*} [Field K] [CommRing A]
    [Nontrivial A] [_root_.IsReduced A] [Algebra K A] [Algebra.IsIntegral K A]
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField A := by
  refine ⟨exists_pair_ne A, mul_comm, ?_⟩
  intro a ha
  obtain ⟨t, ht⟩ := exists_eq_sq_mul_of_isIntegral (K := K) (Algebra.IsIntegral.isIntegral a)
  have he : IsIdempotentElem (a * t) := by
    unfold IsIdempotentElem
    calc a * t * (a * t) = a ^ 2 * t * t := by ring
      _ = a * t := by rw [← ht]
  rcases hidem _ he with h | h
  · exact absurd (by rw [ht, show a ^ 2 * t = a * (a * t) by ring, h, mul_zero]) ha
  · exact ⟨t, h⟩

/-- **`Γ(Z, ⊤)` HAS NO NONTRIVIAL IDEMPOTENTS FOR A CONNECTED REDUCED SCHEME** (PROVEN).

An idempotent `e` gives two opens `Z.basicOpen e` and `Z.basicOpen (1 - e)` which are *disjoint*
(`e * (1 - e) = 0`, and `Z.basicOpen 0 = ⊥`) and *cover* `Z` (in the local ring at any point,
`IsLocalRing.isUnit_or_isUnit_one_sub_self` makes `e` or `1 - e` a unit).  So `Z.basicOpen e` is
clopen; connectedness makes it `⊥` or `⊤`, and reducedness turns that into `e = 0` or `e = 1`
via `basicOpen_eq_bot_iff`.

Reducedness is genuinely needed: on `Z = Spec (K[ε]/ε²)` the element `ε` has `basicOpen ε = ⊥`
without being zero — though of course `ε` is not idempotent, the *implication*
`basicOpen s = ⊥ → s = 0` is what fails. -/
theorem isIdempotentElem_appTop_eq_zero_or_one {Z : Scheme.{u}} [IsReduced Z]
    [ConnectedSpace Z] {e : Γ(Z, ⊤)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have hdisj : Z.basicOpen e ⊓ Z.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, hmul, Scheme.basicOpen_zero]
  have hcover : Z.basicOpen e ⊔ Z.basicOpen (1 - e) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
        ((Z.presheaf.germ ⊤ x trivial) e) with h | h
    · exact Or.inl ((Z.mem_basicOpen_top e x).mpr h)
    · exact Or.inr ((Z.mem_basicOpen_top (1 - e) x).mpr (by simpa using h))
  have hclopen : IsClopen (Z.basicOpen e : Set Z) := by
    refine ⟨?_, (Z.basicOpen e).isOpen⟩
    have hcompl : (Z.basicOpen e : Set Z)ᶜ = (Z.basicOpen (1 - e) : Set Z) := by
      refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx hx' => ?_)
      · have hx' : x ∈ (⊤ : Z.Opens) := trivial
        rw [← hcover] at hx'
        exact hx'.resolve_left hx
      · have hmem : x ∈ Z.basicOpen e ⊓ Z.basicOpen (1 - e) := ⟨hx', hx⟩
        rw [hdisj] at hmem
        exact hmem
    rw [← isOpen_compl_iff, hcompl]
    exact (Z.basicOpen (1 - e)).isOpen
  rcases _root_.isClopen_iff.mp hclopen with h | h
  · exact Or.inl ((basicOpen_eq_bot_iff e).mp (by ext x; simp [h]))
  · refine Or.inr ?_
    have h1 : Z.basicOpen (1 - e) = ⊥ := by
      have htop : Z.basicOpen e = ⊤ := by ext x; simp [h]
      rw [htop, top_inf_eq] at hdisj
      exact hdisj
    exact (sub_eq_zero.mp ((basicOpen_eq_bot_iff (1 - e)).mp h1)).symm

/-- **`Γ(Z, ⊤)` IS A FIELD FOR A CONNECTED REDUCED SCHEME UNIVERSALLY CLOSED OVER A FIELD**
(PROVEN) — steps 1–3 of the route above, and the sharpening of `Mathlib`'s
`isField_of_universallyClosed`, which assumes `[IsIntegral Z]`.

Irreducibility really is dropped, not hidden: two lines meeting in a point are connected and
reduced but not irreducible, and they do have `H⁰ = k`. -/
theorem isField_appTop_of_universallyClosed {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [UniversallyClosed g] [IsReduced Z] [ConnectedSpace Z] :
    IsField Γ(Z, ⊤) := by
  let F : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed g
  algebraize [F.hom]
  haveI : Nonempty ↥(⊤ : Z.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  haveI : Nontrivial Γ(Z, ⊤) := LocallyRingedSpace.component_nontrivial Z.toLocallyRingedSpace ⊤
  exact isField_of_isIntegral_of_forall_isIdempotentElem (K := K)
    (fun e he => isIdempotentElem_appTop_eq_zero_or_one he)

/-- **`H⁰(Z, 𝒪_Z) = K` OVER AN ALGEBRAICALLY CLOSED FIELD** (PROVEN) — step 4.

`Γ(Z, ⊤)` is a field by `isField_appTop_of_universallyClosed`, hence a domain, and it is integral
over `K`; `IsAlgClosed.ringHom_bijective_of_isIntegral` then says the structure map is bijective.

No geometric connectedness or geometric reducedness appears, because over an algebraically closed
field ordinary connectedness and ordinary reducedness *are* the geometric notions. -/
theorem isIso_appTop_of_universallyClosed_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [UniversallyClosed g] [IsReduced Z]
    [ConnectedSpace Z] : IsIso g.appTop := by
  let F : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed g
  letI : Field ↥Γ(Z, ⊤) := (isField_appTop_of_universallyClosed g).toField
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hF)
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ F = g.appTop := by simp [F]
  rw [← hcomp]
  infer_instance

/-! #### Descent from `K̄` to `K`: flat base change for `H⁰`

Contrary to what an earlier version of this file's docstring asserted, `Mathlib` **does** carry
the base-change machinery for global sections, in
`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`: for a cartesian square

```
Y --g--→ X
|        |
iY       iX
↓        ↓
T --f--→ S
```

`AlgebraicGeometry.pushoutSection` is the canonical map
`Γ(X, Uₓ) ⊗_{Γ(S, Uₛ)} Γ(T, Uₜ) ⟶ Γ(Y, Uy)`, and
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` makes it an isomorphism when `Uₛ`, `Uₜ`
are affine, `Uₓ` is quasi-compact and quasi-separated, and `f` is flat.  Instantiated at
`S = Spec K`, `T = Spec L`, `X = Z` with all opens `⊤`, that is exactly `Γ(Z_L, ⊤) =
Γ(Z, ⊤) ⊗_K L`, and the descent is then a one-line dimension count.  What was absent from
`Mathlib` is higher direct images, not this.
-/

open TensorProduct in
/-- **A `K`-ALGEBRA WHOSE BASE CHANGE TO `L` IS `L` IS `K`** (PROVEN) — the dimension count that
turns flat base change for `H⁰` into the descent.

If `L ⟶ L ⊗_K A` is bijective then `L ⊗_K A` has `L`-rank one, so `A` has `K`-rank one by
`Module.rank_baseChange`, and a unital `K`-algebra of rank one is `K`.  Note `A` is not assumed
nontrivial: that follows, because rank one is not rank zero. -/
theorem bijective_algebraMap_of_bijective_includeLeft {R A L : Type u} [Field R] [CommRing A]
    [Field L] [Algebra R A] [Algebra R L]
    (hbij : Function.Bijective (algebraMap L (L ⊗[R] A))) :
    Function.Bijective (algebraMap R A) := by
  have h1 : Module.rank L (L ⊗[R] A) = 1 := by
    have e : L ≃ₗ[L] (L ⊗[R] A) :=
      (AlgEquiv.ofBijective (Algebra.ofId L (L ⊗[R] A)) hbij).toLinearEquiv
    rw [← e.rank_eq, CommSemiring.rank_self]
  have h2 : Module.rank R A = 1 := by
    have hbc := Module.rank_baseChange (R := L) (S := R) (M' := A)
    rw [h1] at hbc
    simpa using hbc.symm
  haveI : Nontrivial A := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rw [rank_subsingleton'] at h2
    exact zero_ne_one h2
  refine ⟨(algebraMap R A).injective, ?_⟩
  intro w
  have hfr : Module.finrank R A = 1 := Module.rank_eq_one_iff_finrank_eq_one.mp h2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : A) one_ne_zero).mp hfr w
  exact ⟨c, by simpa [Algebra.smul_def] using hc⟩

open TensorProduct in
/-- **FAITHFULLY FLAT DESCENT OF ISOMORPHISMS ALONG A FIELD EXTENSION, IN PUSHOUT FORM** (PROVEN).

In a pushout square of commutative rings whose top-left corner `R` and lower-left corner `L` are
fields, the right-hand leg `δ : L ⟶ Y` being an isomorphism forces the left-hand leg
`α : R ⟶ A` to be one.

The proof does not invoke faithful flatness abstractly: the pushout is identified with
`L ⊗_R A` by `CommRingCat.isPushout_tensorProduct` (two pushouts over the same span are uniquely
isomorphic, and `IsPushout.inl_isoPushout_hom` says the identification carries `δ` to
`includeLeft`), and then `bijective_algebraMap_of_bijective_includeLeft` counts dimensions. -/
theorem isIso_of_isPushout_of_isField {R A L Y : CommRingCat.{u}} (hR : IsField R) (hL : IsField L)
    {α : R ⟶ A} {β : R ⟶ L} {γ : A ⟶ Y} {δ : L ⟶ Y}
    (hpo : IsPushout α β γ δ) [IsIso δ] : IsIso α := by
  letI : Field ↥R := hR.toField
  letI : Field ↥L := hL.toField
  algebraize [α.hom, β.hom]
  have hT : IsPushout β α
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A)))
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ↥R) (A := ↥L) (B := ↥A)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct ↥R ↥L ↥A
  let e : CommRingCat.of (↥L ⊗[↥R] ↥A) ≅ Y := hT.isoPushout ≪≫ hpo.flip.isoPushout.symm
  have hinl : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A)) = δ ≫ e.inv := by
    have h1 := hT.inl_isoPushout_hom
    have h2 := hpo.flip.inl_isoPushout_hom
    simp only [e, Iso.trans_inv, Iso.symm_inv]
    rw [← Category.assoc, h2, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI hiso : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A))) := by
    rw [hinl]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective α).mpr
    (bijective_algebraMap_of_bijective_includeLeft
      ((ConcreteCategory.isIso_iff_bijective _).mp hiso))

/-- `f.appLE ⊤ ⊤` differs from `f.appTop` only by the restriction along `⊤ = f ⁻¹ᵁ ⊤`, which is
an isomorphism because `Opens` is a poset. -/
theorem isIso_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    IsIso (f.appLE ⊤ ⊤ e) ↔ IsIso f.appTop := by
  haveI : IsIso (homOfLE e) := ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rw [Scheme.Hom.appLE]
  exact isIso_comp_right_iff _ _

/-- **`Γ` COMMUTES WITH BASE FIELD EXTENSION, IN THE FORM THE DESCENT NEEDS** (PROVEN,
2026-07-28): if `Γ(Spec L, ⊤) ⟶ Γ(Z ×_{Spec K} Spec L, ⊤)` is an isomorphism, so is
`Γ(Spec K, ⊤) ⟶ Γ(Z, ⊤)`.

**The content.**  For `Z` quasi-compact and quasi-separated over a field `K` and any field
extension `L/K`, the canonical map `Γ(Z, ⊤) ⊗_K L ⟶ Γ(Z ×_{Spec K} Spec L, ⊤)` is bijective —
flat base change for `H⁰`, which is the *equalizer* of a finite Čech diagram of affines together
with the exactness of `- ⊗_K L`, not the full cohomology-and-base-change theorem.  That is
supplied by `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`; `Spec.map φ` is flat
because `K` is a field, and `Z` is quasi-compact and quasi-separated because `g` is and the base
is affine.  `isIso_pushoutSection_iff` turns it into an `IsPushout` square of rings, and
`isIso_of_isPushout_of_isField` descends the isomorphism.

**FAITHFULNESS.**  Both fields are load-bearing: `hK` is what makes `L` flat over `K` (so the
base change computes `Γ` at all), and `hL` is what makes "rank one over `L`" meaningful.  The
empty scheme is not a counterexample — there `Γ(Z, ⊤) = 0 = Γ(Z_L, ⊤)` and the hypothesis fails,
since a field never maps isomorphically to the zero ring. -/
theorem isIso_appTop_of_isIso_appTop_baseChange {K L : CommRingCat.{u}}
    (hK : IsField K) (hL : IsField L) (φ : K ⟶ L) {Z : Scheme.{u}} (g : Z ⟶ Spec K)
    [QuasiCompact g] [QuasiSeparated g]
    (h : IsIso (pullback.snd g (Spec.map φ)).appTop) : IsIso g.appTop := by
  letI : Field ↥K := hK.toField
  letI : Field ↥L := hL.toField
  haveI : Flat (Spec.map φ) := by
    rw [Flat.SpecMap_iff]
    letI := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat ↥K ↥L)
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace g).mp inferInstance
  haveI : QuasiSeparatedSpace Z := (quasiSeparated_iff_quasiSeparatedSpace g).mp inferInstance
  have H : IsPullback (pullback.fst g (Spec.map φ)) (pullback.snd g (Spec.map φ)) g
      (Spec.map φ) := IsPullback.of_hasPullback _ _
  have hpo := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H)
    (hUST := (le_top : (⊤ : (Spec L).Opens) ≤ _)) (hUSX := (le_top : (⊤ : Z.Opens) ≤ _))
    (hUY := (by simp : (⊤ : (pullback g (Spec.map φ)).Opens) = _))
    (isAffineOpen_top _) (isAffineOpen_top _) (by simpa using isCompact_univ (X := Z))
    (by simpa using isQuasiSeparated_univ (α := Z))
  rw [isIso_pushoutSection_iff] at hpo
  haveI : IsIso ((pullback.snd g (Spec.map φ)).appLE ⊤ ⊤ (by simp)) :=
    (isIso_appLE_top_iff _ _).mpr h
  refine (isIso_appLE_top_iff g (by simp)).mp ?_
  exact isIso_of_isPushout_of_isField
    ((Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv.isField hK)
    ((Scheme.ΓSpecIso L).commRingCatIsoToRingEquiv.toMulEquiv.isField hL) hpo

/-- **`H⁰(Z, 𝒪_Z) = K` FOR A PROPER, GEOMETRICALLY CONNECTED, GEOMETRICALLY REDUCED SCHEME
OVER A FIELD** — the fibrewise half of the pushforward theorem, **PROVEN** (2026-07-28), with no
leaf left under it.

**FALSITY AUDIT AND REPAIR (2026-07-28) — the hypothesis used to be `[Field K]` and that made
the statement FALSE.**  With `K : CommRingCat`, the binder `[Field K]` elaborates as
`Field ↥K`: a field structure on the *carrier type* of `K`, whose ring operations are a fresh
structure field and are **provably unrelated** to `K`'s own ring structure — the compiler reports
the two `CommSemiring ↥K` instance paths (`CommRing.toCommSemiring` from `CommRingCat` versus
`Field.toSemifield.toCommSemiring`) as not even definitionally equal.  So `[Field K]` did not say
"`K` is a field"; it said "the carrier of `K` happens to be in bijection with some field", which
is a condition on a *type*, not on a ring.

Explicit counterexample to the old statement: `K = CommRingCat.of (ZMod 4)`, `Z = Spec (ZMod 2)`,
`g` the closed immersion induced by `ZMod 4 ↠ ZMod 2`.  Then `g` is finite, hence proper; every
field-valued point of `Spec (ZMod 4)` kills the nilpotent `2`, so every base change of `g` to a
field is an isomorphism, making `g` geometrically connected and geometrically reduced; and
`g.appTop : ZMod 4 ⟶ ZMod 2` is not an isomorphism.  The old hypothesis `[Field ↥K]` is
satisfied because `↥K` is a four-element type, and a four-element type carries a field structure
(`𝔽₄`).

The repair is the honest hypothesis `hK : IsField K`, which is stated with respect to `K`'s own
semiring structure and therefore cannot be satisfied spuriously.  The consumer supplies it with
`Field.toIsField`, so nothing downstream got harder.

**The proof.**  Base-change to `K̄`: the pullback is proper, reduced and connected (this is
exactly what `GeometricallyReduced` and `GeometricallyConnected` say), so
`isIso_appTop_of_universallyClosed_of_isAlgClosed` computes its global sections, and
`isIso_appTop_of_isIso_appTop_baseChange` descends that to `K`.

**FAITHFULNESS.**  All three hypotheses are load-bearing.  Without geometric connectedness the
statement fails for `Z = Spec (K × K)`; without geometric reducedness it fails for
`Z = Spec (K[ε]/ε²)`; and *geometric* connectedness cannot be weakened to connectedness — for
`K = ℝ` and `Z = Spec ℂ`, `Z` is connected, reduced and proper over `ℝ`, and
`H⁰(Z, 𝒪) = ℂ ≠ ℝ`.  Likewise geometric reducedness cannot be weakened to reducedness, by the
usual inseparable example `Z = Spec 𝔽_p(t^{1/p})` over `K = 𝔽_p(t)`.  Note that the first two
are already invisible to steps 1–4: `Γ` of `Spec (K × K)` is a nontrivial idempotent, and `Γ` of
`Spec (K[ε]/ε²)` is not reduced. -/
theorem isIso_appTop_of_isProper_over_field {K : CommRingCat.{u}} (hK : IsField K)
    {Z : Scheme.{u}} (g : Z ⟶ Spec K) [IsProper g] [GeometricallyConnected g]
    [GeometricallyReduced g] : IsIso g.appTop := by
  letI : Field ↥K := hK.toField
  let φ : K ⟶ CommRingCat.of (AlgebraicClosure ↥K) :=
    CommRingCat.ofHom (algebraMap ↥K (AlgebraicClosure ↥K))
  refine isIso_appTop_of_isIso_appTop_baseChange hK (Field.toIsField _) φ g ?_
  haveI : UniversallyClosed (pullback.snd g (Spec.map φ)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsReduced (pullback g (Spec.map φ)) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  haveI : ConnectedSpace ↥(pullback g (Spec.map φ)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  exact isIso_appTop_of_universallyClosed_of_isAlgClosed (K := AlgebraicClosure ↥K) _

/-! #### The commutative algebra of the base-change argument

Everything in this block is pure commutative algebra about a ring map `φ : R ⟶ A`; no
geometry appears, and it is all **PROVEN**.  It lives here only because this file is its
single consumer — it would sit just as well in a `RingTheory` shim, and can be hoisted
verbatim.  It is stated inside `namespace AlgebraicGeometry` (with undotted names) so that
nothing lands in the root namespace.

What it isolates is exactly the part of the classical proof that is *not* cohomology: given
that `A` is a finite `R`-module, that `A` is `R`-flat, and that `R/𝔪 ⟶ A/𝔪A` is bijective
for every maximal `𝔪`, the map `R ⟶ A` is itself bijective.  The three geometric leaves
below supply those three inputs and nothing else. -/

/-- **NAKAYAMA OVER EVERY MAXIMAL IDEAL** (PROVEN): a finitely generated submodule `N` with
`N ≤ 𝔪 • N` for *every* maximal ideal `𝔪` is zero.

The usual local statement needs `𝔪` inside the Jacobson radical; the global one is got from
it by looking at the annihilator.  If `N ≠ 0` then `Ann N ≠ ⊤`, so `Ann N ≤ 𝔪` for some
maximal `𝔪`; the determinant trick
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) applied at that `𝔪`
produces `r` with `r - 1 ∈ 𝔪` and `r ∈ Ann N ≤ 𝔪`, whence `1 ∈ 𝔪`.  So `Ann N = ⊤` and
`N = 1 • N = 0`. -/
theorem eq_bot_of_fg_of_le_smul_of_forall_isMaximal {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {N : Submodule R M} (hfg : N.FG)
    (h : ∀ m : Ideal R, m.IsMaximal → N ≤ m • N) : N = ⊥ := by
  have hann : N.annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr2⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m N hfg (h m hm)
    have hrann : r ∈ N.annihilator := Submodule.mem_annihilator.mpr hr2
    have hone : (1 : R) ∈ m := by
      have h1 : r ∈ m := hle hrann
      have h2 := Submodule.sub_mem m h1 hr1
      simpa using h2
    exact hm.ne_top (Ideal.eq_top_iff_one m |>.mpr hone)
  refine le_antisymm (fun x hx => ?_) bot_le
  have h1 : (1 : R) ∈ N.annihilator := by rw [hann]; trivial
  have := Submodule.mem_annihilator.mp h1 x hx
  simpa using this

/-- **SURJECTIVITY BY NAKAYAMA** (PROVEN): if `A` is a *finite* `R`-module and every element
of `A` is congruent to an element of `R` modulo `𝔪A`, for every maximal ideal `𝔪`, then
`R ⟶ A` is surjective.

This is `eq_bot_of_fg_of_le_smul_of_forall_isMaximal` applied to `⊤` in the cokernel
`A ⧸ (image of R)`: the hypothesis says exactly that the cokernel is killed by passing to
`A/𝔪A`, i.e. that `⊤ ≤ 𝔪 • ⊤` there.  Only *finiteness* of `A` is used, not finite
presentation. -/
theorem surjective_algebraMap_of_finite_of_forall_isMaximal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a : A,
      ∃ r : R, a - algebraMap R A r ∈ m.map (algebraMap R A)) :
    Function.Surjective (algebraMap R A) := by
  set N : Submodule R A := LinearMap.range (Algebra.linearMap R A) with hNdef
  haveI : Module.Finite R (A ⧸ N) := Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  have hQ : (⊤ : Submodule R (A ⧸ N)) = ⊥ := by
    refine eq_bot_of_fg_of_le_smul_of_forall_isMaximal Module.Finite.fg_top ?_
    intro m hm q _
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨r, hr⟩ := h m hm a
    have hmem : a - algebraMap R A r ∈ m • (⊤ : Submodule R A) := by
      rw [Ideal.smul_top_eq_map]
      exact hr
    have hz : N.mkQ (algebraMap R A r) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨r, rfl⟩
    have heq : N.mkQ a = N.mkQ (a - algebraMap R A r) := by
      rw [map_sub, hz, sub_zero]
    rw [heq]
    have hmap : Submodule.map N.mkQ (m • (⊤ : Submodule R A))
        = m • (⊤ : Submodule R (A ⧸ N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap]
    exact Submodule.mem_map_of_mem hmem
  intro a
  have hmem : N.mkQ a = 0 := by
    have h0 : N.mkQ a ∈ (⊤ : Submodule R (A ⧸ N)) := Submodule.mem_top
    rw [hQ] at h0
    simpa using h0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact ⟨r, hr⟩

/-- **INJECTIVITY FROM FLATNESS, WITHOUT ANY FINITENESS** (PROVEN): if `A` is a *flat*
`R`-algebra, `R ⟶ A` is surjective, and `ker (R ⟶ A)` lies in the Jacobson radical of `R`,
then `R ⟶ A` is injective.

The classical route here goes through `Tor₁(A, R/𝔪) = 0` and needs `ker` finitely generated
(via `Module.FinitePresentation.fg_ker`).  It is **not** needed: the *equational criterion
for flatness* (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, Stacks 00HK) applied to
the one-term relation `k • (1 : A) = 0` gives `aⱼ ∈ R` and `yⱼ ∈ A` with `1 = ∑ aⱼ • yⱼ` and
`k * aⱼ = 0`.  Surjectivity turns `yⱼ` into `algebraMap dⱼ`, so `e := ∑ aⱼ dⱼ` satisfies
`algebraMap e = 1` — i.e. `e - 1 ∈ ker` — and `k * e = 0`.  Since `e - 1` is in the Jacobson
radical, `e` is a *unit*, so `k = 0` outright.  No Nakayama, no finite generation, no `Tor`.

That is why the geometric leaf below asks only for `Module.Finite`, not
`Module.FinitePresentation`. -/
theorem injective_algebraMap_of_flat_of_ker_le_jacobson
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (hsurj : Function.Surjective (algebraMap R A))
    (hker : RingHom.ker (algebraMap R A) ≤ Ideal.jacobson ⊥) :
    Function.Injective (algebraMap R A) := by
  refine (injective_iff_map_eq_zero (algebraMap R A)).mpr ?_
  intro k hk
  have hrel : ∑ _i : Unit, k • (1 : A) = 0 := by
    simp [Algebra.smul_def, hk]
  obtain ⟨n, a, y, hx, ha⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) (ι := Unit)
      (f := fun _ => k) (x := fun _ => (1 : A)) hrel
  choose d hd using hsurj
  set e : R := ∑ j, a () j * d (y j) with he
  have he1 : algebraMap R A e = 1 := by
    rw [he, map_sum]
    have hterm : ∀ j : Fin n, algebraMap R A (a () j * d (y j)) = a () j • y j := by
      intro j
      rw [map_mul, hd, Algebra.smul_def]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← hx ()]
  have hke : k * e = 0 := by
    rw [he, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : k * a () j = 0 := by simpa using ha j
    rw [← mul_assoc, hj, zero_mul]
  have hsub : e - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    refine hker ?_
    simp [RingHom.mem_ker, map_sub, he1]
  obtain ⟨b, hb⟩ := (Ideal.isUnit_of_sub_one_mem_jacobson_bot e hsub).exists_right_inv
  calc k = k * (e * b) := by rw [hb, mul_one]
    _ = (k * e) * b := by ring
    _ = 0 := by rw [hke, zero_mul]

/-- **THE ASSEMBLED COMMUTATIVE-ALGEBRA STATEMENT** (PROVEN): a finite flat `R`-algebra `A`
whose reduction `R/𝔪 ⟶ A/𝔪A` is bijective at every maximal ideal `𝔪` has `R ⟶ A` bijective.

Surjectivity is `surjective_algebraMap_of_finite_of_forall_isMaximal` (Nakayama on the
cokernel); injectivity is `injective_algebraMap_of_flat_of_ker_le_jacobson`, whose Jacobson
hypothesis is exactly the *injective* half of `R/𝔪 ⟶ A/𝔪A` read at every maximal `𝔪`
(`ker ≤ 𝔪` for all `𝔪`, and `Ideal.jacobson ⊥` is the infimum of the maximal ideals).

This is the whole of the base-change theorem that is not cohomology. -/
theorem bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (h : ∀ m : Ideal R, m.IsMaximal →
      Function.Bijective (Ideal.quotientMap (I := m) (m.map (algebraMap R A))
        (algebraMap R A) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap R A) := by
  have hsurj : Function.Surjective (algebraMap R A) := by
    refine surjective_algebraMap_of_finite_of_forall_isMaximal ?_
    intro m hm a
    obtain ⟨x, hx⟩ := (h m hm).2 (Ideal.Quotient.mk _ a)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨r, ?_⟩
    rw [Ideal.quotientMap_mk] at hx
    exact (Ideal.Quotient.eq.mp hx.symm)
  refine ⟨?_, hsurj⟩
  refine injective_algebraMap_of_flat_of_ker_le_jacobson hsurj ?_
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro J ⟨-, hJ⟩
  intro k hk
  have h0 : Ideal.quotientMap (I := J) (J.map (algebraMap R A)) (algebraMap R A)
      Ideal.le_comap_map (Ideal.Quotient.mk J k) = 0 := by
    rw [Ideal.quotientMap_mk]
    have hk0 : algebraMap R A k = 0 := hk
    rw [hk0, map_zero]
  have hinj : (Ideal.Quotient.mk J) k = 0 := (h J hJ).1 (by simpa using h0)
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hinj

/-! #### The geometric inputs

`R := Γ(S, ⊤)` and `A := Γ(X, ⊤)`, with `A` an `R`-algebra through `φ := f.appTop`.  These
supply the hypotheses of `bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap`,
and together they are the *entire* remaining content of degree-zero cohomology and base
change.

The classical shape of the argument is:

* the comparison map `φ⁰(s) : (f_*𝒪_X) ⊗ κ(s) ⟶ H⁰(X_s, 𝒪)` is **surjective** for every `s`,
  because the hypothesis `h s` factors it: `κ(s) ⟶ (f_*𝒪_X) ⊗ κ(s) ⟶ H⁰(X_s, 𝒪)` is the
  structure map, which `h s` says is an isomorphism;
* III.12.11(a) then makes `φ⁰(s)` an ISOMORPHISM — over an affine base this reads
  `A/𝔪A ≅ H⁰(X_s, 𝒪) = κ(s) = R/𝔪`, which is
  `surjective_quotientMap_appTop_of_isIso_appTop_fiber`, the ONE leaf left in this block;
* III.12.11(b) would then make `f_*𝒪_X` locally free.  **It is not needed** — see
  `module_flat_appTop_of_isIso_appTop_fiber`, which gets `Module.Flat R A` from lying over
  plus faithfully flat descent on stalks instead.

Note that the reducedness of `S` demanded by Grauert (Hartshorne III.12.9, Mumford *AV* §5
Corollary 2) is *not* needed on this route: III.12.11 has no such hypothesis, which matters
here because the bases this development feeds in are arbitrary.  Nothing below has been
"simplified to Grauert". -/

/-! #### The maximal-ideal ↔ point dictionary (PROVEN, 2026-07-30)

Both remaining leaves of this file are stated at a **maximal ideal `𝔪 ⊂ R = Γ(S, ⊤)`**, while
the hypothesis `h` is indexed by **points `s : S`**.  The two are matched by the pair of
theorems below, and with them in hand each leaf reduces to a statement with no ideal in it at
all: *a global section that RESTRICTS TO ZERO ON THE FIBRE `X_s` lies in `𝔪 · (…)`*.

The docstring of `rank_quotient_appTop_le_one_of_isIso_appTop_fiber`'s block introduction said
this bookkeeping "belongs here, not in the assembly"; it is now discharged once and consumed
twice, by `adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` below and by
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` far below.

The content is entirely in the pin: `Ideal.algebraMap_residueField_surjective` and
`Ideal.ker_algebraMap_residueField` for the ALGEBRA of it — `R ⟶ κ(𝔪)` is surjective with
kernel `𝔪` exactly because `𝔪` is maximal, `R_𝔪/𝔪R_𝔪 = R/𝔪` — and
`Scheme.Spec.algebraMap_residueFieldIso_inv` plus `Scheme.Γevaluation_naturality` to move it
across `S ≅ Spec Γ(S, ⊤)`.  **Maximality is load-bearing and cannot be relaxed to primality**:
at a non-maximal prime `𝔭` the map `R ⟶ κ(𝔭)` lands in a fraction field and is not surjective,
so no `r : R` need restrict to a given value on the fibre. -/

/-- **THE POINT CUT OUT BY A MAXIMAL IDEAL** (PROVEN, 2026-07-30): for `S` affine and
`𝔪 ⊂ Γ(S, ⊤)` maximal there is a point `s : S` at which evaluation of global sections is
SURJECTIVE with kernel exactly `𝔪`.

`s` is `S.isoSpec.inv ⟨𝔪, _⟩`.  On `Spec R` the statement is
`Scheme.Spec.algebraMap_residueFieldIso_inv`, which identifies
`(Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ⟨𝔪, _⟩` with
`algebraMap R 𝔪.ResidueField` up to an isomorphism of residue fields; surjectivity and the
kernel are then `Ideal.algebraMap_residueField_surjective` and
`Ideal.ker_algebraMap_residueField`.  `Scheme.Γevaluation_naturality` applied to `S.isoSpec.hom`
transports both to `S`, the transport being harmless because `Hom.residueFieldMap` of an
isomorphism is an isomorphism. -/
theorem exists_point_ker_Γevaluation_eq_of_isMaximal (S : Scheme.{u}) [IsAffine S]
    (m : Ideal ↥Γ(S, ⊤)) (hm : m.IsMaximal) :
    ∃ s : S, RingHom.ker (S.Γevaluation s).hom = m ∧
      Function.Surjective (S.Γevaluation s).hom := by
  classical
  refine ⟨S.isoSpec.inv.base ⟨m, hm.isPrime⟩, ?_⟩
  set s : S := S.isoSpec.inv.base ⟨m, hm.isPrime⟩ with hsdef
  have hbase : S.isoSpec.hom.base s = (⟨m, hm.isPrime⟩ : ↥(Spec Γ(S, ⊤))) := by
    rw [hsdef, ← Scheme.Hom.comp_apply, S.isoSpec.inv_hom_id]; rfl
  have hs : (S.isoSpec.hom.base s).asIdeal = m := by rw [hbase]
  haveI hpm : (S.isoSpec.hom.base s).asIdeal.IsMaximal := hs ▸ hm
  set p : ↥(Spec Γ(S, ⊤)) := S.isoSpec.hom.base s
  set ψ : Γ(S, ⊤) ⟶ (Spec Γ(S, ⊤)).residueField p :=
    (Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ (Spec Γ(S, ⊤)).Γevaluation p with hψ
  have hkey : CommRingCat.ofHom (algebraMap (↥Γ(S, ⊤)) p.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso Γ(S, ⊤) p).inv = ψ :=
    Scheme.Spec.algebraMap_residueFieldIso_inv Γ(S, ⊤) p
  have hψsurj : Function.Surjective ψ.hom := by
    rw [← hkey, CommRingCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso Γ(S, ⊤) p).inv).2.comp
      (Ideal.algebraMap_residueField_surjective p.asIdeal)
  have hψker : RingHom.ker ψ.hom = m := by
    rw [← hkey, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      ((ConcreteCategory.bijective_of_isIso
        (Scheme.Spec.residueFieldIso Γ(S, ⊤) p).inv).1)]
    rw [show ((CommRingCat.ofHom
        (algebraMap (↥Γ(S, ⊤)) p.asIdeal.ResidueField)).hom) =
      algebraMap (↥Γ(S, ⊤)) p.asIdeal.ResidueField from rfl,
      Ideal.ker_algebraMap_residueField, hs]
  have hnat : ψ ≫ S.isoSpec.hom.residueFieldMap s = S.Γevaluation s := by
    rw [hψ, Category.assoc, Scheme.Γevaluation_naturality S.isoSpec.hom s,
      ← Category.assoc]
    simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
      Category.id_comp]
  constructor
  · rw [← hnat, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _
      ((ConcreteCategory.bijective_of_isIso
        (S.isoSpec.hom.residueFieldMap s)).1), hψker]
  · rw [← hnat, CommRingCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso
      (S.isoSpec.hom.residueFieldMap s)).2.comp hψsurj

/-- **`Γ` OF `Spec κ(s) ⟶ S` IS EVALUATION AT `s`** (PROVEN, 2026-07-30):
`(S.fromSpecResidueField s).appTop = S.Γevaluation s ≫ (ΓSpecIso κ(s)).inv`.

Unfolding `fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x` and applying
`Scheme.fromSpecStalk_appTop` and `Scheme.ΓSpecIso_inv_naturality` leaves exactly
`germ ⊤ s ≫ residue s`, which is `Γevaluation` by definition.  Absent from the pin, which has
`fromSpecStalk_appTop` but no residue-field form of it. -/
theorem appTop_fromSpecResidueField_eq_Γevaluation (S : Scheme.{u}) (s : S) :
    (S.fromSpecResidueField s).appTop =
      S.Γevaluation s ≫ (Scheme.ΓSpecIso (S.residueField s)).inv := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp [Scheme.Γevaluation, Scheme.evaluation, ← Scheme.ΓSpecIso_inv_naturality]

/-- **THE RESTRICTION OF A GLOBAL SECTION TO A FIBRE IS THE RESTRICTION OF A SECTION OF `S`**
(PROVEN, 2026-07-30): for `S` affine and `h s`, the composite
`Γ(S, ⊤) ⟶ Γ(X, ⊤) ⟶ Γ(X_s, ⊤)` is SURJECTIVE at every point `s` at which evaluation on `S`
is surjective — in particular, by `exists_point_ker_Γevaluation_eq_of_isMaximal`, at the point
cut out by any maximal ideal.

This is the half of degree-zero base change that `h` gives away, isolated: `Scheme.Hom.fiber_fac`
factors the composite as `(S.fromSpecResidueField s).appTop ≫ (f.fiberToSpecResidueField s).appTop`,
the second factor is an isomorphism by `h s`, and the first is `S.Γevaluation s` up to
`ΓSpecIso` by `appTop_fromSpecResidueField_eq_Γevaluation`.  **No properness, flatness or
finite presentation is used.** -/
theorem surjective_appTop_fiberι_comp_appTop (f : X ⟶ S) (s : S)
    (hs : IsIso (f.fiberToSpecResidueField s).appTop)
    (hsurj : Function.Surjective (S.Γevaluation s).hom) :
    Function.Surjective ((f.appTop ≫ (f.fiberι s).appTop).hom) := by
  haveI := hs
  have hfac : f.appTop ≫ (f.fiberι s).appTop
      = (S.fromSpecResidueField s).appTop ≫ (f.fiberToSpecResidueField s).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, f.fiber_fac s]
  rw [hfac, appTop_fromSpecResidueField_eq_Γevaluation, CommRingCat.hom_comp,
    CommRingCat.hom_comp]
  exact ((ConcreteCategory.bijective_of_isIso
      ((f.fiberToSpecResidueField s).appTop)).2.comp
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (S.residueField s)).inv).2).comp hsurj

/-- **THE COMMUTATIVE-ALGEBRA BRIDGE FROM GROTHENDIECK'S COMPLEX** — **PROVEN**
(2026-07-31).  Let `d : R^{n₀} ⟶ R^{n₁}` be a map of finite free modules whose IMAGE is
projective, and let `x ∈ ker d` be such that for every maximal ideal `𝔪` the fibre kernel
`ker(d ⊗ R/𝔪)` is the line spanned by the image of `x` — written, as everywhere in this file,
as `d⁻¹(𝔪·R^{n₁}) = R·x + 𝔪·R^{n₀}`.  Then `ker d = R·x` **on the nose**.

**Why projectivity of the image is exactly the right hypothesis, and how it is used twice.**
Projectivity splits `0 ⟶ ker d ⟶ R^{n₀} ⟶ range d ⟶ 0`, producing a retraction
`r : R^{n₀} ⟶ ker d`.  That single object discharges both finiteness obligations that the
Nakayama argument has and that no weaker hypothesis supplies:

* `ker d` is a quotient of the finite module `R^{n₀}`, hence **finite** — the file's other
  route to `Module.Finite` runs through `module_finite_appTop_of_isProper`, which is
  DOWNSTREAM of this bridge's consumer, so borrowing it would be circular;
* `ker d ∩ 𝔪·R^{n₀} ≤ 𝔪 · ker d`, because `r` maps `𝔪·R^{n₀}` into `𝔪 · ker d` and fixes
  `ker d` pointwise.  This is the conclusion that
  `inf_smul_top_le_smul_ker_of_flat_range` below obtains from flatness of the image by a Tor
  computation; here it is one line, and the two hypotheses agree, since a finitely presented
  flat module is projective and `range d` is finitely presented as soon as `ker d` is.

With those two, the fibre clause gives `ker d = R·x + 𝔪·(ker d)` for every maximal `𝔪`, and
`eq_bot_of_fg_of_le_smul_of_forall_isMaximal` above kills the quotient.

**No noetherian, no local, no flatness of `R`, and nothing geometric.**  This is pure module
theory over an arbitrary commutative ring, which is what makes it usable against the
non-noetherian bases this file must survive (audit block (A) on
`finiteType_appTop_of_isProper` below exhibits one). -/
theorem ker_eq_span_of_projective_range_of_forall_isMaximal
    {R : Type*} [CommRing R] {n₀ n₁ : ℕ}
    (d : (Fin n₀ → R) →ₗ[R] (Fin n₁ → R))
    (hproj : Module.Projective R ↥(LinearMap.range d))
    (x : ↥(LinearMap.ker d))
    (hfib : ∀ m : Ideal R, m.IsMaximal →
      Submodule.comap d (m • (⊤ : Submodule R (Fin n₁ → R))) =
        Submodule.span R {(x : Fin n₀ → R)} ⊔ m • (⊤ : Submodule R (Fin n₀ → R))) :
    (⊤ : Submodule R ↥(LinearMap.ker d)) = Submodule.span R {x} := by
  classical
  haveI := hproj
  -- a section of `R^{n₀} ↠ range d`
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  have hdσ : ∀ y : ↥(LinearMap.range d), d (σ y) = (y : Fin n₁ → R) := by
    intro y
    have := congrArg (fun (g : ↥(LinearMap.range d) →ₗ[R] ↥(LinearMap.range d)) => g y) hσ
    simpa [LinearMap.rangeRestrict] using congrArg Subtype.val this
  -- the resulting retraction `r : R^{n₀} ⟶ ker d`
  set q : (Fin n₀ → R) →ₗ[R] (Fin n₀ → R) :=
    (LinearMap.id : (Fin n₀ → R) →ₗ[R] (Fin n₀ → R)) - σ.comp d.rangeRestrict with hqdef
  have hmem : ∀ c : Fin n₀ → R, q c ∈ LinearMap.ker d := by
    intro c
    simp only [hqdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub]
    rw [hdσ (d.rangeRestrict c)]
    simp [LinearMap.rangeRestrict]
  set r : (Fin n₀ → R) →ₗ[R] ↥(LinearMap.ker d) :=
    LinearMap.codRestrict (LinearMap.ker d) q hmem with hrdef
  have hrk : ∀ k : ↥(LinearMap.ker d), r (k : Fin n₀ → R) = k := by
    intro k
    have hk0 : d.rangeRestrict (k : Fin n₀ → R) = 0 := by
      ext; simp [LinearMap.rangeRestrict]
    apply Subtype.ext
    show q (k : Fin n₀ → R) = (k : Fin n₀ → R)
    simp only [hqdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hk0,
      map_zero, sub_zero]
  have hrsurj : Function.Surjective r := fun k => ⟨(k : Fin n₀ → R), hrk k⟩
  haveI : Module.Finite R ↥(LinearMap.ker d) := Module.Finite.of_surjective r hrsurj
  -- `𝔪·R^{n₀} ∩ ker d ≤ 𝔪 · ker d`, read off the retraction
  have hdesc : ∀ (m : Ideal R) (k : ↥(LinearMap.ker d)),
      (k : Fin n₀ → R) ∈ m • (⊤ : Submodule R (Fin n₀ → R)) →
      k ∈ m • (⊤ : Submodule R ↥(LinearMap.ker d)) := by
    intro m k hk
    have hmap : r (k : Fin n₀ → R) ∈
        Submodule.map r (m • (⊤ : Submodule R (Fin n₀ → R))) :=
      Submodule.mem_map_of_mem hk
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr hrsurj] at hmap
    rw [hrk k] at hmap
    exact hmap
  -- Nakayama on the quotient by the line `R·x`
  set L : Submodule R ↥(LinearMap.ker d) := Submodule.span R {x} with hLdef
  have hquot : ∀ m : Ideal R, m.IsMaximal →
      (⊤ : Submodule R (↥(LinearMap.ker d) ⧸ L)) ≤
        m • (⊤ : Submodule R (↥(LinearMap.ker d) ⧸ L)) := by
    intro m hm
    rintro z -
    obtain ⟨k, rfl⟩ := L.mkQ_surjective z
    have hcomap : (k : Fin n₀ → R) ∈
        Submodule.comap d (m • (⊤ : Submodule R (Fin n₁ → R))) := by
      simp only [Submodule.mem_comap]
      have hk : d (k : Fin n₀ → R) = 0 := k.2
      rw [hk]
      exact zero_mem _
    rw [hfib m hm] at hcomap
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hcomap
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hvk : v = ((k - c • x : ↥(LinearMap.ker d)) : Fin n₀ → R) := by
      have hkv : (k : Fin n₀ → R) = c • (x : Fin n₀ → R) + v := huv.symm
      push_cast
      rw [hkv]
      abel
    have hvmem : (k - c • x : ↥(LinearMap.ker d)) ∈
        m • (⊤ : Submodule R ↥(LinearMap.ker d)) :=
      hdesc m _ (hvk ▸ hv)
    have hkx : L.mkQ k = L.mkQ (k - c • x) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hsub : k - (k - c • x) = c • x := by abel
      rw [hsub, hLdef]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    rw [hkx]
    have hmapq : L.mkQ (k - c • x) ∈
        Submodule.map L.mkQ (m • (⊤ : Submodule R ↥(LinearMap.ker d))) :=
      Submodule.mem_map_of_mem hvmem
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr L.mkQ_surjective] at hmapq
    exact hmapq
  haveI : Module.Finite R (↥(LinearMap.ker d) ⧸ L) :=
    Module.Finite.of_surjective L.mkQ L.mkQ_surjective
  have htop : (⊤ : Submodule R (↥(LinearMap.ker d) ⧸ L)) = ⊥ :=
    eq_bot_of_fg_of_le_smul_of_forall_isMaximal (Module.Finite.fg_top) hquot
  refine le_antisymm (fun k _ => ?_) le_top
  have hz : L.mkQ k = 0 := by
    have := htop.le (Submodule.mem_top (x := L.mkQ k))
    simpa using this
  simpa [hLdef, Submodule.Quotient.mk_eq_zero] using hz

/-- **LEAF 1a⁗ — GROTHENDIECK'S DEGREE-`0` COMPLEX, FINITE FREE, WITH PROJECTIVE IMAGE**
(LEAF, CUT 2026-07-31 out of `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero` immediately
below, which is now PROVEN over it together with the bridge above).

**THIS IS THE ONLY GEOMETRIC OBLIGATION LEFT IN THIS FILE**, and it is a NAMED CLASSICAL
THEOREM rather than an ad-hoc algebraic one: it is the degree-`0` part of the finite free
complex computing `Rf_*𝒪_X`, EGA III 6.10.5 / Mumford *Abelian Varieties* §5 / Hartshorne
III.12.2, together with the base-change clause that `h` supplies.  In the language of the
pin-free literature it is Stacks 0B91 (`Rf_*𝒪_X` is a **perfect** complex for `f` proper,
flat and of finite presentation) plus the observation that `h` makes `H⁰` commute with base
change, i.e. makes `range d` flat.

**What it says.**  With `R = Γ(S, ⊤)` and `A = Γ(X, ⊤)` there are `n₀`, `n₁` and an
`R`-linear `d : R^{n₀} ⟶ R^{n₁}` with

* `Module.Projective R (range d)` — the image of `d` is a projective `R`-module;
* `A ≃ₗ[R] ker d` — global sections are the equalizer of the two-term complex;
* for every maximal `𝔪`, `d⁻¹(𝔪·R^{n₁}) = R·(e 1) + 𝔪·R^{n₀}` — the SAME complex computes
  `H⁰` of the fibre after reduction mod `𝔪`, and that `H⁰` is the line spanned by the image
  of `1 ∈ A`.  This clause is `h s` read through the complex.

**RELATION TO THE STATEMENT IT REPLACES: they are EQUIVALENT, so no audit is voided.**  The
leaf below is derived from this one (`ker_eq_span_of_projective_range_of_forall_isMaximal`
above plus four lines of `Γ`-bookkeeping).  Conversely this one follows from that one exactly
as `exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber` far below is proved from
it: once `A ≅ R`, take `R^1 ⟶ R^0` with `d = 0`, whose image `⊥` is projective.  So every
negative result recorded on the leaf below — (D1)'s `ℤ_p ⋉ ℚ_p`, (D2)'s route, (E)'s cusp
`k[t², t³] ⊆ k[t]`, (F)'s circular diagonal, and audit blocks (A)–(D) on
`finiteType_appTop_of_isProper` — transfers verbatim and still rules out the same shortcuts.
**What the re-cut buys is not a weaker obligation but a NAMED one**: the whole
commutative-algebra half of the argument, which was previously entangled with the geometry,
is now proven, and what is left is a single classical theorem with a textbook proof.

**WHY `Module.Projective (range d)` AND NOT `Module.Flat`.**  The two agree here — `range d`
is finitely presented once `ker d` is finite, and finitely presented flat is projective — but
projectivity is the form that can be USED without first knowing `ker d` is finite, which is
precisely the finiteness this file is trying to establish.  Choosing `Flat` instead would
reintroduce the circularity through `module_finite_appTop_of_isProper`.  (`Flat` is what
`exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` far below asks for; that
statement sits underneath `module_finite_appTop_of_isProper` and so may use it.)

**FAITHFULNESS.**  `Module.Projective R (range d)` is TRUE in the classical situation and the
reason is worth recording, because it is where `h` does its work: `range d` is finitely
presented (`R^{n₀}` is finite free and `ker d ≅ A` is finite), and `Tor₁^R(range d, M)` is
exactly the obstruction to `H⁰(X, 𝒪) ⊗_R M ⟶ H⁰(X_M, 𝒪)` being an isomorphism.  Stacks 0E0S
— `f_*𝒪_X = 𝒪_Y` for `f` proper, flat, of finite presentation with geometrically reduced
connected fibres, **and this holds after any base change** — says that obstruction vanishes
for every `M`.  So flatness, hence projectivity, of the image is a *consequence of the
classical theorem including its base-change clause*, and asking for it is not asking for more
than the literature provides.  Without `h` it is false exactly where `h⁰` jumps; audit block
(A) on `finiteType_appTop_of_isProper` below carries the char-`2` wild-fibre witness.

**NON-VACUITY.**  The existential is not satisfiable by a degenerate choice: as noted above,
the cheapest witness `R^1 ⟶ R^0` requires `A = R·1`, which is what the leaf exists to prove.
That is a property of every terminal leaf and not a defect of this cut — the same paragraph
appears on `exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` below.

**THE ROUTE, AND ONE NEW REDUCTION THAT NEEDS NO COHERENCE AT ALL** (2026-07-31).  The Čech
description is the source of the complex and it is much cheaper than the coherence theorem
that pins it down.  `f` proper over an affine `S` makes `X` quasi-compact and separated, so a
finite affine cover `{U_i}` exists and every `U_i ∩ U_j` is affine.  Put
`C₀ := ∏_i Γ(U_i, 𝒪)`, `C₁ := ∏_{i<j} Γ(U_i ∩ U_j, 𝒪)` and `d :=` the difference of the two
restrictions.  Then, **by the sheaf axiom alone and with no cohomology theory whatsoever**:

* `A = ker d`;
* each `C_j` is a FLAT `R`-module, because `f` is flat and each `U` is affine;
* for every `R`-algebra `R'`, `Γ(X_{R'}, 𝒪) = ker(d ⊗_R R')`, because
  `Γ(U ×_S Spec R', 𝒪) = Γ(U, 𝒪) ⊗_R R'` for affine `U` and the cover base-changes.

The terms are flat but not finite, so this is NOT the leaf; the leaf's finite freeness is the
coherence theorem.  But the flat form is enough over an **artinian** base, and that reduction
is worth writing down because it is elementary and was not previously recorded:

> Let `R` be artinian local with residue field `k` and `length R = n`.  For an `R`-module `M`
> put `H⁰(M) := ker(d ⊗ M)`.  Flatness of `C₀` and `C₁` makes `H⁰` LEFT EXACT (snake lemma on
> the two exact rows `0 → C_j ⊗ M' → C_j ⊗ M → C_j ⊗ M'' → 0`).  Filter
> `0 = J_0 ⊂ ⋯ ⊂ J_n = R` with `J_i/J_{i-1} ≅ k`; left exactness embeds
> `H⁰(J_i)/H⁰(J_{i-1}) ↪ H⁰(k) = Γ(X_k, 𝒪) = k` by `h`, so
> `length_R A = length_R H⁰(R) ≤ n`.  Since `R ⟶ A` is injective
> (`injective_appTop_of_flat_of_surjective`), `length_R A ≥ n`, so `A = R·1`. ∎

Two notes on that reduction.  *First*, no tensor product is needed to state it: flatness of
`C₀` identifies `H⁰(J)` with the honest submodule `ker d ∩ J·C₀`, so the whole dévissage can
be written with `Submodule.inf` and `Submodule.smul`.  *Second*, it is exactly Step 1 of the
elementary route recorded on `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` below,
with the quasi-coherent ideal sheaf `J·𝒪_X` replaced by `J·C₀`; the sheaf-theoretic
formulation is not needed and mathlib's `IdealSheafData` need not be involved.

So the remaining work splits cleanly into two independent tasks:

1. **The Čech complex** (flat terms, base change, `A = ker d`) — provable at this pin from
   the sheaf axiom, `Flat f` and affine base change.  It closes the ARTINIAN case outright
   via the dévissage above, and it is the object the coherence theorem improves.
2. **Finite freeness**, i.e. replacing the flat Čech complex by a finite free one — the
   coherence theorem proper, which classically comes from the noetherian case (EGA III 3.2.1)
   plus limits.  Audit block (B) on `finiteType_appTop_of_isProper` below records what
   mathlib has for the second half (`AffineTransitionLimit.lean`) and what it lacks (object
   descent, EGA IV 8.8.2 / Stacks 01ZM). -/
theorem exists_finiteFree_projectiveRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber
    (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∃ (n₀ n₁ : ℕ) (d : (Fin n₀ → ↥Γ(S, ⊤)) →ₗ[↥Γ(S, ⊤)] (Fin n₁ → ↥Γ(S, ⊤)))
      (e : ↥Γ(X, ⊤) ≃ₗ[↥Γ(S, ⊤)] LinearMap.ker d),
      Module.Projective ↥Γ(S, ⊤) ↥(LinearMap.range d) ∧
      ∀ m : Ideal ↥Γ(S, ⊤), m.IsMaximal →
        Submodule.comap d (m • (⊤ : Submodule ↥Γ(S, ⊤) (Fin n₁ → ↥Γ(S, ⊤)))) =
          Submodule.span ↥Γ(S, ⊤) {((e 1 : LinearMap.ker d) : Fin n₀ → ↥Γ(S, ⊤))} ⊔
            m • (⊤ : Submodule ↥Γ(S, ⊤) (Fin n₀ → ↥Γ(S, ⊤))) :=
  sorry

/-- **1a‴ — `a|_{X_s} = 0 ⟹ a ∈ 𝔪 · R[a]`, FOR ITS OWN `a`** — **PROVEN** (2026-07-31) over
`exists_finiteFree_projectiveRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` and
`ker_eq_span_of_projective_range_of_forall_isMaximal` immediately above.  **The two statements
are EQUIVALENT** (the derivation in both directions is in that leaf's docstring), so
everything recorded below — including the audit blocks — is still live evidence, now about
the complex.  Read that docstring for where the file stands; read this one for what was tried.
It was itself RE-CUT 2026-07-30
out of `mem_smul_adjoin_of_appTop_fiberι_eq_zero` immediately below, which is PROVEN over it).
`𝔪` is `RingHom.ker (S.Γevaluation s)`, i.e. the maximal ideal cut out by `s` when `s` comes
from `exists_point_ker_Γevaluation_eq_of_isMaximal`.

**IT CARRIED, UNTIL 2026-07-31, THE WHOLE GEOMETRIC OBLIGATION OF THIS FILE.**  It carries
BOTH of the leaves this file had before, and it is the sharpest form either of them takes:
one element, one hypothesis, no quantifier over a submodule, no ideal, no `span {1}`, no
maximality — only *vanishing on a fibre*.  The two derivations are in the file, immediately
below and at
`mem_smul_top_of_appTop_fiberι_eq_zero`, and they are three lines each:

* the general `x ∈ R[a]` form follows because **`x` is its own `a`**.  Apply this leaf to `x`,
  getting `x ∈ 𝔪 · R[x]`, and push forward along `R[x] ≤ R[a]`, which holds by
  `Algebra.adjoin_le` since `x ∈ R[a]`.  Nothing is lost: `𝔪 · R[x] ≤ 𝔪 · R[a]`.
* the `Γ(X, ⊤)` form (`mem_smul_top_of_appTop_fiberι_eq_zero`) follows by pushing the same
  membership forward along `R[a] ≤ ⊤`.

So the file's two former leaves were **not two obligations**: the weaker one was a corollary of
the stronger, in the direction opposite to the one the old docstrings looked for.  They had
recorded (correctly) that the `Γ(X, ⊤)` statement does NOT imply the `R[a]` statement —
descending it needs `𝔪A ∩ R[a] ⊆ 𝔪·R[a]`, refuted by audit block (D1) below — and concluded
that neither subsumed the other.  The missing observation is that the implication runs the
*other* way for free, because `𝔪 · R[a]` only ever grows when `R[a]` does.

**DO NOT GENERALISE TO AN ARBITRARY SUBALGEBRA `B ⊆ Γ(X, ⊤)` WITH `x ∈ B ⟹ x ∈ 𝔪·B`.**
That is an unverified universally quantified clause of exactly the kind whose splitting was
declined on `exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` below, and getting
it wrong plants a FALSE leaf.  The reduction above does **not** need it and must not be
mistaken for it: it only ever instantiates `B` at `R[x]` for the very `x` in hand, i.e. at a
one-generator subalgebra, which is the only case this leaf asserts.

**FAITHFULNESS — VOUCHED, AND THE PREVIOUS AUDIT TRANSFERS BECAUSE THE TWO ARE EQUIVALENT.**
CLAUDE.md's rule is that a leaf restated a second time voids its earlier audit.  That rule
guards against a restatement whose truth value may have moved; here it has not, because the
old statement and this one are **inter-derivable**, and both directions are one line:
this one from the old one by `x := a` and `Algebra.self_mem_adjoin_singleton` (checked in Lean
against the sorried old form before the re-cut), the old one from this one below.  So the
audit is inherited legitimately rather than by assumption.  On its own terms: the hypothesis
`a = 0` is in the domain, so nothing is forgotten and there is no vacuity question; `h` is
load-bearing, and the witness for THAT is not the one the neighbouring docstrings use, because
theirs does not satisfy this leaf's hypothesis.  **Corrected 2026-07-30 while re-cutting.**
Take `Z` proper non-reduced over `k` with `ε ∈ Γ(Z, 𝒪)`, `ε² = 0`, `ε ∉ k`; take
`R = k[t]_{(t)}`, `𝔪 = (t)`, `S = Spec R` and `X = S ×_k Z`, so that `f` is proper, flat and of
finite presentation and fails only `h` (indeed `Γ(X_s, 𝒪) = κ(s)[ε] ≠ κ(s)`).  Then
`A = R ⊕ Rε`.  The neighbouring statements are refuted by `a = ε`, but `ε` restricts to `ε ≠ 0`
on `X_s`, so it is NOT a witness here.  The witness here is `a = t·ε`: it restricts to
`t̄·ε = 0` on `X_s`, while `R[a] = R ⊕ R·tε` (as `(tε)² = 0`), so
`𝔪·R[a] = tR ⊕ t²R·ε ∌ tε` — the `ε`-coefficient would have to lie in `t²R` and it is `t`.

**WHAT NOT TO DO.**  Do **not** weaken the hypothesis to `a ∈ 𝔪·Γ(X, ⊤)`.  That version is
FALSE — audit block (D1) below refutes it with `R = ℤ_p`, `A = ℤ_p ⋉ ℚ_p`, `a = x` — so any
proof that never mentions the fibre `X_s` is wrong.  `a|_{X_s} = 0` is strictly stronger: it
says `a` is a section of the ideal sheaf `𝔪𝒪_X`, and
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` below is precisely the assertion that
those two conditions coincide for `Γ(X, ⊤)`.

**WHAT REMAINS, GEOMETRICALLY, AND WHY INTEGRALITY ALONE CANNOT DO IT.**  `a` induces a proper
surjection `g : X ⟶ Spec R[a]` over `S`; `h` forces the fibre of `Spec R[a]` at `s` to be a
single point with residue field `κ(𝔪)`, and what is missing is that this fibre is also
REDUCED — equivalently `R[a] ⊗_R κ(𝔪) = κ(𝔪)`, equivalently the conclusion.  Integrality of
`a` (free, `isIntegral_appTop_of_universallyClosed`) gets one step and then stops, and it is
worth recording exactly where so it is not re-tried: from
`aⁿ + c_{n-1}a^{n-1} + ⋯ + c₀ = 0` with `cᵢ : R`, applying `·|_{X_s}` kills every term but
`c₀`, so `c₀ ∈ 𝔪`, hence `a · (a^{n-1} + ⋯ + c₁) = -c₀·1 ∈ 𝔪·R[a]`.  That is `a·u ∈ 𝔪·R[a]`,
and it gives `a ∈ 𝔪·R[a]` only if `u` is a unit — which it need not be, since `u` restricts to
`c₁|_{X_s}` and nothing forces `c₁ ∉ 𝔪`.  The `a = tε` witness above is exactly this failure
with `n = 2`, `c₁ = c₀ = 0`, `u = a`: `a·u = (tε)² = 0` lies in `𝔪·R[a]` for free and says
nothing.  So the fibre-reducedness input is genuinely irreducible: no argument using only that
`R[a]` is a finite `R`-algebra can close this leaf.

**AND THE FIBRE REALLY IS A SINGLE `κ(𝔪)`-POINT — that half is free, so only reducedness is
owed** (verified 2026-07-30).  `X.toSpecΓ` is universally closed with dense image (a global
section vanishing on all of `X` is `0`), hence surjective; `A` is integral over `R` hence over
`R[a]`, and `R[a] ↪ A`, so `Spec A ⟶ Spec R[a]` is surjective by lying over.  Surjectivity is
stable under base change, so `X_s ↠ Spec (R[a] ⊗_R κ(s))`.  That algebra is finite over
`κ(s)`, hence artinian with finite discrete spectrum, while `h` makes `Γ(X_s, 𝒪) = κ(s)` have
no nontrivial idempotents, so `X_s` is connected and its image is one point; the composite
`R[a] ⊗ κ(s) ⟶ κ(s)` is onto (its image is a `κ(s)`-subalgebra of `κ(s)`), so that point has
residue field exactly `κ(s)`.  What is left is that the local artinian ring `R[a] ⊗_R κ(s)`
has zero maximal ideal, which is the conclusion.

**ONE FREE REDUCTION, AND IT IS THE CONSUMER'S ONLY USE.**  The single consumer
(`adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` below) calls this only at points `s`
coming from `exists_point_ker_Γevaluation_eq_of_isMaximal`, where `S.Γevaluation s` is
SURJECTIVE, so `κ(s) = R/𝔪` and `𝔪` is maximal.  A prover may therefore assume `𝔪` maximal at
no cost, and then `R[a]/𝔪·R[a]` is a `κ(s)`-vector space, so Step 0 of the elementary route on
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` below applies verbatim: the conclusion
localises at `𝔪`, and one may take `R` LOCAL.  That is the only part of the route that is free
here; the rest of it (dévissage of `Γ(X, J𝒪_X)`, induction on `dim R`) still needs a noetherian
base and quasi-coherent ideal sheaves, and is unchanged by this re-cut.

**WHAT THIS RE-CUT DOES NOT INHERIT.**  The Čech/`Tor₁` obstruction analysis on
`mem_smul_top_of_appTop_fiberι_eq_zero` below is about `A = Γ(X, ⊤) = ker d` and identifies
that statement with `Tor₁^R(range d, κ(𝔪)) = 0`.  It is a route to the `Γ(X, ⊤)` form ONLY:
`R[a]` is a subalgebra of `ker d` and not a term of the Čech complex, so the identification
does not transfer to this leaf.  It is retained there because it is real content — and because
it says something this leaf's route does not, namely that the `Γ(X, ⊤)` form is one
application of the local criterion away from Grothendieck finiteness in POSITIVE degree.  A
prover who closes the `Γ(X, ⊤)` form that way has **not** closed this leaf, and this leaf is
what `finiteType_appTop_of_isProper` needs. -/
theorem self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) (s : S)
    (a : ↥Γ(X, ⊤)) (ha : (f.fiberι s).appTop.hom a = 0) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    a ∈ RingHom.ker (S.Γevaluation s).hom •
      (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  obtain ⟨n₀, n₁, d, e, hproj, hfib⟩ :=
    exists_finiteFree_projectiveRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber f h
  -- STEP 1: the bridge makes `ker d` the line spanned by `e 1`, so `R ⟶ A` is onto.
  have hspan := ker_eq_span_of_projective_range_of_forall_isMaximal d hproj (e 1) hfib
  have halg : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) = f.appTop.hom := rfl
  obtain ⟨c, hc⟩ : ∃ c : ↥Γ(S, ⊤), a = algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) c := by
    have hmem : e a ∈ Submodule.span ↥Γ(S, ⊤) {e 1} := hspan ▸ Submodule.mem_top
    obtain ⟨c, hcv⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, ?_⟩
    have he : e a = e (c • (1 : ↥Γ(X, ⊤))) := by rw [map_smul]; exact hcv.symm
    have ha' := e.injective he
    rw [ha', Algebra.smul_def, mul_one]
  -- STEP 2: `a|_{X_s} = 0` forces `c` into the ideal cut out by `s`.
  have hfac : f.appTop ≫ (f.fiberι s).appTop
      = (S.fromSpecResidueField s).appTop ≫ (f.fiberToSpecResidueField s).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, f.fiber_fac s]
  have hck : c ∈ RingHom.ker (S.Γevaluation s).hom := by
    haveI := h s
    have h0 : ((f.appTop ≫ (f.fiberι s).appTop)).hom c = 0 := by
      rw [CommRingCat.hom_comp]
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← halg, ← hc]
      exact ha
    rw [hfac, appTop_fromSpecResidueField_eq_Γevaluation, CommRingCat.hom_comp,
      CommRingCat.hom_comp] at h0
    simp only [RingHom.coe_comp, Function.comp_apply] at h0
    have hz1 : (f.fiberToSpecResidueField s).appTop.hom
        (((Scheme.ΓSpecIso (S.residueField s)).inv).hom ((S.Γevaluation s).hom c)) =
        (f.fiberToSpecResidueField s).appTop.hom 0 := by rw [map_zero]; exact h0
    have h1 := (ConcreteCategory.bijective_of_isIso
      ((f.fiberToSpecResidueField s).appTop)).1 hz1
    have hz2 : ((Scheme.ΓSpecIso (S.residueField s)).inv).hom ((S.Γevaluation s).hom c) =
        ((Scheme.ΓSpecIso (S.residueField s)).inv).hom 0 := by rw [map_zero]; exact h1
    have h2 := (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (S.residueField s)).inv)).1 hz2
    exact RingHom.mem_ker.mpr h2
  -- STEP 3: `a = c · 1` with `c ∈ 𝔪` and `1 ∈ R[a]`.
  rw [hc, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem_smul hck (Subalgebra.one_mem _)

/-- **LEAF 1a″ — A SECTION OF `R[a]` VANISHING ON THE FIBRE `X_s` LIES IN `𝔪 · R[a]`** —
**PROVEN** (2026-07-30) over `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero` immediately
above, by the observation that `x` is its own `a`: the leaf applied to `x` gives
`x ∈ 𝔪 · R[x]`, and `R[x] ≤ R[a]` because `x ∈ R[a]`.  (It was itself CUT 2026-07-30 out of
`adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` below, which is PROVEN over it; that
consumer and its call are unchanged by the re-cut.)  `𝔪` is
`RingHom.ker (S.Γevaluation s)`, i.e. the maximal ideal cut out by `s` when `s` comes from
`exists_point_ker_Γevaluation_eq_of_isMaximal`.

**WHAT THIS CUT DOES.**  The theorem below is `R[a] = R·1 + 𝔪·R[a]`.  Its `R·1` half is pure
bookkeeping — lift the fibre value of `x` to some `r : R`, which
`surjective_appTop_fiberι_comp_appTop` says is possible — and what is left is this statement,
which contains no ideal, no `span {1}` and no maximality, only *vanishing on a fibre*.  The
same cut is made for the other statement of this file at
`mem_smul_top_of_appTop_fiberι_eq_zero`, and the two are visibly the same sentence with `R[a]`
replaced by `Γ(X, ⊤)`; both are now corollaries of the one-element leaf above, whose docstring
carries the obstruction analysis. -/
theorem mem_smul_adjoin_of_appTop_fiberι_eq_zero (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) (s : S)
    (a : ↥Γ(X, ⊤)) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ x ∈ (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule,
      (f.fiberι s).appTop.hom x = 0 →
      x ∈ RingHom.ker (S.Γevaluation s).hom •
        (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  intro x hx hxvan
  have hle : (Algebra.adjoin ↥Γ(S, ⊤) {x}).toSubmodule ≤
      (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule := fun y hy =>
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx) hy
  exact Submodule.smul_mono le_rfl hle
    (self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero f h s x hxvan)

/-- **LEAF 1a′ — `R[a] = R·1 + 𝔪·R[a]` FOR EVERY `a ∈ Γ(X, ⊤)` AND EVERY MAXIMAL `𝔪`** —
**PROVEN** (2026-07-30) over `mem_smul_adjoin_of_appTop_fiberι_eq_zero` immediately above,
which is the same statement with the `R·1` and the maximality removed; the reduction is the
maximal-ideal ↔ point dictionary of the block introduction and nothing else.
(CUT 2026-07-30 out of `finiteType_appTop_of_isProper` below, which is PROVEN over it.)

**What it says.**  `R = Γ(S, ⊤)`, `A = Γ(X, ⊤)`, `φ = f.appTop` giving `A` its `R`-algebra
structure.  For each `a : A` the subalgebra `R[a] = Algebra.adjoin R {a}` is generated as an
`R`-module by `1` together with `𝔪 · R[a]`.  Equivalently `R[a] ⊗_R κ(𝔪) = κ(𝔪)`, i.e. the
degree-zero comparison map `R[a] ⊗_R κ(𝔪) ⟶ Γ(X_𝔪, 𝒪)` is INJECTIVE (surjectivity onto
`Γ(X_𝔪, 𝒪) ≅ κ(𝔪)` is free from `h`).  It is the SAME statement as leaf 3's injectivity —
see `surjective_quotientMap_appTop_of_isIso_appTop_fiber` — with `A` replaced throughout by a
**finite** subalgebra of it, and that replacement is the entire point of the cut.

**WHY THIS CUT.**  `finiteType_appTop_of_isProper` was the last piece of Grothendieck
finiteness in degree `0`, and the only route recorded for it needed limits and object descent
(audit block (B) on that theorem: EGA IV 8.8.2 / Stacks 01ZM, the one half `Mathlib` does not
have).  Audit block (D2) there gives a second, independent route which needs no limit theory
at all, and this is its target.  Since integrality makes `R[a]` a **finite** `R`-module,
`eq_bot_of_fg_of_le_smul_of_forall_isMaximal` above applies to it directly, and the theorem
below is exactly that Nakayama step.  Nothing in the cut uses
`Module.Finite ↥Γ(S,⊤) ↥Γ(X,⊤)`, so it is not circular.

**FAITHFULNESS — VOUCHED, AND `h` IS LOAD-BEARING.**  The statement is TRUE under these
hypotheses: `h` plus properness, flatness and finite presentation give `𝒪_S ≅ f_*𝒪_X` over an
arbitrary base (Stacks 0E0S), so `A = R·1` and the inclusion is trivial.  It is *not* vacuous
and `h` cannot be dropped: for `X = S ×_k Z` with `Z` a proper non-reduced `k`-scheme having
`ε ∈ Γ(Z, 𝒪)`, `ε² = 0`, `ε ∉ k`, the element `a = ε` gives `R[ε] = R·1 ⊕ R·ε` while
`R·1 + 𝔪·R[ε] = R·1 ⊕ 𝔪·ε` does not contain `ε`.  Such an `f` is proper, flat and of finite
presentation and fails only `h`.

**WHAT NOT TO DO.**  Do **not** weaken this to the abstract `𝔪A ∩ R[a] ⊆ 𝔪 · R[a]`, which is
what the statement looks like it is about.  That version is FALSE — audit block (D1) below
refutes it with `R = ℤ_p`, `A = ℤ_p ⋉ ℚ_p`, `a = x` — so any proof that never mentions the
fibre `X_𝔪` is wrong.  The geometric input, written out in (D2), is that `a` induces a proper
surjection `X ⟶ Spec R[a]` over `S` whose fibres are single points with residue field
`κ(𝔪)`; what remains is that those fibres are also REDUCED.

**HOW IT RELATES TO THE FILE'S OTHER STATEMENT OF THE SAME KIND, AND WHY NEITHER SUBSUMES THE
OTHER.**  (Both are now proven over their fibre-vanishing forms; the remark is about those.)
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` is the same equation for `A` itself
rather than for `R[a]`.  It does **not** imply this leaf: descending `A = R·1 + 𝔪A` to `R[a]`
requires exactly `𝔪A ∩ R[a] ⊆ 𝔪 · R[a]`, which (D1) refutes.  It implies this leaf only via
`Module.Finite ↥Γ(S,⊤) ↥Γ(X,⊤)`, which is downstream of *this* leaf — so as the file is
ordered the two are separate obligations and neither subsumes the other.  They are
nevertheless the same mathematics at different generality, so anyone closing that leaf should
check whether the argument also gives this one for finite subalgebras; if it does, both close
at once and the file's noetherian gap disappears with them. -/
theorem adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ (a : ↥Γ(X, ⊤)) (m : Ideal ↥Γ(S, ⊤)), m.IsMaximal →
      (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule ≤
        Submodule.span ↥Γ(S, ⊤) {(1 : ↥Γ(X, ⊤))} ⊔
          m • (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  intro a m hm
  obtain ⟨s, hker, hsurj⟩ := exists_point_ker_Γevaluation_eq_of_isMaximal S m hm
  intro x hx
  obtain ⟨r, hr⟩ := surjective_appTop_fiberι_comp_appTop f s (h s) hsurj
    ((f.fiberι s).appTop.hom x)
  rw [CommRingCat.hom_comp] at hr
  have hvan : (f.fiberι s).appTop.hom (x - algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r) = 0 := by
    have hid : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r = f.appTop.hom r := rfl
    rw [map_sub, hid, ← RingHom.comp_apply, hr, sub_self]
  have hradj : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r ∈
      (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule :=
    (Algebra.adjoin ↥Γ(S, ⊤) {a}).algebraMap_mem r
  have hmem := mem_smul_adjoin_of_appTop_fiberι_eq_zero f h s a _
    (Submodule.sub_mem _ hx hradj) hvan
  rw [hker] at hmem
  have h1 : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r ∈
      Submodule.span ↥Γ(S, ⊤) {(1 : ↥Γ(X, ⊤))} :=
    Submodule.mem_span_singleton.mpr ⟨r, by simp [Algebra.smul_def]⟩
  exact Submodule.mem_sup.mpr ⟨_, h1, _, hmem, by ring⟩

/-- **LEAF 1a — `Γ(X, ⊤)` IS A FINITE-TYPE `Γ(S, ⊤)`-ALGEBRA** (LEAF, 2026-07-28), the whole
remaining content of Grothendieck's finiteness theorem in degree `0` (EGA III 3.2.1,
Stacks 02O5 / 0B91) once the integral half is discharged.

**Where it comes from.**  `module_finite_appTop_of_isProper` below asks that `Γ(X, ⊤)` be a
*finite* `Γ(S, ⊤)`-module.  `RingHom.finite_iff_isIntegral_and_finiteType` splits that into
integrality and finite-type-ness, and integrality is already in the pin:
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` applies verbatim (properness gives
`UniversallyClosed f`, and `S` is affine).  So this leaf is exactly what is left.

**Why it is not formal.**  For non-affine `X`, `Γ(X, ⊤)` is the equalizer of a finite Čech
diagram of finite-type `R`-algebras — the sheaf axiom for a finite affine cover — and an
`R`-subalgebra of a finite-type `R`-algebra need not be of finite type, *even when it is
integral over `R`*.  Properness must therefore be used again here; the classical proofs go
through dévissage and Chow's lemma (Stacks 02O5), or through the projective case plus
cohomology.

**WITNESS FOR THAT DISMISSAL** (2026-07-28 — the claim above is CORRECT, but it was stated
without the step that actually makes it a counterexample, and that step is not obvious).
"Nagata's examples exist" is not by itself a refutation of the subalgebra route: one must
also exhibit the *ambient finite-type algebra*, and `Frac R` is not a finite-type `R`-algebra
in general.  It is in **dimension one**.  Take `R` a `1`-dimensional noetherian local domain
whose integral closure `R'` in `K = Frac R` is not a finite `R`-module (Nagata), and let
`t ≠ 0` lie in the maximal ideal.  Inverting `t` kills the only nonzero prime, so
`B := R[1/t] = K` is generated by **one** element over `R`, hence of finite type; and
`integralClosure R B = R'`, which is not a finite `R`-module.  So the purely ring-theoretic
statement

  "`A` an `R`-subalgebra of a finite-type `R`-algebra, `A` integral over `R`, `R` noetherian
   ⟹ `A` of finite type over `R`"

is **FALSE**, and no cut may use it as a sub-leaf.

**Axes searched and closed** (2026-07-28), so that they are not re-searched:
* `Mathlib`'s `finite_appTop_of_universallyClosed` — **verified unusable**, and not merely
  because it is stated over a field: its engine
  `RingHom.finite_of_algHom_finiteType_of_isJacobsonRing` requires `[DivisionRing L]` for the
  algebra being shown finite, so it needs `Γ(X, ⊤)` to be a *field*.  That is what
  `[IsIntegral X]` over a field buys and what an arbitrary affine base cannot.
* `IsFinite = IsIntegralHom ⊓ LocallyOfFiniteType`
  (`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`) applied to `Spec.map f.appTop`:
  integrality is free by 1, so this reduces the goal to `LocallyOfFiniteType (Spec.map
  f.appTop)`, which **is** the goal.  Circular.
* `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` — needs `[Subsingleton X]`.
* Descending finite-type along the proper surjection `X ⟶ Spec A` — fppf descent
  (Stacks 02JS) needs the covering flat and locally of finite presentation, and `X.toSpecΓ`
  is neither; the proper-surjective version is Chevalley-strength, i.e. no weaker than the
  goal.
* `Mathlib/AlgebraicGeometry/SpreadingOut.lean` — spreads out *morphisms on stalks*; it has
  no limits of schemes, so it does not give the reduction of the general case to a noetherian
  base.  That reduction remains unavailable.

**Note on the unused hypotheses.**  The integral-embedding chain described below uses neither `[Flat f]` nor
`[LocallyOfFinitePresentation f]` — they are needed only for the non-noetherian generality
(Stacks 0B91, where flatness of `𝒪_X` over `S` is what drives the limit argument), which
confirms the remark below that a prover over a noetherian base may ignore them.

**The statement is TRUE.**  `IsProper` bundles `IsSeparated`, `UniversallyClosed`,
`LocallyOfFiniteType` and `QuasiCompact`, so `f` is qcqs; with `[LocallyOfFinitePresentation
f]` it is of finite presentation, and `𝒪_X` is a finitely presented `𝒪_X`-module flat over
`S` exactly because `[Flat f]`.  That is precisely the hypothesis set of **Stacks 0B91**
(`Rⁱf_*ℱ` is finitely presented), whose `i = 0` case over affine `S` is this statement.

**THE "JUST BUILD NAGATA / UNIVERSALLY JAPANESE" ROUTE IS REFUTED** (2026-07-28, and this
supersedes a rescoping that sent an owner at exactly that).  The proposal was: `Γ(X, ⊤)` is
integral over `R` (free, `isIntegral_appTop_of_universallyClosed`) and embeds by the sheaf
axiom into `∏ i, Γ(X, Uᵢ)` over a finite affine cover, each factor of finite type
(`Scheme.Hom.finiteType_appLE`); so `Γ(X, ⊤) ≤ integralClosure R (∏ i, Γ(X, Uᵢ))` and the
leaf would follow from the purely ring-theoretic

> `R` noetherian universally Japanese, `B` of finite type over `R` ⟹ `integralClosure R B`
> is a finite `R`-module.

Every step of that chain is correct except the last, and **the ring-theoretic statement is
FALSE**, so no amount of Nagata theory closes this leaf.  Witness, over *any* field `k`
(`k` is noetherian, Jacobson, excellent, universally Japanese — every hypothesis one could
want): take `B = k[x, y]/(y²)`, of finite type over `k`.  **Nilpotents are integral over
every subring**, so for `a ∈ k` and `f ∈ k[x]` the element `a + f(x)·y` satisfies the monic
`(T − a)² = T² − 2aT + a²`; hence

  `integralClosure k B = k ⊕ k[x]·y`,

which is infinite-dimensional over `k`.  It is not even of finite type as a `k`-algebra:
the subalgebra generated by `a₁ + f₁y, …, aₙ + fₙy` is `k ⊕ (span_k {f₁, …, fₙ})·y`, because
`(aᵢ + fᵢy)(aⱼ + fⱼy) = aᵢaⱼ + (aᵢfⱼ + aⱼfᵢ)y`.  Checked in `Singular`:
`reduce((3 + (x⁵+x)y − 3)^2, std(y²)) = 0`.

So the containment `Γ(X, ⊤) ≤ integralClosure R (∏ i, Γ(X, Uᵢ))` is true and carries **no
finiteness information at all** as soon as the ambient algebra has nilpotents, i.e. as soon
as `X` is non-reduced.  `Mathlib`'s own API is the corroborating evidence: the analogous
theorem it does have, `finite_of_algHom_finiteType_of_isJacobsonRing`
(`Mathlib/RingTheory/Jacobson/Ring.lean`), is stated for a `K`-**subfield** `L` of a
finite-type algebra, `[DivisionRing L]`, and the witness above is precisely why that binder
cannot be weakened to "integral `K`-subalgebra".

**What the Nagata route *would* give, if the theory existed.**  Only the reduced case, and
only over a noetherian base.  For `B` finite type over noetherian `R` and **reduced**,
`B ↪ ∏ (B/𝔭)` over the finitely many minimal primes; inside each domain `B/𝔭`, an element
integral over `R` is algebraic over `Frac(R/𝔮)`, hence lies in the relative algebraic
closure of `Frac(R/𝔮)` in the finitely generated field extension `Frac(B/𝔭)`, which is a
*finite* extension; Japanese-ness makes its integral closure module-finite, and a submodule
of a finite module over a noetherian ring is finite.  That proves the leaf for `X` reduced
over a noetherian universally Japanese base and leaves three separate gaps, each of which is
itself a theory build:

1. **nilpotents on `X`** — the dévissage `0 ⟶ 𝒩 ⟶ 𝒪_X ⟶ 𝒪_{X_red} ⟶ 0` needs `Γ(X, 𝒩)`
   finite for a coherent ideal sheaf `𝒩`, i.e. it needs *this very theorem for coherent
   sheaves* rather than for `𝒪_X`.  Degree-zero finiteness for `𝒪_X` alone does not induct.
2. **the noetherian reduction** — the hypotheses `[Flat f] [LocallyOfFinitePresentation f]`
   are there exactly so that the statement descends to a finite-type `ℤ`-subalgebra of `R`
   (Stacks 0B91), and limits/approximation of schemes are absent from the pin
   (`SpreadingOut.lean` spreads out *stalk* morphisms only).
3. **that the bases in play are universally Japanese** — needs "finite type over `ℤ` is
   Nagata", the hard half of Nagata theory (Krull–Akizuki + Noether normalization).

Verified absent from the pin `a3364faec4` by direct grep on 2026-07-28: no `Japanese`,
`Nagata`, `N-1`/`N-2`, or `excellent` anywhere in `Mathlib/RingTheory/` (the single `Nagata`
hit is an attribution in `NoetherNormalization.lean`); no Chow's lemma, no coherent sheaves,
no sheaf cohomology and no higher direct images anywhere in `Mathlib/AlgebraicGeometry/`
(`Modules/` contains only `Presheaf.lean`, `Sheaf.lean`, `Tilde.lean`).  **The refuting
check on this leaf is therefore unchanged and is a grep, not an argument**: if coherent
sheaves with a finiteness theorem, or Chow's lemma, ever land in the pin, this leaf is a
corollary; until then it is a theory build and no ring-theoretic shortcut exists.

Mathlib's `finite_appTop_of_universallyClosed` is not usable as a shortcut either: it is
stated over a *field* and under `[IsIntegral X]`, and its Artin–Tate step
(`RingHom.finite_of_algHom_finiteType_of_isJacobsonRing` applied to `Γ(X, ⊤) ⟶ Γ(X, U)`)
needs `Γ(X, ⊤)` to be a field, which is what irreducibility over a field buys and what an
arbitrary affine base does not.

`[Flat f]` is listed because over a base that is not noetherian the finiteness theorem is
stated for a proper morphism *of finite presentation* with the sheaf flat over the base; it
is not otherwise used, and a prover working over a noetherian base may ignore it.

**THIS LEAF CANNOT BE DISSOLVED BY WEAKENING THE RING THEORY DOWNSTREAM** (checked
2026-07-28, with a counterexample, because it is the obvious way to try to make this leaf
unnecessary).  Its only consumer is `module_finite_appTop_of_isProper`, whose only purpose is
to feed `Module.Finite R A` to `surjective_algebraMap_of_finite_of_forall_isMaximal`
(Nakayama on the cokernel) below.  Since integrality of `A` over `R` is **free** (step 1
above), one naturally asks whether Nakayama there can be run on integrality instead — which
would delete this leaf outright.  It cannot: the statement

  "`φ : R ⟶ A` integral, and `A = φ(R) + 𝔪A` for every maximal `𝔪` ⟹ `φ` surjective"

is **FALSE**.  Witness: `R = ℤ`, and `A = ℤ ⊕ N` the square-zero extension of `ℤ` by any
nonzero `ℚ`-vector space `N`, with `(n, v) * (m, w) = (nm, nw + mv)`.  Then

* `A` is integral over `ℤ`: `(n, v)` satisfies the monic `(X - n)² = 0`, since
  `((n, v) - n)² = (0, v)² = 0`;
* for every prime `p`, `pA = pℤ ⊕ pN = pℤ ⊕ N` because `N` is a `ℚ`-vector space, so
  `ℤ + pA = ℤ ⊕ N = A` — indeed `A/pA ≅ ℤ/pℤ`, so `R/𝔪 ⟶ A/𝔪A` is even *bijective* at
  every maximal ideal;
* yet `ℤ ⟶ A` is not surjective, `N ≠ 0`.

So finiteness — not integrality — is what makes Nakayama run, and this leaf is load-bearing
rather than bookkeeping.

**FAITHFULNESS.** Properness is essential: `𝔸¹_S ⟶ S` is flat and of finite presentation and
has `Γ = R[x]`, which *is* of finite type — so the counterexample to the finite-*module*
statement is not one to this one.  The right witness that properness is doing work here is
the non-quasi-compact / non-separated side: `Γ` of an infinite disjoint union of copies of
`S` is `R^ℕ`, not a finite-type `R`-algebra, and quasi-compactness (a consequence of
universal closedness) is what excludes it.

---

**AUDIT BLOCK (2026-07-29).**  Three findings, kept separate from the paragraphs above so
that the concurrent rewrite of them merges cleanly.  Nothing here is proven in Lean; all of
it is evidence about *where* the leaf stands.  **(A) is a FALSITY AUDIT and it settled: the
statement as it stood was false, and the hypothesis `h` in the signature below is the
repair.**  Everything written *above* this block was audited against the `h`-free statement
and remains accurate as a description of the geometry, but its recurring phrase "this leaf"
now means the `h`-carrying statement.

**(A) REFUTED AND REPAIRED (2026-07-29).  WITHOUT the fibrewise hypothesis `h` this leaf is
FALSE over a non-noetherian base.**  The 2026-07-29 audit that stood here recorded the
obstruction exactly and asked for a single missing witness; the witness exists, in char `2`,
and is written out below.  `h` has therefore been ADDED to this leaf and to
`module_finite_appTop_of_isProper`; all three call sites already carried it, so the repair
cost nothing downstream.  **Do not "generalise" it away again.**

*Step 1 — the reduction (this part was already correct).*  The classical finiteness theorem
(EGA III 3.2.1, Stacks 02O5) is stated for a **locally noetherian** base.  The
non-noetherian statement that *is* in the literature is Stacks 0B91: for `f` proper, flat
and of finite presentation and `F` finitely presented and `S`-flat, `Rf_*F` is a **perfect**
object of `D(𝒪_S)` whose formation commutes with base change.  Perfect means locally a
bounded complex of finite free modules — it does **not** say the individual cohomology
modules are finite, and in general they are not: `H⁰` of a two-term complex `[Rᵃ ⟶ Rᵇ]` is a
kernel, and a kernel of a matrix over a non-noetherian ring need not be finitely generated.

Write `S = Spec R` with `R` an `R₀`-algebra, `R₀` noetherian, and let `K` be a bounded
complex of finite free `R₀`-modules computing `Rf₀_*𝒪_{X₀}` for a model `X₀ ⟶ Spec R₀` (the
standard "Mumford complex", EGA III 6.10.5; Mumford, *Abelian Varieties* §5).  For `R₀` a
PID the universal-coefficient sequence of `K` is exact, giving

  `0 ⟶ H⁰(X₀, 𝒪) ⊗_{R₀} R ⟶ Γ(X, 𝒪_X) ⟶ Tor₁^{R₀}(H¹(X₀, 𝒪), R) ⟶ 0`

for `X = X₀ ×_{Spec R₀} Spec R`.  The left term is a finite `R`-module, so `Γ(X, 𝒪_X)` is a
finite `R`-module **iff** `Tor₁^{R₀}(H¹(X₀, 𝒪), R)` is.  Base change preserves `IsProper`,
`Flat` and `LocallyOfFinitePresentation`, so every hypothesis of this leaf survives, and
`Spec R` is affine.

*Step 2 — the witness, a WILD multiple fibre in char 2.*  What was missing was a proper flat
finitely-presented family over a noetherian ring with **torsion in `H¹(𝒪)`**.  In char `0`
there is none of the expected shape — all multiple fibres of an elliptic fibration are tame
and `R¹f_*𝒪` is locally free, which is why the Dolgachev-surface attempt fails and must not
be retried.  Torsion needs a **wild** fibre, hence char `p`, and the smallest one is
explicit:

Let `k = 𝔽₂` and let `E : y² + xy = x³ + 1` be the elliptic curve over `k`.  It is
**ordinary** (`j = 1/Δ = 1 ≠ 0`; `#E(𝔽₂) = 4`, so `a₂ = -1` is odd), and its unique nonzero
`2`-torsion point is `τ = (0, 1)`: negation on `y² + a₁xy = x³ + a₆` sends `(x, y)` to
`(x, y + a₁x)`, here `(x, y + x)`, so `P = -P` forces `x = 0`, and then `y² = 1`, `y = 1`.
*(Verified in PARI/GP: `j = 1`, `ellorder(E, [0,1]) = 2`, `#E(𝔽₂) = 4`.)*
Translation by `τ` is a fixed-point-free involution of `E`.

Let `C = P¹` with coordinate `x` and let `σ : x ↦ x + 1`, an involution in char `2` whose
only fixed point is `∞` — Artin–Schreier, so the ramification at `∞` is **wild** and
`C ⟶ C/σ = P¹` is given by the invariant `y = x² + x`.  Let `G = ℤ/2` act on `E × C`
diagonally by `(e, x) ↦ (e + τ, x + 1)`.  The action is **free** (it is free on the `E`
factor), so

  `X := (E × C)/G`

is a smooth projective surface and `f : X ⟶ C/G = P¹_y` is proper; `X` is integral and
`P¹_y` is a smooth curve, so `f` is **flat**.

`h⁰(𝒪)` JUMPS at `y = ∞`.  For `y = a ≠ ∞` the equation `x² + x = a` is separable, so its
fibre in `C` is two points swapped by `σ` and `f⁻¹(a) ≅ E`, with `h⁰(𝒪) = 1`.  At `y = ∞`
put `u = 1/x`; then `σ(u) = u/(1 + u)` and the base parameter is
`s = 1/y = 1/(x² + x) = u²·(1 + u)⁻¹`, a unit times `u²`.  So the scheme-theoretic fibre of
`C ⟶ C/G` over `∞` is `Spec k[u]/(u²)`, and on it

  `σ(u) = u/(1+u) = u + u² + … ≡ u  (mod u²)` — **`σ` acts trivially**.

Since `G` acts freely, `E × Spec k[u]/(u²) ⟶ F := f⁻¹(∞)` is a `G`-torsor and
`Γ(F, 𝒪_F) = (Γ(E, 𝒪_E) ⊗_k k[u]/(u²))^G = (k[u]/(u²))^G = k[u]/(u²)`, of dimension **2**.
So `F = 2E'` with `E' = E/⟨τ⟩` is a multiple fibre with `h⁰(𝒪_F) = 2 > 1`: it is wild, and
equivalently its normal bundle `𝒪_X(-E')|_{E'} ≅ I/I² = (u)/(u²)` is **trivial** (the
`G`-linearisation on `(u)/(u²)` is trivial), of order `1 < m = 2`.  (`χ(𝒪_F) = 0` as it must
be, with `h¹(𝒪_F) = 2`.)

Now take `R₀ = k[t]` with `t = 1/y`, a **PID**, and `X₀ = f⁻¹(Spec k[t]) ⟶ Spec R₀`: proper,
flat, and finitely presented (finite type over noetherian).  `f_*𝒪_X = 𝒪_{P¹}` (Stein
factorization: `X` is normal with connected fibres), so `H⁰(K) = k[t]` is free of rank `1`,
and the universal-coefficient sequence at `N = k[t]/(t) = k` reads
`2 = h⁰(𝒪_F) = dim(H⁰(K) ⊗ k) + dim Tor₁(M, k) = 1 + dim Tor₁(M, k)` where
`M := H¹(X₀, 𝒪_{X₀})`.  Hence **`M` has nonzero `t`-torsion**, which is exactly the class
the reduction asked for.

*Step 3 — the non-noetherian base.*  Set

  `R := k[t, x₁, x₂, …]/(t·x₁, t·x₂, …)`,

whose `k`-basis is `{tⁿ}_{n ≥ 0} ∪ {x-monomials of positive degree}`; write `m` for the span
of the latter, an ideal.  `M` is finitely generated over the PID `R₀`, so
`M ≅ R₀ʳ ⊕ ⨁ⱼ R₀/(dⱼ)` and `Tor₁^{R₀}(M, R) ≅ ⨁ⱼ ann_R(dⱼ)` **as `R`-modules**.  One `dⱼ` is
divisible by `t`, say `dⱼ = tᵉ·g` with `e ≥ 1` and `g(0) ≠ 0`; in `R`, `tᵉg` kills `m`
(because `t·m = 0` and `g` acts on `m` as the nonzero scalar `g(0)`) and is a nonzerodivisor
on `k[t] ⊂ R`, so `ann_R(dⱼ) = m` exactly.  And `m` is **not** a finitely generated ideal:
`m/m²` is killed by `t` and by every `xᵢ`, hence is a `k`-vector space, and it has the
infinite basis `{x₁, x₂, …}`, so no finite set generates it.

Therefore `Tor₁^{R₀}(M, R)` has `m` as a direct summand and is not a finite `R`-module, so
`Γ(X, 𝒪_X)` is not a finite `R`-module either.  But `f` is proper, hence universally closed,
so `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` makes `Γ(S, ⊤) ⟶ Γ(X, ⊤)`
**integral**; integral + finite type would force finite.  **So `f.appTop.hom.FiniteType` is
FALSE for this `f`, with `S = Spec R` affine and `f` proper, flat and of finite
presentation.**  ∎

*Step 4 — why `h` repairs it, and why the repaired leaf is not vacuous or circular.*  In the
counterexample `Γ(F, 𝒪_F) = k[u]/(u²) ≇ k`, so `h` fails at the wild fibre — as it must.
Conversely `h` says `κ(s) ≅ Γ(X_s, 𝒪)` for every `s`, and since `X_s` is proper this survives
any field extension of `κ(s)` by flat base change; so every geometric fibre is connected and
reduced, and `𝒪_S ⟶ f_*𝒪_X` is an isomorphism for `f` proper, flat and of finite
presentation over an **arbitrary** base.  That is **Stacks 0E0S**, verified verbatim on
2026-07-29: *"Let `f : X → Y` be a morphism of algebraic spaces.  Assume `f` is proper, flat,
and of finite presentation, and the geometric fibres of `f` are reduced and connected.  Then
`f_*𝒪_X = 𝒪_Y` and this holds after any base change."*  No noetherian hypothesis appears.
`FiniteType` is then immediate.  This is *not* circular: `h` plus
`A/𝔪A ≅ R/𝔪` yields `A = R` only through Nakayama, which needs the finiteness this leaf
supplies, so a proof of the repaired leaf must still run a genuine base-change argument.
It is also not vacuous — `f = 𝟙` and any `X = S ×_k Z` with `Γ(Z, 𝒪) = k` satisfy `h`.

**(B) CORRECTION — "limits / approximation of schemes are absent from the pin" is FALSE.**
Re-checked at pin `a3364faec4` on 2026-07-29.  `Mathlib/AlgebraicGeometry/
AffineTransitionLimit.lean` is a **1371-line development of EGA IV 8 / Stacks 01YT**:
inverse limits of schemes with affine transition maps, `Scheme.nonempty_of_isLimit`,
`Scheme.compactSpace_of_isLimit`, `Scheme.exists_isAffine_of_isLimit`,
`Scheme.exists_isOpenCover_and_isAffine`, `nonempty_isColimit_Γ_mapCocone` (`Γ` of a limit
is the colimit of the `Γ`s), and `Scheme.preservesColimit_yoneda`
(`Hom_S(lim Dᵢ, X) = colim Hom_S(Dᵢ, X)` for `X` locally of finite presentation over `S` —
EGA IV 8.14.2).  The claim that `SpreadingOut.lean` "spreads out stalk morphisms only" is
true of `SpreadingOut.lean` but was used to conclude that scheme-level approximation is
absent, and that conclusion is wrong.

What is genuinely absent is narrower and should be named as such: **object descent**, i.e.
EGA IV 8.8.2 / Stacks 01ZM — given `X` locally of finite presentation over `S = lim Sᵢ`,
produce an index `i` and `Xᵢ ⟶ Sᵢ` with `X ≅ Xᵢ ×_{Sᵢ} S` — together with **descent of the
properties** `IsProper` and `Flat` to a finite stage (EGA IV 8.10.5, 11.2.6).  Mathlib has
the morphism half and not the object half.  So the noetherian reduction is a much smaller
build than the earlier note implies, and it sits on top of substantial existing machinery.

**(C) NEGATIVE RESULT — the "flat base change to the generic fibre" shortcut cannot prove
the consumer, and should not be attempted as stated.**  The proposal was: over a normal
noetherian domain base, `A ⊗_R Frac R ≅ Γ(X_η) = Frac R` by flat base change and `h` at the
generic point; `A` is `R`-torsion-free because it embeds by the sheaf axiom in `∏ᵢ Γ(X, Uᵢ)`
and each factor is `R`-flat; `A` is integral over `R`; hence `A ↪ Frac R` with image integral
over the normal `R`, so `A = R` — bypassing *both* open leaves in this file.  The
mathematics of that argument is correct as far as it goes.

It nevertheless does not discharge what this file must prove, because
`hasUniversallyTrivialPushforward_of_isProper_of_flat` establishes
`hasTrivialPushforwardProperty.universally f`, which quantifies over **every** pullback
square — the base `S'` of the base-changed morphism is an arbitrary scheme, not one inherited
from the top-level call site.  So even though the outermost consumers instantiate the base at
`Spec ℚ` (`Fermat/FLT/ModularCurve/EllipticScheme.lean` around line 9756 and
`Fermat/FLT/ModularCurve/X0.lean` around line 28036), normality of `R` is not available where
the work happens.  Making the shortcut usable would mean weakening
`HasUniversallyTrivialPushforward` to quantify only over base changes along morphisms from
normal (or smooth-over-`ℚ`) schemes and re-checking every use in the rigidity lemma — an
architectural change with a real chance of success, since the base changes the rigidity proof
performs are to products of smooth `ℚ`-schemes, but not one to make from inside this leaf.

**(D) NEGATIVE RESULT (2026-07-30) — THIS LEAF CANNOT BE CLOSED BY INVERTING THE FILE'S OWN
CHAIN.  Integrality plus fibrewise triviality is STRICTLY WEAKER than finiteness, and there
is an explicit counterexample.**  Record this before attempting the obvious shortcut, which
is the first thing the surrounding architecture suggests.

*The shortcut.*  Two facts here do **not** depend on this leaf:
`isIntegral_appTop_of_universallyClosed` makes `φ : R = Γ(S,⊤) ⟶ A = Γ(X,⊤)` integral, and
`h` is fibrewise data.  Downstream, `bijective_quotientMap_appTop_of_isIso_appTop_fiber`
gives `R/𝔪 ≅ A/𝔪A`, i.e. `A = R·1 + 𝔪A`, for every maximal `𝔪`.  So one is tempted to run
the assembly backwards — derive `A = R·1` from *integrality + `A = R·1 + 𝔪A` at every
maximal `𝔪`* — which would give `FiniteType` for free (a surjection is generated by `∅`) and
make `module_finite_appTop_of_isProper`, leaf 2 and the Nakayama block all unnecessary.

*It is false as a statement of commutative algebra.*  Take `R = ℤ_p` and

  `A = ℤ_p ⋉ ℚ_p = ℤ_p ⊕ ℚ_p·x`,  `x² = 0`,

the square-zero extension: `(a, q)(a', q') = (aa', aq' + a'q)`.  Then

* `A` is a commutative `R`-algebra and `R ⟶ A` is injective;
* `A` is **integral** over `ℤ_p`: `((a,q) - (a,0))² = (0,q)² = 0`, so `(a,q)` is a root of the
  monic `T² - 2aT + a² ∈ ℤ_p[T]`.  Every element is integral of degree `≤ 2`;
* `𝔪 = pℤ_p` is the only maximal ideal, and `𝔪A = pℤ_p ⊕ ℚ_p·x` because `p·ℚ_p = ℚ_p`.
  Hence `R·1 + 𝔪A = ℤ_p ⊕ ℚ_p·x = A`, and `R/𝔪 ⟶ A/𝔪A` is the **isomorphism** `𝔽_p ≅ 𝔽_p`;
* yet `A ≠ R·1`.

So every ring-theoretic hypothesis the shortcut wants is satisfied and the conclusion fails.
`Module.Finite` is doing irreplaceable work in
`bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap`, and no re-ordering of this
file avoids the leaf.  The same example kills the `𝔪`-adic iteration one tries next:
`A = R + 𝔪A` iterated gives `A = R + 𝔪ⁿA` for every `n`, so `a ∈ ⋂ₙ (R + 𝔪ⁿA)`, but here
`⋂ₙ 𝔪ⁿA = ℚ_p·x ≠ 0` and the intersection is all of `A`.  A Krull-intersection argument needs
`A` to be `𝔪`-adically separated, which is exactly the finiteness being sought.

*The POSITIVE by-product, and the smallest statement so far known to imply this leaf.*  The
geometric refinement of the shortcut does not collapse, and it locates the residual difficulty
at one point.  Fix `a ∈ A`.  Then `B := R[a] ⊆ A` is a **finite** `R`-algebra (integrality),
so `Spec B ⟶ S` is finite and `a` induces `g : X ⟶ Spec B` over `S` by the `Γ`-`Spec`
adjunction.  Three steps, each elementary:

1. `g` is **proper** (`f` proper, `Spec B ⟶ S` separated) and `ker (B ⟶ A) = 0`, so the
   scheme-theoretic image of `g` is all of `Spec B`; a proper morphism has closed set-image,
   so `g` is **surjective**.
2. Fix `s ∈ S`.  Surjectivity is stable under base change and `X_s = X ×_{Spec B} (Spec B)_s`,
   so `X_s ⟶ Spec (B ⊗_R κ(s))` is surjective; it factors through
   `Spec Γ(X_s, 𝒪_{X_s}) = Spec κ(s)` by `h s`.  Hence `B ⊗_R κ(s)` is a **local** `κ(s)`-algebra
   with residue field `κ(s)` and **nilpotent** maximal ideal `J` — equivalently
   `Spec B ⟶ S` is a finite universal homeomorphism.
3. If `J = 0` then `B = R·1 + 𝔪B` with `B` a **finite** `R`-module, so
   `eq_bot_of_fg_of_le_smul_of_forall_isMaximal` (above, and it needs only finite generation
   of `B`, never of `A`) gives `B = R·1`, i.e. `a ∈ range φ`.  Ranging over `a`, `φ` is
   surjective and `FiniteType` follows.

So the whole leaf reduces to: **for every `a : Γ(X,⊤)` and every maximal `𝔪`, the degree-zero
comparison map `R[a] ⊗_R κ(𝔪) ⟶ Γ(X_𝔪, 𝒪)` is INJECTIVE.**  That is leaf 3's injectivity
statement (see the equivalent form in the docstring of
`surjective_quotientMap_appTop_of_isIso_appTop_fiber`) restricted to **finite** `R`-subalgebras
of `A`, and the restriction is the whole point: it is a statement about finite modules, so the
existing Nakayama toolkit in this file applies to it directly, and it is **not** circular —
nothing in steps 1–3 uses `Module.Finite ↥Γ(S,⊤) ↥Γ(X,⊤)`.

*Two warnings about that reduction.*  First, it is **not** equivalent to the abstract
`𝔪A ∩ R[a] ⊆ 𝔪·R[a]`, and must not be weakened to it: the counterexample above refutes the
abstract form (`a = x`, `B = ℤ_p ⊕ ℤ_p·x`, `𝔪A ∩ B = pℤ_p ⊕ ℤ_p·x ⊋ pℤ_p ⊕ pℤ_p·x = 𝔪B`), so
genuine input from `X` is needed and any proof that never mentions `X_𝔪` is wrong.  Second,
steps 1–3 are verified **on paper only**; in Lean each needs plumbing that is not yet here
(`Γ`-`Spec` adjunction for a map into an affine, properness of `X ⟶ Spec B`, the
scheme-theoretic image of a quasi-compact morphism into an affine, and the identification
`X ×_S (Spec B)_s = X_s`).  The Nakayama lemma step 3 needs is available where it is wanted —
`eq_bot_of_fg_of_le_smul_of_forall_isMaximal` sits *above* this leaf, applied to
`N = ⊤ : Submodule R (B ⧸ R·1)` — but note that anything borrowed from the fibrewise block
(`surjective_of_isIso_appTop_fiber` and below) sits *underneath* it, so realising steps 1–3
may mean moving declarations and not only writing a proof.

**THIS THEOREM IS NOW PROVEN over the single leaf
`adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` immediately below** (2026-07-30), by the
route (D2) records.  Audit blocks (A)–(D) are kept verbatim rather than moved: (A) is what
justifies the hypothesis `h` and must stay attached to the statement it repaired, and
(B)–(D) describe the geometry of *this* statement, which the cut did not change. -/
theorem finiteType_appTop_of_isProper (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    f.appTop.hom.FiniteType := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have halg : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) = f.appTop.hom :=
    RingHom.algebraMap_toAlgebra _
  have hint : f.appTop.hom.IsIntegral := isIntegral_appTop_of_universallyClosed f
  have hleaf := adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber f h
  -- `φ` is SURJECTIVE, which is more than `FiniteType`; only `FiniteType` is exported, so
  -- that the Nakayama assembly downstream is left exactly as it is.  See the leaf docstring.
  refine RingHom.FiniteType.of_surjective f.appTop.hom ?_
  intro a
  -- `B` is the subalgebra generated by `a` — FINITE, by integrality — and `P = R·1`.
  set B : Submodule ↥Γ(S, ⊤) ↥Γ(X, ⊤) := (Algebra.adjoin ↥Γ(S, ⊤) {a}).toSubmodule
  set P : Submodule ↥Γ(S, ⊤) ↥Γ(X, ⊤) := Submodule.span ↥Γ(S, ⊤) {(1 : ↥Γ(X, ⊤))}
  have haint : _root_.IsIntegral ↥Γ(S, ⊤) a := by
    have := hint a
    rwa [RingHom.IsIntegralElem, ← halg] at this
  have hBfg : B.FG := haint.fg_adjoin_singleton
  -- Nakayama over every maximal ideal, applied inside `Γ(X, ⊤) ⧸ P`: the leaf says the image
  -- of `B` there is killed by passing to `𝔪 •` it, and that image is finitely generated.
  have hbot : B.map P.mkQ = ⊥ := by
    refine eq_bot_of_fg_of_le_smul_of_forall_isMaximal (hBfg.map _) ?_
    intro m hm
    have hmap := Submodule.map_mono (f := P.mkQ) (hleaf a m hm)
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.mkQ_map_self, bot_sup_eq] at hmap
    exact hmap
  have hBP : B ≤ P := by
    have hcomap := Submodule.map_le_iff_le_comap.mp hbot.le
    rwa [Submodule.comap_bot, Submodule.ker_mkQ] at hcomap
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hBP (Algebra.subset_adjoin rfl))
  exact ⟨r, by rw [← halg, ← hr, Algebra.smul_def, mul_one]⟩

/-- **LEAF 1 — `Γ(X, ⊤)` IS A FINITE `Γ(S, ⊤)`-MODULE** — **PROVEN** (2026-07-28) over the
single leaf `finiteType_appTop_of_isProper` above, by
`finite = integral + finite type` (`RingHom.IsIntegral.to_finite`).

Over an affine base, `Γ(X, ⊤) = (f_*𝒪_X)(S)`, so this is coherence of the direct image of
`𝒪_X` along a proper morphism, in degree `0` (Grothendieck's finiteness theorem; EGA III
3.2.1, Stacks 02O5 / 0B91).

**What the pin already gives, and what it does not.**
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` applies verbatim here — properness
gives `UniversallyClosed f`, and `S` is affine — and yields that `φ = f.appTop` is
**integral**.  Since `RingHom.Finite` is exactly `RingHom.IsIntegral` together with
`RingHom.FiniteType` (`RingHom.finite_iff_isIntegral_and_finiteType`), the *entire* remaining
content of this leaf is finite-type-ness of `Γ(X, ⊤)` over `R`, which is what
`finiteType_appTop_of_isProper` isolates.  Mathlib's `finite_appTop_of_universallyClosed` is
not usable as a shortcut: it is stated over a *field* and under `[IsIntegral X]`.

**Why the residual leaf is not formal, and is not weaker than the theorem it came from.**
For non-affine `X`, `Γ(X, ⊤)` is the equalizer of a finite Čech diagram of finite-type
`R`-algebras, and an `R`-subalgebra of a finite-type `R`-algebra need not be of finite type
even when it is integral over `R` — Nagata's examples of a noetherian domain whose integral
closure in a finite field extension is not module-finite already show that integrality plus
an ambient finite-type algebra cannot suffice.  So properness has to be used again here, and
the cut merely *records* that the integral half is discharged; it does not make the geometry
disappear.

**The fibrewise hypothesis `h` (added 2026-07-29) is inherited from
`finiteType_appTop_of_isProper` and is NOT bookkeeping.**  Without it the statement is FALSE
over a non-noetherian base — see audit block (A) on that leaf for the char-`2` wild-fibre
witness.  All three call sites of this theorem already had `h` in scope. -/
theorem module_finite_appTop_of_isProper (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
  (isIntegral_appTop_of_universallyClosed f).to_finite (finiteType_appTop_of_isProper f h)

/-! #### Surjectivity of `f`, and the two consequences of it that replace III.12.11(b)

The three lemmas in this block are what let leaf 2 (`f_*𝒪_X` flat over the base) be
DISCHARGED rather than proven as a second instance of cohomology and base change; see the
docstring of `module_flat_appTop_of_isIso_appTop_fiber` below for why that is legitimate and
what it cost.  All three are elementary — no higher direct images appear. -/

/-- **THE FIBREWISE HYPOTHESIS MAKES `f` SURJECTIVE** (PROVEN).

If `s ∉ range f` then the scheme-theoretic fibre `X_s` is EMPTY (its inclusion
`f.fiberι s` has range `f ⁻¹' {s} = ∅`), so `Γ(X_s, ⊤)` is the zero ring; but `h s` makes it
isomorphic to `Γ(Spec κ(s), ⊤) ≅ κ(s)`, and a field is not a zero ring.

This is the same argument as `surjective_of_hasUniversallyTrivialPushforward` below, run at
the fibre rather than at a general base change, and stated here because it is needed
upstream of it. -/
theorem surjective_of_isIso_appTop_fiber (f : X ⟶ S)
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) : Surjective f := by
  constructor
  intro s
  by_contra hs
  have hrange : Set.range (f.fiberι s) = ∅ := by
    rw [Scheme.Hom.range_fiberι]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hs ⟨x, ?_⟩
    simpa using hx
  haveI : IsEmpty ↥(f.fiber s) := Set.range_eq_empty_iff.mp hrange
  haveI := h s
  haveI : Subsingleton Γ(f.fiber s, ⊤) := by
    have htop : (⊤ : (f.fiber s).Opens) = ⊥ := by
      ext x
      exact (IsEmpty.false x).elim
    rw [htop]
    infer_instance
  haveI : Subsingleton Γ(Spec (S.residueField s), ⊤) :=
    (asIso ((f.fiberToSpecResidueField s).appTop)).commRingCatIsoToRingEquiv.toEquiv
      |>.subsingleton_congr.mpr inferInstance
  haveI : Subsingleton ↥(S.residueField s) :=
    (Scheme.ΓSpecIso (S.residueField s)).commRingCatIsoToRingEquiv.toEquiv
      |>.subsingleton_congr.mp inferInstance
  exact false_of_nontrivial_of_subsingleton ↥(S.residueField s)

/-- **A FLAT SURJECTIVE MORPHISM HAS `Γ(S, ⊤) ⟶ Γ(X, ⊤)` INJECTIVE** (PROVEN) — faithfully
flat descent, read on stalks.  No properness, no finiteness, no affineness.

For each `x : X` the stalk map `𝒪_{S, f x} ⟶ 𝒪_{X, x}` is a FLAT LOCAL homomorphism of local
rings (`AlgebraicGeometry.Flat.stalkMap`), hence FAITHFULLY flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), hence injective.  Surjectivity of `f` makes
every point of `S` of the form `f x`, so a global section of `𝒪_S` killed by `f.appTop` has
vanishing germ at *every* point of `S`, and the sheaf axiom (`TopCat.Presheaf.section_ext`)
makes it zero.

This is the ingredient that lets `module_flat_appTop_of_isIso_appTop_fiber` be proven from
the surjectivity half of `bijective_quotientMap_appTop_of_isIso_appTop_fiber` alone: the
classical route obtains injectivity of `φ` FROM flatness of `A` over `R`, and this obtains it
from flatness of `f` directly, which is a hypothesis rather than a theorem.

Mathlib proves `AlgebraicGeometry.Flat.epi_of_flat_of_surjective` by exactly this stalkwise
argument; only the conclusion differs, so the two-line core is lifted from there. -/
theorem injective_appTop_of_flat_of_surjective (f : X ⟶ S) [Flat f] [Surjective f] :
    Function.Injective f.appTop.hom := by
  intro a b hab
  refine TopCat.Presheaf.section_ext S.sheaf ⊤ a b fun s _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective s
  have hinj : Function.Injective (f.stalkMap x).hom := by
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  have key : ∀ c : ↥Γ(S, ⊤), (f.stalkMap x) (S.presheaf.germ ⊤ (f x) trivial c)
      = X.presheaf.germ (f ⁻¹ᵁ ⊤) x trivial (f.appTop c) :=
    fun c => Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial c
  show S.presheaf.germ ⊤ (f x) trivial a = S.presheaf.germ ⊤ (f x) trivial b
  refine hinj ?_
  rw [key, key]
  exact congrArg _ hab

/-- **`Spec Γ(X, ⊤) ⟶ Spec Γ(S, ⊤)` IS SURJECTIVE WHEN `f` IS AND `S` IS AFFINE** (PROVEN).

`Scheme.toSpecΓ_naturality` factors `f ≫ S.toSpecΓ` as `X.toSpecΓ ≫ Spec.map f.appTop`.  For
affine `S` the map `S.toSpecΓ` is an isomorphism, so the left-hand side is surjective, and a
composite is surjective only if its second factor is (`Surjective.of_comp`).

Read ideal-theoretically this says every prime of `Γ(S, ⊤)` is contracted from a prime of
`Γ(X, ⊤)` — the "lying over" statement that makes `𝔪 ↦ 𝔪A` lose no information. -/
theorem surjective_comap_appTop_of_isAffine (f : X ⟶ S) [IsAffine S] [Surjective f] :
    Function.Surjective (PrimeSpectrum.comap f.appTop.hom) := by
  haveI : Surjective (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  haveI : Surjective (Spec.map f.appTop) :=
    Surjective.of_comp X.toSpecΓ (Spec.map f.appTop)
  exact (surjective_iff (Spec.map f.appTop)).mp inferInstance

/-- **`𝔭` IS RECOVERED FROM `𝔭A`** (PROVEN): for every prime `𝔭 ⊂ R = Γ(S, ⊤)`,
`φ⁻¹(𝔭 · A) = 𝔭`, where `A = Γ(X, ⊤)` and `φ = f.appTop`.

Lying over: `surjective_comap_appTop_of_isAffine` produces a prime `q ⊂ A` with `φ⁻¹ q = 𝔭`;
then `𝔭A ≤ q`, so `φ⁻¹(𝔭A) ≤ φ⁻¹ q = 𝔭`, and the reverse inclusion is `Ideal.le_comap_map`.

This is the INJECTIVE half of `bijective_quotientMap_appTop_of_isIso_appTop_fiber`, and it
needs neither properness, flatness, finite presentation nor maximality of `𝔭` — only that
the fibrewise hypothesis forces `f` to be surjective. -/
theorem comap_map_appTop_eq_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop)
    (m : Ideal ↥Γ(S, ⊤)) (hm : m.IsPrime) :
    Ideal.comap f.appTop.hom (Ideal.map f.appTop.hom m) = m := by
  haveI := surjective_of_isIso_appTop_fiber f h
  refine le_antisymm ?_ Ideal.le_comap_map
  obtain ⟨q, hq⟩ := surjective_comap_appTop_of_isAffine f ⟨m, hm⟩
  have hqm : Ideal.comap f.appTop.hom q.asIdeal = m := congrArg PrimeSpectrum.asIdeal hq
  calc Ideal.comap f.appTop.hom (Ideal.map f.appTop.hom m)
      ≤ Ideal.comap f.appTop.hom q.asIdeal :=
        Ideal.comap_mono (Ideal.map_le_iff_le_comap.mpr (hqm ▸ le_rfl))
    _ = m := hqm

/-! #### The degree-zero base-change cut

Everything in this block serves one statement, `rank_quotient_appTop_le_one_of_isIso_appTop_fiber`
at its end: **`dim_{R/𝔪} A/𝔪A ≤ 1`**.  That is Hartshorne III.12.11(a) in degree `0`
(EGA III 7.8.6) and it is **the whole of cohomology and base change left in this file** —
everything the surjectivity statement after it adds is linear algebra over the field `R/𝔪`.

This introduction states the problem and records what does not work; the cut into two leaves
plus a proven bridge follows it.

**What it says.**  With `R = Γ(S, ⊤)`, `A = Γ(X, ⊤)` and `φ = f.appTop`, the ring
`A/𝔪A = A ⊗_R κ(s)` — `s ∈ S` being the point cut out by the maximal ideal `𝔪`, so that
`κ(s) = R/𝔪` — has dimension at most one as an `R/𝔪`-vector space.  Equivalently, and this
is the form to attack, the degree-zero comparison map

  `A ⊗_R κ(s)  =  A/𝔪A  ⟶  H⁰(X_s, 𝒪_{X_s})  =  Γ(f.fiber s, ⊤)`

is **INJECTIVE**: the target is the field `κ(s)` by the hypothesis `h s`, so injectivity and
`dim ≤ 1` are the same statement.  (That the comparison map is *surjective* is what `h s`
gives for free: the composite `κ(s) = R/𝔪 ⟶ A/𝔪A ⟶ Γ(X_s, ⊤)` is
`(f.fiberToSpecResidueField s).appTop` by `Scheme.Hom.fiber_fac` applied to global sections,
and `h s` says that composite is an isomorphism.)

The rank formulation is used rather than the map formulation because it keeps the *assembly*
free of the point ↔ prime dictionary: the consumer below needs only `rank ≤ 1` together with
the injection `R/𝔪 ↪ A/𝔪A` already proven in
`comap_map_appTop_eq_of_isIso_appTop_fiber`.  A prover of this leaf will have to set up
`κ(s) ≅ R/𝔪` for maximal `𝔪` (`Scheme.map_PrimeSpectrum_basicOpen_of_affine` and
`Scheme.evaluation_eq_zero_iff_notMem_basicOpen` identify
`RingHom.ker (S.Γevaluation s)` with `𝔪` for `s = S.isoSpec.inv ⟨𝔪, _⟩`); that bookkeeping
belongs here, not in the assembly.

**THE REAL OBSTRUCTION, and it is not point-set.**  `H⁰` is a KERNEL
(`Γ(X, 𝒪) = ker(∏ Γ(U_i) ⇉ ∏ Γ(U_{ij}))`) and `κ(s)` is *not* a flat `R`-module, so
`ker(M ⇉ N) ⊗ κ(s) ⟶ ker(M ⊗ κ(s) ⇉ N ⊗ κ(s))` need not be injective; the failure is
measured by a `Tor₁`.  Killing it is exactly III.12.11(a) — flatness of `f` plus the
constancy of `h⁰` supplied by `h`.

**What is NOT enough** (checked twice, so that the next owner does not repeat it): `f`
surjective gives `A/𝔪A ≠ 0`; `Γ(X, 𝒪) = A` makes `X ⟶ Spec A` surjective, hence
`Spec(A/𝔪A)` connected, hence — with `Module.Finite R A` — `A/𝔪A` local artinian with
residue field `κ(s)`.  So `A/𝔪A = κ(s) ⊕ 𝔫` with `𝔫` nilpotent and the leaf is exactly
`𝔫 = 0`.  Nilpotents are invisible to the topology and the fibre may itself be non-reduced
(a ribbon on `ℙ¹` has `H⁰ = k`), so `𝔫 = 0` follows from no point-set argument.  Nor does
any of the following work, each of which was tried and is recorded so it is not tried again:
**THE VERDICT OF THE NEXT THREE BULLETS IS SUPERSEDED (2026-07-29).**  They are correct
about the three routes they describe and were read — including by this docstring's own
summary — as saying that no elementary argument exists.  That reading is FALSE: localising
WITHOUT completing, and inducting on `dim R`, closes the leaf over a noetherian base with no
higher cohomology, no Grothendieck complex and no theorem on formal functions.  The route is
written out on `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` below.  In particular
the first bullet's "what is missing is … the THEOREM ON FORMAL FUNCTIONS" is a fact about
the completion route only; the induction below never forms `lim_n Γ(X_n, 𝒪)`.
* *Localize and complete.*  `R ⟶ R_𝔪` and `R ⟶ \hat R_𝔪` are FLAT, so
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` transports `A` along them and one
  may assume `R` complete local noetherian.  Over such an `R` one gets, by induction on `n`
  using flatness of `f` and a length count, `Γ(X ×_R R/𝔪ⁿ⁺¹, 𝒪) = R/𝔪ⁿ⁺¹` — i.e. base change
  over ARTINIAN quotients is elementary.  What is missing is the comparison of `\hat A` with
  `lim_n Γ(X_n, 𝒪)`, which is the THEOREM ON FORMAL FUNCTIONS; in degree `0` it amounts to
  the Artin–Rees statement that `{Γ(X, 𝔪ⁿ𝒪_X)}` and `{𝔪ⁿ A}` are cofinal, and that is not
  elementary.
* *Reduce to the generic fibre.*  For `R` REDUCED the leaf does follow at the minimal primes
  (`R ⟶ κ(𝔭)` is flat there, so flat base change applies), but `Supp(A/R)` can avoid every
  minimal prime while being nonempty, so this proves nothing at a maximal ideal.  It is also
  the Grauert route, which this file deliberately avoids: the bases fed in here are
  arbitrary and are not assumed reduced.
* *Stein factorization / ZMT.*  `X ⟶ Spec A` is proper and surjective with connected fibres,
  and `Spec(A ⊗ κ(s))` is a single point either way, so it gives no new information.

**PIN RE-CHECK, 2026-07-28, in MATHLIB's vocabulary rather than this project's.**  The
absence claim above is not inherited; it was re-run against `Mathlib/` and `~/cs/FLT/`.
**TWO CLAUSES OF THE 2026-07-28 RE-CHECK WERE FALSE ABSENCES and are corrected here
(2026-07-28, second pass); both were greps that missed by SPELLING or by DIRECTORY, which is
the standard failure mode.  The operative conclusion — no coherence, no `Rⁱf_*`, no base
change — nevertheless STANDS, and was re-verified.**
* ~~`QuasiCoherent` has zero occurrences anywhere under `Mathlib/AlgebraicGeometry/`, so
  there are no quasi-coherent sheaves.~~  **FALSE.**  The capital-`C` grep is what returns
  zero: `Mathlib` spells it **`Quasicoherent`**, and quasi-coherent sheaves DO exist —
  `SheafOfModules.IsQuasicoherent` in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` (51 occurrences), used in
  `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` (30 occurrences), which builds `tilde M`,
  the adjunction `tilde ⊣ Γ` on an affine, `instance : (tilde M).IsQuasicoherent`, and
  stability of quasi-coherence under pushforward along an affine map and under restriction to
  an open.  What is genuinely absent is everything DERIVED: no `Rⁱf_*`, no coherence, no
  finiteness, no base change.  `higherDirectImage` and `directImage` still have zero hits
  anywhere in `Mathlib/`, and `IsCoherent` occurs only in topology and in
  `CategoryTheory/Sites/Coherent` (a Grothendieck topology, unrelated).
* Sheaf cohomology exists only ABSTRACTLY and only on sites:
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` defines `H F n` as an `Ext` in
  the category of `AddCommGrpCat`-valued sheaves, with `H.equiv₀ : H F 0 ≃+ F(T)`.  There is
  no finiteness and no base change, and it is not connected to
  `AlgebraicGeometry.Scheme.Modules`.
* ~~There is no Čech complex.~~  **FALSE.**
  `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean` (with a
  `MayerVietoris.lean` beside it) defines `CategoryTheory.cechComplexFunctor`, the Čech
  cochain complex of a presheaf for a family `U : ι → C` in a category with finite products.
  It is three definitions and no theorems: there is still **no Čech-to-derived comparison**,
  so it computes nothing on its own — but a prover building the degree-`0` Čech complex below
  should start from it rather than roll their own.
* `Scheme.Modules` DOES exist now (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`) with
  `pushforward`, `pullback` and their adjunction — degree zero only, nothing derived.  This
  is new since the paragraph at the head of this file was written and is the right place to
  hang a future development.
* `Tor` exists only as the abstract monoidal derived functor
  (`Mathlib/CategoryTheory/Monoidal/Tor.lean`), related to flatness in
  `Mathlib/RingTheory/Flat/CategoryTheory.lean`.
* `~/cs/FLT` has nothing: its `FLT/Mathlib/AlgebraicGeometry/` contains only `EllipticCurve`.
So the claim STANDS, and the route below is a theory build rather than a missing-lemma hunt.

**THE CHOSEN ROUTE — Čech in degree `0`, which needs NO sheaf cohomology.**  This is the
cheapest honest cut and it is where the next owner should start.  Two further leaves, one
geometric and one pure commutative algebra:

1. *(geometric)* **A two-term FINITE FREE presentation of `H⁰` compatible with base change.*
   There are `n₀ n₁ : ℕ` and a matrix `d : Matrix (Fin n₁) (Fin n₀) R` with `R`-linear
   isomorphisms `Γ(X, ⊤) ≃ₗ ker d.mulVecLin` and, for every `s : S`,
   `Γ(f.fiber s, ⊤) ≃ₗ ker (d.map (algebraMap R κ(s))).mulVecLin`, compatibly with the
   comparison map (the square with `Γ(X,⊤) ⊗ κ(s) ⟶ Γ(X_s,⊤)` on top commutes).
   Classically: take a finite affine cover `𝔘` of `X` (`f` proper ⟹ `X` quasi-compact and
   separated over affine `S`, so all `U_{i₀…i_p}` are affine), let `C^p` be the Čech complex
   — its terms are FLAT `R`-modules because `f` is flat, and it commutes with base change
   term by term because `Γ(U ×_S Spec R') = Γ(U) ⊗_R R'`.  The sheaf axiom gives
   `Γ(X_{R'}, 𝒪) = ker(C⁰ ⊗ R' → C¹ ⊗ R')` in degree `0` alone, so no cohomology theory is
   needed for the IDENTIFICATION.  Replacing `C^•` by a bounded complex of finite free
   modules is Grothendieck's complex, and that step *does* use finiteness of `Hⁱ(X, 𝒪)` in
   all degrees.
2. *(commutative algebra, stateable and provable now)* with `R` noetherian, `M N` flat
   `R`-modules, `N` finite, `d : M →ₗ[R] N`, if for every maximal `𝔪` the map
   `(LinearMap.range d) ⊗ R/𝔪 ⟶ N ⊗ R/𝔪` is injective, then `Module.Flat R (range d)`.
   Because: `N/range d` is finitely presented with `Tor₁(N/range d, R/𝔪) = 0` at every
   maximal ideal, hence flat by the local criterion, hence `range d` is flat as the kernel of
   a surjection of flat modules onto a flat module.  Then `0 ⟶ ker d ⟶ M ⟶ range d ⟶ 0` is
   universally exact and `ker d ⊗ κ(s) ⟶ M ⊗ κ(s)` is injective — which IS the leaf.
   The hypothesis of 2 is supplied by `h`: `h s` makes the comparison map SURJECTIVE, and
   the cokernel of `ker d ⊗ κ ⟶ ker(d ⊗ κ)` is exactly `Tor₁(N/range d, κ)`.
   Useful pin material for this step: `Module.Flat.ker_lTensor_eq`
   (`Mathlib/RingTheory/Flat/Equalizer.lean` — flat base change commutes with kernels),
   `Module.free_of_flat_of_isLocalRing`, and `Mathlib/RingTheory/Flat/LocallyFree.lean`.

**FAITHFULNESS.**  `h` cannot be dropped: without it `h⁰` jumps and `A/𝔪A` is strictly
bigger than `κ(s)` where it does — the conclusion is then literally false, not merely
unprovable.  `[Flat f]` cannot be dropped either; it is the hypothesis of III.12.11 and it is
what makes the Čech terms flat in step 1.  Maximality of `𝔪` is genuinely used: it is what
makes `κ(s) = R/𝔪`, so that `dim_{R/𝔪}` is the right thing to bound; at a non-maximal prime
the analogous statement is about `A ⊗ κ(𝔭)`, not about `A/𝔭A` over `R/𝔭`.  The conclusion is
`≤ 1` rather than `= 1` because non-vanishing is available separately and more cheaply, from
lying over.

**CUT, 2026-07-28 — this declaration is now PROVEN**, over the two leaves stated immediately
below (`inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le`, pure commutative algebra, and
`exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber`, the geometry) and the
proven bridge `rank_quotient_le_one_of_fibre_span` between them.  The two paragraphs above
describing that cut are what got carried out; read them as the plan and the declarations
below as its realisation. -/

/-- Over a field, a linear map out of a finite-dimensional space admits a finite family of
vectors whose images form a basis of its range.  This is the only place linear algebra over
the residue field is used in `free_of_isLocalRing_of_comap_smul_le`, and it is stated
separately because keeping the field abstract is what stops `whnf` from unfolding
`IsLocalRing.ResidueField R = R ⧸ maximalIdeal R` during instance search. -/
theorem exists_linearIndependent_image_of_field
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] (T : V →ₗ[k] W) :
    ∃ (m : ℕ) (v : Fin m → V), LinearIndependent k (fun i => T (v i)) ∧
      LinearMap.range T ≤ Submodule.span k (Set.range fun i => T (v i)) := by
  classical
  haveI : Module.Free k (LinearMap.range T) := Module.Free.of_divisionRing k (LinearMap.range T)
  set m := Module.finrank k (LinearMap.range T) with hm
  set bb : Module.Basis (Fin m) k (LinearMap.range T) :=
    Module.finBasis k (LinearMap.range T) with hbb
  choose v hv using fun i : Fin m => (bb i).2
  have hcomp : (fun i => T (v i)) = (LinearMap.range T).subtype ∘ (bb : Fin m → _) := by
    funext i; rw [hv i]; rfl
  refine ⟨m, v, ?_, ?_⟩
  · rw [hcomp]
    exact bb.linearIndependent.map' _ (Submodule.ker_subtype _)
  · rw [hcomp, Set.range_comp, ← Submodule.map_span, bb.span_eq, Submodule.map_top,
      Submodule.range_subtype]

open TensorProduct in
/-- The base change of `Finsupp.linearCombination R w` along `R ⟶ A` is injective as soon as the
base-changed family `1 ⊗ w i` is `A`-linearly independent. -/
theorem injective_lTensor_linearCombination
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module R N] {m : ℕ} (w : Fin m → N)
    (hw : LinearIndependent A (fun i => (1 : A) ⊗ₜ[R] w i)) :
    Function.Injective ((Finsupp.linearCombination R w).lTensor A) := by
  classical
  set bb : Module.Basis (Fin m) A (A ⊗[R] (Fin m →₀ R)) :=
    (Finsupp.basisSingleOne).baseChange A with hbb
  have key : ((Finsupp.linearCombination R w).baseChange A) =
      (Finsupp.linearCombination A (fun i => (1 : A) ⊗ₜ[R] w i)) ∘ₗ bb.repr.toLinearMap := by
    refine bb.ext fun i => ?_
    have h1 : bb i = (1 : A) ⊗ₜ[R] (Finsupp.single i (1 : R)) := by
      rw [hbb, Module.Basis.baseChange_apply]
      simp
    have h2 : bb.repr (bb i) = Finsupp.single i (1 : A) := Module.Basis.repr_self bb i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Finsupp.linearCombination_single,
      one_smul]
    rw [h1, LinearMap.baseChange_tmul]
    simp
  have hinj : Function.Injective ((Finsupp.linearCombination R w).baseChange A) := by
    rw [key]
    exact hw.finsuppLinearCombination_injective.comp bb.repr.injective
  rwa [LinearMap.baseChange_eq_ltensor] at hinj

set_option maxHeartbeats 1000000 in
open IsLocalRing TensorProduct in
/-- **THE LOCAL HALF of `inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le`** (PROVEN,
2026-07-28).  Over a LOCAL ring `(R, 𝔪, k)`, if `F₀ ⟶ F₁ ⟶ P ⟶ 0` is exact with `F₀` finite
and `F₁` finite free, and if `d⁻¹(𝔪F₁) ≤ K + 𝔪F₀` for some `K ≤ ker d`, then `P` is FREE.

**The proof, and why it needs no Tor.**  Choose `e i : F₀` whose images `d(e i)` reduce to a
`k`-basis of `range (d ⊗ k)`.  The hypothesis says exactly that `ker (d ⊗ k)` is hit by
`K ⊗ k`, so `F₀ = span{e i} + K + 𝔪F₀`, and Nakayama (`F₀` finite, `𝔪 ≤ jacobson ⊥`) upgrades
this to `F₀ = span{e i} + ker d`.  Hence `range d = span{d (e i)}` is the range of
`φ : Rⁿ ⟶ F₁`, `φ` has `k ⊗ φ` injective by construction, and mathlib's
`Module.free_of_lTensor_residueField_injective` applied to `Rⁿ ⟶ F₁ ⟶ P ⟶ 0` gives `P` free.

`K` is a parameter rather than `ker d` itself because the caller feeds in the LOCALIZATION of
a kernel, which is contained in — and in fact equal to, though that is not needed — the kernel
of the localized map. -/
theorem free_of_isLocalRing_of_comap_smul_le
    {R F₀ F₁ P : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup F₀] [Module R F₀] [Module.Finite R F₀]
    [AddCommGroup F₁] [Module R F₁] [Module.Finite R F₁] [Module.Free R F₁]
    [AddCommGroup P] [Module R P]
    (d : F₀ →ₗ[R] F₁) (g : F₁ →ₗ[R] P) (hg : Function.Surjective g)
    (hex : Function.Exact d g)
    (K : Submodule R F₀) (hK : K ≤ LinearMap.ker d)
    (h : Submodule.comap d (maximalIdeal R • (⊤ : Submodule R F₁)) ≤
      K ⊔ maximalIdeal R • (⊤ : Submodule R F₀)) :
    Module.Free R P := by
  classical
  obtain ⟨m, v, hvli, hvsp⟩ :=
    exists_linearIndependent_image_of_field (d.baseChange (ResidueField R))
  choose e he using fun i : Fin m => TensorProduct.mk_surjective R F₀ (ResidueField R)
    Ideal.Quotient.mk_surjective (v i)
  simp only [TensorProduct.mk_apply] at he
  have hDe : ∀ i : Fin m, (d.baseChange (ResidueField R)) (v i)
      = (1 : ResidueField R) ⊗ₜ[R] d (e i) := by
    intro i; rw [← he i, LinearMap.baseChange_tmul]
  set φ : (Fin m →₀ R) →ₗ[R] F₁ := Finsupp.linearCombination R (fun i => d (e i)) with hφ
  have hsm : ∀ (r : R) (z : F₀), (1 : ResidueField R) ⊗ₜ[R] (r • z) =
      (IsLocalRing.residue R r) • ((1 : ResidueField R) ⊗ₜ[R] z) := by
    intro r z
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  -- (1) `k ⊗ φ` is injective.
  have hφinj : Function.Injective (φ.lTensor (ResidueField R)) := by
    refine injective_lTensor_linearCombination (fun i => d (e i)) ?_
    have : (fun i => (1 : ResidueField R) ⊗ₜ[R] d (e i))
        = fun i => (d.baseChange (ResidueField R)) (v i) := by
      funext i; rw [hDe i]
    rw [this]
    exact hvli
  -- (2) Nakayama: `F₀ = span {e i} + ker d`.
  have hjac : maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
  have hspan : (⊤ : Submodule R F₀) ≤
      Submodule.span R (Set.range e) ⊔ LinearMap.ker d := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac ?_
    intro x _
    have hxW : (d.baseChange (ResidueField R)) ((1 : ResidueField R) ⊗ₜ[R] x)
        ∈ Submodule.span (ResidueField R)
          (Set.range fun i => (d.baseChange (ResidueField R)) (v i)) :=
      hvsp (LinearMap.mem_range_self _ _)
    rw [Submodule.mem_span_range_iff_exists_fun] at hxW
    obtain ⟨c, hc⟩ := hxW
    choose a ha using fun i : Fin m => IsLocalRing.residue_surjective (c i)
    have hsum : (d.baseChange (ResidueField R))
        ((1 : ResidueField R) ⊗ₜ[R] (∑ i, a i • e i))
        = (d.baseChange (ResidueField R)) ((1 : ResidueField R) ⊗ₜ[R] x) := by
      rw [TensorProduct.tmul_sum]
      simp only [map_sum]
      rw [Finset.sum_congr rfl (fun i _ =>
        show (d.baseChange (ResidueField R)) ((1 : ResidueField R) ⊗ₜ[R] (a i • e i))
            = c i • (d.baseChange (ResidueField R)) (v i) by
          rw [hsm, map_smul, ha i, ← he i])]
      exact hc
    have hdy : (1 : ResidueField R) ⊗ₜ[R] (d (x - ∑ i, a i • e i)) = 0 := by
      have hz : (d.baseChange (ResidueField R))
          ((1 : ResidueField R) ⊗ₜ[R] (x - ∑ i, a i • e i)) = 0 := by
        rw [TensorProduct.tmul_sub, map_sub, hsum, sub_self]
      rwa [LinearMap.baseChange_tmul] at hz
    have hmem : (x - ∑ i, a i • e i) ∈ Submodule.comap d
        (maximalIdeal R • (⊤ : Submodule R F₁)) := by
      rw [Submodule.mem_comap, ← LinearMap.ker_tensorProductMk (R := R) (Q := F₁)
        (I := maximalIdeal R)]
      exact hdy
    have hmem2 := h hmem
    have hxe : (∑ i, a i • e i) ∈ Submodule.span R (Set.range e) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, rfl⟩)
    have hfin : x = (∑ i, a i • e i) + (x - ∑ i, a i • e i) := by abel
    rw [hfin]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hxe)
    · rcases Submodule.mem_sup.mp hmem2 with ⟨u, hu, y, hy, huy⟩
      rw [← huy]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_right (hK hu)))
        (Submodule.mem_sup_right hy)
  -- (3) `range φ = range d`.
  have hrange : LinearMap.range φ = LinearMap.range d := by
    have h1 : LinearMap.range φ = Submodule.map d (Submodule.span R (Set.range e)) := by
      rw [hφ, Finsupp.range_linearCombination, Submodule.map_span, ← Set.range_comp]
      rfl
    have h2 : Submodule.map d (LinearMap.ker d) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      simpa using hz
    rw [h1]
    refine le_antisymm LinearMap.map_le_range ?_
    calc LinearMap.range d = Submodule.map d ⊤ := (Submodule.map_top d).symm
      _ ≤ Submodule.map d (Submodule.span R (Set.range e) ⊔ LinearMap.ker d) :=
          Submodule.map_mono hspan
      _ = Submodule.map d (Submodule.span R (Set.range e)) ⊔ Submodule.map d (LinearMap.ker d) :=
          Submodule.map_sup _ _ _
      _ = Submodule.map d (Submodule.span R (Set.range e)) := by rw [h2, sup_bot_eq]
  have hexφ : Function.Exact φ g := by
    rw [LinearMap.exact_iff] at hex ⊢
    rw [hrange]; exact hex
  exact Module.free_of_lTensor_residueField_injective φ g hg hexφ hφinj

/-- If `mk' f y s` lies in the localization of a submodule `N`, then some `t` in the localizing
submonoid pushes `y` itself into `N`. -/
theorem exists_smul_mem_of_mk'_mem_localized' {R : Type*} [CommRing R] (S : Submonoid R)
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A] [Module A M']
    [IsScalarTower R A M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (N : Submodule R M) (y : M) (s : S)
    (hy : IsLocalizedModule.mk' f y s ∈ N.localized' A S f) :
    ∃ t : S, (t : R) • y ∈ N := by
  obtain ⟨n, hn, u, hu⟩ := hy
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hu
  obtain ⟨w, hw⟩ := hu
  refine ⟨w * u, ?_⟩
  have hcalc : ((w * u : S) : R) • y = ((w * s : S) : R) • n := by
    simp only [Submonoid.coe_mul, mul_smul]
    exact hw
  rw [hcalc]
  exact N.smul_mem _ hn

/-- The localization at a maximal ideal `I` carries `I • ⊤` to `𝔪 • ⊤`. -/
theorem localized'_smul_top_eq {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal]
    {M : Type*} [AddCommGroup M] [Module R M] :
    (I • (⊤ : Submodule R M)).localized' (Localization.AtPrime I) I.primeCompl
        (LocalizedModule.mkLinearMap I.primeCompl M)
      = IsLocalRing.maximalIdeal (Localization.AtPrime I) •
        (⊤ : Submodule (Localization.AtPrime I) (LocalizedModule I.primeCompl M)) := by
  apply le_antisymm
  · rw [Submodule.localized'_eq_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine Submodule.smul_induction_on hy (fun r hr z _ => ?_) (fun z z' hz hz' => ?_)
    · rw [map_smul, ← IsScalarTower.algebraMap_smul (Localization.AtPrime I) r]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hr
    · rw [map_add]; exact Submodule.add_mem _ hz hz'
  · rw [Submodule.smul_le]
    intro a ha z _
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl a
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective I.primeCompl
      (LocalizedModule.mkLinearMap I.primeCompl M) z
    simp only [Function.uncurry_apply_pair] at ha ⊢
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime I) I] at ha
    rw [IsLocalizedModule.mk'_smul_mk']
    exact ⟨c • y, Submodule.smul_mem_smul ha Submodule.mem_top, s * t, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **LEAF 3a-CA — THE COMMUTATIVE ALGEBRA OF DEGREE-ZERO BASE CHANGE** — **PROVEN**
(2026-07-28).
Self-contained, no geometry, and stated entirely in `RingTheory` vocabulary: it could be
hoisted to a shim file or upstreamed unchanged.

For a map `d : R^{n₀} ⟶ R^{n₁}` of finite free modules, write `K = ker d`.  The hypothesis is
that at every maximal ideal `𝔪` the comparison map `K/𝔪K ⟶ ker(d mod 𝔪)` is SURJECTIVE — in
submodule language `d⁻¹(𝔪R^{n₁}) ≤ K + 𝔪R^{n₀}` — and the conclusion is that at every maximal
ideal it is INJECTIVE, in submodule language `K ∩ 𝔪R^{n₀} ≤ 𝔪K`.

**The proof, in Tor language.**  Put `B = range d ≤ R^{n₁}` and `M = R^{n₁}/B`.  Since
`R^{n₀}` is flat, `coker(K ⊗ κ ⟶ ker(d ⊗ κ)) ≅ Tor₁(M, κ)` for `κ = R/𝔪`, so the hypothesis
says `Tor₁(M, R/𝔪) = 0` at every maximal ideal.  `M` is finitely presented **by
construction** — it is the cokernel of a map of finite free modules, so no noetherian
hypothesis is needed — hence the local criterion for flatness makes `M` flat, hence
projective, so `0 ⟶ B ⟶ R^{n₁} ⟶ M ⟶ 0` splits and `B` is flat.  Then
`ker(K ⊗ κ ⟶ R^{n₀} ⊗ κ) ≅ Tor₁(B, κ) = 0`, which is the conclusion.

Mathlib material to build on: `Module.Flat.ker_lTensor_eq`
(`Mathlib/RingTheory/Flat/Equalizer.lean`), `Module.free_of_flat_of_isLocalRing`,
`Mathlib/RingTheory/Flat/LocallyFree.lean`, and the abstract `Tor` of
`Mathlib/CategoryTheory/Monoidal/Tor.lean` if a Tor-free rendering proves awkward.  The
statement is deliberately phrased with `Submodule.comap`, `⊓` and `•` rather than with tensor
products so that a prover may choose either rendering.

**FAITHFULNESS.**  Finite freeness of the TARGET is essential and is the one hypothesis a
reader is likely to try to weaken: the conclusion is false for a general flat `F₁`, because
`F₁/range d` is then not finitely presented and Tor-vanishing at maximal ideals no longer
forces flatness.  That is exactly why the geometric leaf below must produce Grothendieck's
finite free complex rather than the Čech complex it starts from.  Quantifying the hypothesis
over ALL maximal ideals while concluding at ONE is also not an oversight: flatness of `M` is
a global statement and the local criterion consumes every maximal ideal.

**THE PROOF ACTUALLY CARRIED OUT (2026-07-28), and it is Tor-free.**  `Tor` is never named;
every Tor-vanishing statement above is replaced by a SPLITTING, which is what makes the
argument fit `Mathlib` at this pin (there is no `Tor` of modules here, only the abstract
monoidal one).

1. `M = Rⁿ¹ / range d` is finitely presented, `Module.finitePresentation_of_free_of_surjective`.
2. `M` is PROJECTIVE, by `Module.projective_of_localization_maximal` — projectivity of a
   finitely presented module may be checked on stalks.  At a maximal `I` the local statement
   is `free_of_isLocalRing_of_comap_smul_le` above, applied to the localized presentation
   `(Rⁿ⁰)_I ⟶ (Rⁿ¹)_I ⟶ M_I ⟶ 0` (exact because localization is exact) with
   `K = (ker d)_I`.  Transporting the hypothesis at `I` is `localized'_smul_top_eq` plus
   `exists_smul_mem_of_mk'_mem_localized'`: clear denominators, apply `hsurj I`, put the
   denominator back.
3. `0 ⟶ range d ⟶ Rⁿ¹ ⟶ M ⟶ 0` therefore splits, so `range d` is projective;
4. hence `0 ⟶ ker d ⟶ Rⁿ⁰ ⟶ range d ⟶ 0` splits, giving a retraction `p : Rⁿ⁰ ⟶ ker d`;
5. and then `x ∈ ker d ⊓ 𝔪Rⁿ⁰` gives `x = p x ∈ p(𝔪Rⁿ⁰) = 𝔪·p(Rⁿ⁰) ≤ 𝔪·ker d`.

**TWO OBSERVATIONS ON THE STATEMENT, recorded rather than acted on.**  (a) `hm` is not used:
step 5 works for an ARBITRARY ideal `m` once `ker d` is a direct summand, so maximality of
the *conclusion's* ideal is redundant (maximality of the *hypothesis's* ideals is not — step 2
consumes `hsurj` at every maximal ideal).  (b) The faithfulness note above is right that the
proof given consumes every maximal ideal, but the hypothesis at `m` ALONE would in fact
suffice: `ker d ⊓ 𝔪Rⁿ⁰ ≤ 𝔪·ker d` is a local condition at `m` (at any other maximal `𝔫` the
ideal `m` becomes the unit ideal and the inclusion is vacuous), and only `M_m` needs to be
free.  Both are hypothesis-strengthenings, harmless for the consumer, and the statement is
left exactly as the consumer
`rank_quotient_appTop_le_one_of_isIso_appTop_fiber` supplies it. -/
theorem inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le
    {R : Type*} [CommRing R] {n₀ n₁ : ℕ}
    (d : (Fin n₀ → R) →ₗ[R] (Fin n₁ → R))
    (hsurj : ∀ mm : Ideal R, mm.IsMaximal →
      Submodule.comap d (mm • (⊤ : Submodule R (Fin n₁ → R))) ≤
        LinearMap.ker d ⊔ mm • (⊤ : Submodule R (Fin n₀ → R)))
    (m : Ideal R) (_hm : m.IsMaximal) :
    LinearMap.ker d ⊓ (m • (⊤ : Submodule R (Fin n₀ → R))) ≤ m • LinearMap.ker d := by
  classical
  -- `M := coker d` is finitely presented *by construction*.
  have hfg : (LinearMap.range d).FG := by
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map d
  haveI : Module.FinitePresentation R ((Fin n₁ → R) ⧸ LinearMap.range d) :=
    Module.finitePresentation_of_free_of_surjective (LinearMap.range d).mkQ
      (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact hfg)
  -- `M` is projective, checked on stalks.
  haveI : Module.Projective R ((Fin n₁ → R) ⧸ LinearMap.range d) := by
    apply Module.projective_of_localization_maximal
    intro I hI
    haveI : Module.Free (Localization.AtPrime I)
        (LocalizedModule I.primeCompl (Fin n₁ → R)) :=
      Module.free_of_isLocalizedModule (Rₛ := Localization.AtPrime I) I.primeCompl
        (LocalizedModule.mkLinearMap I.primeCompl (Fin n₁ → R))
    haveI : Module.Free (Localization.AtPrime I)
        (LocalizedModule I.primeCompl ((Fin n₁ → R) ⧸ LinearMap.range d)) := by
      refine free_of_isLocalRing_of_comap_smul_le
        (LocalizedModule.map I.primeCompl d)
        (LocalizedModule.map I.primeCompl (LinearMap.range d).mkQ)
        (LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _))
        ?_
        ((LinearMap.ker d).localized' (Localization.AtPrime I) I.primeCompl
          (LocalizedModule.mkLinearMap I.primeCompl (Fin n₀ → R)))
        ?_ ?_
      · -- localization is exact, so the presentation localizes
        exact LocalizedModule.map_exact I.primeCompl d (LinearMap.range d).mkQ
          (LinearMap.exact_map_mkQ_range d)
      · -- the localized kernel sits inside the kernel of the localized map
        rintro _ ⟨y, hy, s, rfl⟩
        simp only [LinearMap.mem_ker, ← IsLocalizedModule.mk_eq_mk', LocalizedModule.map_mk,
          LinearMap.mem_ker.mp hy, LocalizedModule.zero_mk]
      · -- the hypothesis at `I`, transported to `R_I`
        rw [← localized'_smul_top_eq I (M := Fin n₁ → R),
          ← localized'_smul_top_eq I (M := Fin n₀ → R)]
        intro z hz
        obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective I.primeCompl
          (LocalizedModule.mkLinearMap I.primeCompl (Fin n₀ → R)) z
        simp only [Function.uncurry_apply_pair] at hz ⊢
        rw [Submodule.mem_comap] at hz
        have hdz : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap I.primeCompl (Fin n₁ → R))
            (d x) s ∈ (I • (⊤ : Submodule R (Fin n₁ → R))).localized'
              (Localization.AtPrime I) I.primeCompl
              (LocalizedModule.mkLinearMap I.primeCompl (Fin n₁ → R)) := by
          rw [← IsLocalizedModule.mk_eq_mk'] at hz ⊢
          rwa [LocalizedModule.map_mk] at hz
        obtain ⟨t, ht⟩ := exists_smul_mem_of_mk'_mem_localized' I.primeCompl
          (Localization.AtPrime I) _ _ _ _ hdz
        have hx : ((t : R) • x) ∈ LinearMap.ker d ⊔ I • (⊤ : Submodule R (Fin n₀ → R)) := by
          refine hsurj I hI ?_
          rw [Submodule.mem_comap, map_smul]
          exact ht
        obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hx
        have hsplit : IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap I.primeCompl (Fin n₀ → R)) x s
            = IsLocalizedModule.mk'
                (LocalizedModule.mkLinearMap I.primeCompl (Fin n₀ → R)) u (t * s)
              + IsLocalizedModule.mk'
                (LocalizedModule.mkLinearMap I.primeCompl (Fin n₀ → R)) w (t * s) := by
          rw [← IsLocalizedModule.mk'_add, huw, ← Submonoid.smul_def,
            IsLocalizedModule.mk'_cancel_left]
        rw [hsplit]
        refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
        · exact (Submodule.mem_localized' _ _ _ _ _).mpr ⟨u, hu, t * s, rfl⟩
        · exact (Submodule.mem_localized' _ _ _ _ _).mpr ⟨w, hw, t * s, rfl⟩
    infer_instance
  -- `0 ⟶ range d ⟶ Rⁿ¹ ⟶ M ⟶ 0` splits, so `range d` is projective.
  haveI : Module.Projective R (LinearMap.range d) := by
    have hsplit := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range d))
      Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
    obtain ⟨l', hl'⟩ := hsplit.mp
      (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
    exact Module.Projective.of_split _ _ hl'
  -- hence `0 ⟶ ker d ⟶ Rⁿ⁰ ⟶ range d ⟶ 0` splits too: `ker d` is a direct summand.
  obtain ⟨p, hp⟩ : ∃ p : (Fin n₀ → R) →ₗ[R] LinearMap.ker d,
      p ∘ₗ (LinearMap.ker d).subtype = LinearMap.id := by
    have hexact : Function.Exact (LinearMap.ker d).subtype
        (d.codRestrict (LinearMap.range d) (LinearMap.mem_range_self d)) := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    have hsplit := (Function.Exact.split_tfae hexact Subtype.val_injective
      (fun ⟨_, y, e⟩ => ⟨y, Subtype.ext e⟩)).out 0 1
    exact hsplit.mp (Module.projective_lifting_property _ _ (fun ⟨_, y, e⟩ => ⟨y, Subtype.ext e⟩))
  -- a retraction `p` onto `ker d` sends `𝔪·Rⁿ⁰` into `𝔪·ker d` and fixes `ker d`.
  intro x hx
  have hx1 : x ∈ LinearMap.ker d := hx.1
  have hx2 : x ∈ m • (⊤ : Submodule R (Fin n₀ → R)) := hx.2
  have hpx : p x ∈ m • (⊤ : Submodule R (LinearMap.ker d)) := by
    have h0 : p x ∈ Submodule.map p (m • (⊤ : Submodule R (Fin n₀ → R))) := ⟨x, hx2, rfl⟩
    rw [Submodule.map_smul''] at h0
    exact (Submodule.smul_mono (le_refl m) le_top) h0
  have hpxeq : p x = ⟨x, hx1⟩ := by
    have hid := LinearMap.congr_fun hp ⟨x, hx1⟩
    simpa using hid
  have hfinal : ((LinearMap.ker d).subtype) (p x) ∈
      Submodule.map (LinearMap.ker d).subtype (m • (⊤ : Submodule R (LinearMap.ker d))) :=
    ⟨p x, hpx, rfl⟩
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, hpxeq] at hfinal
  exact hfinal

/-- **THE BRIDGE** (PROVEN): the fibre statement plus the commutative-algebra leaf give the
rank bound.

Let `K = ker d`, `k₀ = e 1`.  The hypothesis `hfib` says the fibre `H⁰` — which in the
equalizer description is `d⁻¹(𝔪F₁)/𝔪F₀` — is spanned by `k₀`; `hCA` says `K ∩ 𝔪F₀ = 𝔪K`.
Given `a : A`, the element `e a` lies in `d⁻¹(𝔪F₁)`, so `e a = r • k₀ + y` with `y ∈ 𝔪F₀`;
but `y = e a - r • k₀ = e (a - r • 1)` lies in `K` as well, hence in `K ∩ 𝔪F₀ = 𝔪K`, hence
`a - r • 1 ∈ 𝔪A`.  So `A = R·1 + 𝔪A`, i.e. `A/𝔪A` is spanned by `1` over the field `R/𝔪`,
which is `rank ≤ 1`.

Nothing here is geometric and nothing here needs the modules to be free or finite; the two
finiteness hypotheses live in the leaf below it, where they are actually used. -/
theorem rank_quotient_le_one_of_fibre_span
    {R A F₀ F₁ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁]
    {d : F₀ →ₗ[R] F₁} (e : A ≃ₗ[R] LinearMap.ker d)
    (m : Ideal R) (hm : m.IsMaximal)
    (hfib : Submodule.comap d (m • (⊤ : Submodule R F₁)) =
      Submodule.span R {((e 1 : LinearMap.ker d) : F₀)} ⊔ m • (⊤ : Submodule R F₀))
    (hCA : LinearMap.ker d ⊓ (m • (⊤ : Submodule R F₀)) ≤ m • LinearMap.ker d) :
    letI : Algebra (R ⧸ m) (A ⧸ Ideal.map (algebraMap R A) m) :=
      (Ideal.quotientMap (I := m) (Ideal.map (algebraMap R A) m) (algebraMap R A)
        Ideal.le_comap_map).toAlgebra
    Module.rank (R ⧸ m) (A ⧸ Ideal.map (algebraMap R A) m) ≤ 1 := by
  haveI : m.IsMaximal := hm
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  letI : Algebra (R ⧸ m) (A ⧸ Ideal.map (algebraMap R A) m) :=
    (Ideal.quotientMap (I := m) (Ideal.map (algebraMap R A) m) (algebraMap R A)
      Ideal.le_comap_map).toAlgebra
  show Module.rank (R ⧸ m) (A ⧸ Ideal.map (algebraMap R A) m) ≤ 1
  have hmap : (m • (⊤ : Submodule R A)) = (Ideal.map (algebraMap R A) m).restrictScalars R :=
    Ideal.smul_top_eq_map m
  have hsm : m • (LinearMap.ker d) = Submodule.map (LinearMap.ker d).subtype (m • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hmap' : Submodule.map (e.symm : LinearMap.ker d →ₗ[R] A) (m • ⊤) =
      m • (⊤ : Submodule R A) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  -- `A = R·1 + 𝔪A`.
  have key : ∀ a : A, ∃ r : R, a - r • (1 : A) ∈ m • (⊤ : Submodule R A) := by
    intro a
    have h1 : ((e a : LinearMap.ker d) : F₀) ∈
        Submodule.comap d (m • (⊤ : Submodule R F₁)) := by
      simp [Submodule.mem_comap]
    rw [hfib] at h1
    obtain ⟨u, hu, y, hy, huy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨r, ?_⟩
    have hzy : ((e (a - r • (1 : A)) : LinearMap.ker d) : F₀) = y := by
      have h2 : e (a - r • (1 : A)) = e a - r • e 1 := by rw [map_sub, map_smul]
      rw [h2]
      have h3 : ((e a - r • e 1 : LinearMap.ker d) : F₀) = (e a : F₀) - r • ((e 1 : F₀)) := by
        simp
      rw [h3, ← huy]
      abel
    have hz1 : ((e (a - r • (1 : A)) : LinearMap.ker d) : F₀) ∈
        LinearMap.ker d ⊓ (m • (⊤ : Submodule R F₀)) :=
      ⟨(e (a - r • (1 : A))).2, hzy ▸ hy⟩
    obtain ⟨w, hw, hwz⟩ := hsm ▸ hCA hz1
    have hwz' : w = e (a - r • (1 : A)) := Subtype.ext hwz
    have hfin : a - r • (1 : A) = e.symm w := by rw [hwz']; simp
    rw [hfin, ← hmap']
    exact ⟨w, hw, rfl⟩
  -- A module spanned by `1` over a field has rank at most one.
  rw [rank_le_one_iff]
  refine ⟨(1 : A ⧸ Ideal.map (algebraMap R A) m), ?_⟩
  intro v
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective v
  obtain ⟨r, hr⟩ := key a
  refine ⟨Ideal.Quotient.mk m r, ?_⟩
  have hsmul : (Ideal.Quotient.mk m r) • (1 : A ⧸ Ideal.map (algebraMap R A) m) =
      Ideal.Quotient.mk _ (algebraMap R A r) := by
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk]
  rw [hsmul]
  refine Ideal.Quotient.eq.mpr ?_
  have h2 : a - algebraMap R A r ∈ Ideal.map (algebraMap R A) m := by
    rw [hmap] at hr
    simpa [Algebra.smul_def] using hr
  have h3 := (Ideal.neg_mem_iff _).mpr h2
  rwa [neg_sub] at h3

/-- **PURITY OF `ker d` WHEN `range d` IS FLAT** (PROVEN, 2026-07-28) — pure commutative
algebra, no finiteness of any kind, no noetherian hypothesis, and in particular **no
freeness**: for `d : M ⟶ N` with `range d` a FLAT `R`-module and any ideal `I`,

  `ker d ∩ I·M ≤ I·(ker d)`,

i.e. `ker d ⊗ R/I ⟶ M ⊗ R/I` is injective.  Immediate from
`LinearMap.lTensor_injective_of_exact_of_flat` applied to `0 ⟶ ker d ⟶ M ⟶ range d ⟶ 0`
(whose right-hand term is flat by hypothesis) with `A := R ⧸ I`, transported across
`TensorProduct.quotTensorEquivQuotSMul`.

**This is the lemma that makes the finite-free shape of the geometric leaf unnecessary**, and
it is why the leaf below asks for a flat IMAGE rather than for Grothendieck's finite free
complex; see that leaf's docstring.  It is *not* a strengthening of
`inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le` above and does not replace it: that
leaf derives flatness of `range d` from finite freeness plus a Tor-vanishing hypothesis,
whereas this one takes flatness of `range d` as given. -/
theorem inf_smul_top_le_smul_ker_of_flat_range {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (d : M →ₗ[R] N) [Module.Flat R ↥(LinearMap.range d)] (I : Ideal R) :
    LinearMap.ker d ⊓ (I • (⊤ : Submodule R M)) ≤ I • LinearMap.ker d := by
  have hex : Function.Exact (LinearMap.ker d).subtype d.rangeRestrict := by
    intro y
    constructor
    · intro hy
      exact ⟨⟨y, by simpa [Subtype.ext_iff] using hy⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact Subtype.ext (by simpa using hz)
  have hinj : Function.Injective
      (LinearMap.lTensor (R ⧸ I) (LinearMap.ker d).subtype) :=
    LinearMap.lTensor_injective_of_exact_of_flat d.rangeRestrict
      (LinearMap.surjective_rangeRestrict d) _ (LinearMap.ker d).subtype_injective hex (R ⧸ I)
  intro x hx
  set k : ↥(LinearMap.ker d) := ⟨x, hx.1⟩ with hk
  have hsq : (TensorProduct.quotTensorEquivQuotSMul M I)
      (LinearMap.lTensor (R ⧸ I) (LinearMap.ker d).subtype
        ((TensorProduct.quotTensorEquivQuotSMul (↥(LinearMap.ker d)) I).symm
          (Submodule.Quotient.mk k)))
      = Submodule.Quotient.mk (k : M) := by
    have h1 : (TensorProduct.quotTensorEquivQuotSMul (↥(LinearMap.ker d)) I).symm
        (Submodule.Quotient.mk k) = (1 : R ⧸ I) ⊗ₜ k := by
      rw [LinearEquiv.symm_apply_eq, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rw [h1, LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rfl
  have hzero : Submodule.Quotient.mk (k : M) = (0 : M ⧸ I • (⊤ : Submodule R M)) := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx.2
  rw [hzero] at hsq
  have h2 : LinearMap.lTensor (R ⧸ I) (LinearMap.ker d).subtype
      ((TensorProduct.quotTensorEquivQuotSMul (↥(LinearMap.ker d)) I).symm
        (Submodule.Quotient.mk k)) = 0 :=
    (TensorProduct.quotTensorEquivQuotSMul M I).injective (by rw [hsq]; simp)
  have h3 : (TensorProduct.quotTensorEquivQuotSMul (↥(LinearMap.ker d)) I).symm
      (Submodule.Quotient.mk k) = 0 := hinj (by rw [h2]; simp)
  have h4 : (Submodule.Quotient.mk k : ↥(LinearMap.ker d) ⧸ I • ⊤) = 0 :=
    (TensorProduct.quotTensorEquivQuotSMul (↥(LinearMap.ker d)) I).symm.injective
      (by rw [h3]; simp)
  rw [Submodule.Quotient.mk_eq_zero] at h4
  have h5 : Submodule.map (LinearMap.ker d).subtype (I • (⊤ : Submodule R ↥(LinearMap.ker d)))
      = I • LinearMap.ker d := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← h5]
  exact ⟨k, h4, rfl⟩

/-- **THE BRIDGE, IN RING FORM** (PROVEN, 2026-07-28): the fibre clause plus purity of
`ker d` give `a ≡ r` modulo `𝔪A`.

This is the `key` step of `rank_quotient_le_one_of_fibre_span` above, stated on its own and
in the form `surjective_algebraMap_of_finite_of_forall_isMaximal` consumes.  The two are
deliberately *not* merged: that theorem is proven and its proof is not touched here.  The
argument is the same three lines — `e a` lies in `d⁻¹(𝔪F₁) = R·(e 1) + 𝔪F₀`, so
`e a - r·(e 1) = e (a - r·1)` lies in `ker d ∩ 𝔪F₀`, which `hCA` puts inside `𝔪·ker d`, and
`e.symm` carries that to `𝔪A`.

Nothing here is geometric and nothing needs the modules to be free or finite. -/
theorem exists_sub_algebraMap_mem_of_fibre_span {R A F₀ F₁ : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁]
    {d : F₀ →ₗ[R] F₁} (e : A ≃ₗ[R] LinearMap.ker d) (m : Ideal R)
    (hfib : Submodule.comap d (m • (⊤ : Submodule R F₁)) =
      Submodule.span R {((e 1 : LinearMap.ker d) : F₀)} ⊔ m • (⊤ : Submodule R F₀))
    (hCA : LinearMap.ker d ⊓ (m • (⊤ : Submodule R F₀)) ≤ m • LinearMap.ker d)
    (a : A) : ∃ r : R, a - algebraMap R A r ∈ m.map (algebraMap R A) := by
  have hsm : m • (LinearMap.ker d) = Submodule.map (LinearMap.ker d).subtype (m • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  have hmap' : Submodule.map (e.symm : LinearMap.ker d →ₗ[R] A) (m • ⊤) =
      m • (⊤ : Submodule R A) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have h1 : ((e a : LinearMap.ker d) : F₀) ∈
      Submodule.comap d (m • (⊤ : Submodule R F₁)) := by
    simp [Submodule.mem_comap]
  rw [hfib] at h1
  obtain ⟨u, hu, y, hy, huy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
  refine ⟨r, ?_⟩
  have hzy : ((e (a - r • (1 : A)) : LinearMap.ker d) : F₀) = y := by
    have h2 : e (a - r • (1 : A)) = e a - r • e 1 := by rw [map_sub, map_smul]
    rw [h2]
    have h3 : ((e a - r • e 1 : LinearMap.ker d) : F₀) = (e a : F₀) - r • ((e 1 : F₀)) := by
      simp
    rw [h3, ← huy]
    abel
  have hz1 : ((e (a - r • (1 : A)) : LinearMap.ker d) : F₀) ∈
      LinearMap.ker d ⊓ (m • (⊤ : Submodule R F₀)) :=
    ⟨(e (a - r • (1 : A))).2, hzy ▸ hy⟩
  obtain ⟨w, hw, hwz⟩ := hsm ▸ hCA hz1
  have hwz' : w = e (a - r • (1 : A)) := Subtype.ext hwz
  have hfin : a - r • (1 : A) = e.symm w := by rw [hwz']; simp
  have hmem : a - r • (1 : A) ∈ m • (⊤ : Submodule R A) := by
    rw [hfin, ← hmap']
    exact ⟨w, hw, rfl⟩
  have hres : a - r • (1 : A) ∈ (m.map (algebraMap R A)).restrictScalars R := by
    rw [← Ideal.smul_top_eq_map]; exact hmem
  simpa [Algebra.smul_def] using hres

/-- **LEAF 3a-N′ — A GLOBAL SECTION VANISHING ON THE FIBRE `X_s` LIES IN `𝔪 · Γ(X, ⊤)`** —
**PROVEN** (2026-07-30) over `self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero` far above, in
one step: that leaf puts `a` in `𝔪 · R[a]`, and `R[a] ≤ ⊤`.  (It was itself CUT 2026-07-30 out
of `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` below, which is PROVEN over it; that
consumer and its call are unchanged.)  `𝔪` is `RingHom.ker (S.Γevaluation s)`, i.e. the maximal
ideal cut out by `s` when `s` comes from `exists_point_ker_Γevaluation_eq_of_isMaximal`.

**THIS STATEMENT IS NO LONGER ON THE CRITICAL PATH, AND THE ANALYSIS BELOW IS NOT A ROUTE TO
WHAT IS.**  Everything from here to the end of this docstring is about `A = Γ(X, ⊤)` as the
kernel of a Čech complex, and it identifies THIS statement with `Tor₁^R(range d, κ(𝔪)) = 0`.
The file's one remaining leaf is the `R[a]` form, and `R[a]` is a subalgebra of `ker d` rather
than a term of the complex, so the identification does **not** transfer to it: closing the
`Tor₁` below would re-prove this theorem and leave the leaf open, and the leaf is what
`finiteType_appTop_of_isProper` consumes.  The analysis is retained because it is correct and
because it names a real theorem to build; it is a record, not a task.

**WHAT THIS CUT DOES, AND WHY IT IS NOT A REWORDING.**  It is *equivalent* to the equation
below — the two differ by the lift-and-subtract step, which
`surjective_appTop_fiberι_comp_appTop` now discharges — and that is the point: the equation's
`span {1}`, its maximality hypothesis and its ideal have all been shown to be bookkeeping, so
what is left is one sentence with a single geometric hypothesis, `x|_{X_s} = 0`.  In sheaf
language it is `Γ(X, 𝔪𝒪_X) ⊆ 𝔪 · Γ(X, 𝒪_X)` (the reverse inclusion is trivial), i.e. **the
comparison of the ideal sheaf's sections with the ideal's own sections** — which is what every
classical proof of III.12.11(a) actually computes.  It also puts this leaf into the same shape
as the file's other one, `mem_smul_adjoin_of_appTop_fiberι_eq_zero`, without merging them (see
the warning there: an arbitrary subalgebra is NOT known to satisfy this).

**WHAT IS FREE, AND WHAT THE WHOLE REMAINING GAP IS: A `Tor₁` ON THE ČECH COKERNEL**
(2026-07-30 analysis; it sharpens "noetherian approximation" to a named classical theorem).
Take a FINITE affine open cover `U_1, …, U_n` of `X` — `X` is quasi-compact, and separated over
the affine `S`, so the `U_i ⊓ U_j` are affine too — and let

  `F₀ = ∏ᵢ Γ(Uᵢ, 𝒪)`,  `F₁ = ∏_{i<j} Γ(Uᵢ ⊓ Uⱼ, 𝒪)`,  `d(x)ᵢⱼ = xᵢ| − xⱼ|`,
  `K = ker d = Γ(X, 𝒪_X) = A`,  `Q = range d`.

`Flat f` makes every `Γ(Uᵢ, 𝒪)` a flat `R`-module, hence `F₀` and `F₁` flat; and since the
product is FINITE, `F₀ ⊗_R κ(𝔪)` and `F₁ ⊗_R κ(𝔪)` are the corresponding products for the fibre
`X_𝔪`, so `ker (d ⊗ κ(𝔪)) = Γ(X_𝔪, 𝒪)`.  Then:

* **the fibre clause is FREE from `h`.**  `h` says `Γ(X_𝔪, 𝒪) = κ(𝔪)·1`, and `1` is the image
  of `1 ∈ A`, so `K ⊗ κ(𝔪) ⟶ ker (d ⊗ κ(𝔪))` is SURJECTIVE.  Chasing
  `0 → K → F₀ → Q → 0` and `0 → Q → F₁ → F₁/Q → 0` with `F₀, F₁` flat identifies
  `ker(d ⊗ κ) / im(K ⊗ κ) ≅ Tor₁^R(F₁/Q, κ)`, so this says exactly
  `Tor₁^R(F₁/Q, κ(𝔪)) = 0` at every maximal ideal.
* **this leaf is exactly `Tor₁^R(Q, κ(𝔪)) = 0`**, i.e. injectivity of `K ⊗ κ ⟶ F₀ ⊗ κ`, i.e.
  `K ⊓ 𝔪F₀ ≤ 𝔪K` — and `K ⊓ 𝔪F₀` is precisely the set of global sections vanishing on `X_𝔪`,
  because `Γ(Uᵢ, 𝒪)/𝔪Γ(Uᵢ, 𝒪)` is the coordinate ring of `Uᵢ ⊓ X_𝔪`.  Given flatness of `Q`
  the file already has the deduction: `inf_smul_top_le_smul_ker_of_flat_range` above.
* **and `Tor₁(Q, κ) ≅ Tor₂(F₁/Q, κ)`.**  So the ONLY missing input is the step from
  `Tor₁(F₁/Q, κ(𝔪)) = 0` at all maximal ideals to `F₁/Q` being FLAT, and that step is the local
  criterion, which needs `F₁/Q` **finitely presented**.  For a two-element cover `F₁/Q` is
  literally `H¹(X, 𝒪_X)`; in general it is an extension of `H¹` by a submodule of `F₂`.

**So the gap is Grothendieck finiteness in POSITIVE degree, not a limit theory.**  That is a
sharper and more standard statement than the noetherian-approximation gap recorded on the
equation below, and it explains retrospectively why the earlier `flat range d` shape of this
leaf was the right one: flatness of `Q` is the real content, and `h` supplies the `Tor₁`
half of it for nothing.  It does NOT make the leaf reachable at this pin — there is no coherent
cohomology of any kind available, **re-checked 2026-07-30 against BOTH sources, since a false
absence claim has already cost this file two cycles**: `Mathlib` has no `directImage` and no
higher pushforward, and `Mathlib/AlgebraicGeometry/Modules/` is `Presheaf`, `Sheaf`, `Tilde`
only; `~/cs/FLT` has cohomology only in the group-theoretic sense
(`FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/`), nothing sheaf-theoretic.  But
it names the theorem to build, and it is a *finiteness* theorem rather than a descent one.

**ONE CASE IS FREE, AND IT IS THE ENGINE OF STEP 3 OF THE ROUTE BELOW** (verified 2026-07-30,
not formalised here because nothing in the cone consumes it): if `𝔪` were generated by a single
NONZERODIVISOR `t ∈ R`, this leaf would be immediate from `Flat f` alone.  Flatness makes `t` a
nonzerodivisor on every `Γ(U, 𝒪)`, so `x|_U = t·b_U` with `b_U` UNIQUE, and uniqueness makes the
`b_U` agree on overlaps, hence glue to `b ∈ Γ(X, ⊤)` with `x = t·b`.  Equivalently:
multiplication by `t` is an isomorphism `𝒪_X ≅ t𝒪_X`, so `Γ(X, t𝒪_X) = t·Γ(X, 𝒪_X)` with no
cohomology at all.  A related free reduction: since the cover is FINITE, `x|_{X_𝔪} = 0` already
gives `x ∈ Γ(X, J𝒪_X)` for some FINITELY GENERATED `J ≤ 𝔪`, so nothing is lost by assuming `𝔪`
finitely generated.  Both are recorded so that a prover attacking the general case knows which
part of it is genuinely hard: it is the passage from a regular element to an arbitrary finitely
generated ideal, i.e. the `H¹` above.

**FAITHFULNESS — VOUCHED.**  A universally quantified implication with `x = 0` in its domain,
so no witness is forgotten and there is no vacuity question; the classical statement
(Hartshorne III.12.11(a) / EGA III 7.8.6 / Stacks 0E0L in degree `0`) is true under exactly
these hypotheses, and `h` cannot be dropped — see the equation below for what breaks. -/
theorem mem_smul_top_of_appTop_fiberι_eq_zero (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) (s : S)
    (a : ↥Γ(X, ⊤)) (ha : (f.fiberι s).appTop.hom a = 0) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    a ∈ RingHom.ker (S.Γevaluation s).hom • (⊤ : Submodule ↥Γ(S, ⊤) ↥Γ(X, ⊤)) := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact Submodule.smul_mono le_rfl le_top
    (self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero f h s a ha)

/-- **LEAF 3a-N — NAKAYAMA'S INPUT: `A = R·1 + 𝔪A` AT EVERY MAXIMAL IDEAL** — **PROVEN**
(2026-07-30) over `mem_smul_top_of_appTop_fiberι_eq_zero` immediately above, by the
maximal-ideal ↔ point dictionary and nothing else; that leaf's docstring carries the current
obstruction analysis and supersedes the route recorded here where the two disagree.
(CUT 2026-07-29 out of `exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber`, which is
PROVEN over it immediately below.)  This is all the geometry left in the cluster.

**What it says.**  With `R = Γ(S, ⊤)`, `A = Γ(X, ⊤)` and `𝔪 ⊆ R` maximal, the `R`-module `A`
is generated by `1` together with `𝔪A`.  Equivalently `dim_{R/𝔪} A/𝔪A ≤ 1`, equivalently the
degree-zero comparison map `A ⊗_R κ(s) ⟶ H⁰(X_s, 𝒪)` is INJECTIVE (it is surjective for free
from `h s`); equivalently, given `module_finite_appTop_of_isProper`, it is the exact
hypothesis of `surjective_algebraMap_of_finite_of_forall_isMaximal`.

**WHY THIS SHAPE, AND WHAT WAS DISCHARGED** (2026-07-29).  The previous cut asked for a
two-term complex `d : C₀ ⟶ C₁` of `R`-modules with `range d` flat, `A ≃ₗ ker d` and a fibre
clause.  Its own docstring already recorded that `C₀ := A`, `C₁ := 0`, `d := 0` satisfies
every clause of that package exactly when the equation above holds — so the complex, the
flatness clause and the `LinearEquiv` were *bookkeeping around this equation*, and they are
now discharged (the theorem below is proven by exhibiting that witness).  Three consequences:
the frontier no longer carries an existential that has to be pinned; the statement is a
single equation with no vacuity question; and the localisation step of the route below —
which is the first thing any prover does — becomes available, because the statement is now
about a FIXED maximal ideal rather than about one complex serving all of them at once.

**THE OBSTRUCTION ANALYSIS IN THE BLOCK INTRODUCTION ABOVE IS WRONG, AND THIS IS THE MAIN
CONTENT OF THIS DOCSTRING** (2026-07-29).  That introduction concludes, under *Localize and
complete*, that "what is missing is the comparison of `Â` with `lim_n Γ(X_n, 𝒪)`, which is
the THEOREM ON FORMAL FUNCTIONS … and that is not elementary", and the docstring below
concludes that Grothendieck's bounded complex of finite frees — hence coherence of `Rⁱf_*`
in ALL degrees — is what makes `range d` flat.  Both are correct accounts of the *routes
they describe* and **false as accounts of the obstruction**: in degree `0` there is an
elementary induction that never completes, never forms `lim_n`, never needs
`{Γ(X, 𝔪ⁿ𝒪_X)}` to be cofinal with `{𝔪ⁿA}`, and never mentions `H^{>0}`.  It is written out
in full below so that the next owner attacks it rather than re-deriving the impossibility
verdict.  (It is a hand-verified argument, not a machine-checked one; every step is named so
each can be refuted separately.)

**THE ELEMENTARY ROUTE.**  Throughout, for an ideal `J ⊆ R` write `X_{R/J} := X ×_S Spec R/J`
— a CLOSED subscheme of `X`, since `Spec R/J ⟶ Spec R` is a closed immersion — and

  `I_J := ker (A ⟶ Γ(X_{R/J}, ⊤))`.

*Step 0 — localise.*  `A/(R·1 + 𝔪A)` is an `R/𝔪`-module, so it vanishes iff it vanishes
after localising at `𝔪`.  `R ⟶ R_𝔪` is FLAT, so
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` (`Mathlib/AlgebraicGeometry/
Morphisms/Flat.lean`, the same lemma that closed the fibrewise half of this file) gives
`Γ(X ×_S Spec R_𝔪, ⊤) = A ⊗_R R_𝔪`, and proper/flat/finitely-presented and the fibre
hypothesis all base-change.  So one may assume `R` LOCAL with maximal ideal `𝔪`, and then —
by `module_finite_appTop_of_isProper` and Nakayama — it suffices to prove `A = R`, i.e. that
`f.appTop` is bijective.  Injectivity is already available:
`injective_appTop_of_flat_of_surjective f` with `surjective_of_isIso_appTop_fiber f h`.

*Step 1 — the ONLY sheaf-theoretic input, and it is degree zero.*  Flatness of `𝒪_X` over `R`
makes `J ⊗_R 𝒪_X ⟶ 𝒪_X` injective, so `J ⊗_R 𝒪_X ≅ J𝒪_X` and `I_J = Γ(X, J𝒪_X)`; in
particular `J ⊆ J'` implies `I_J ⊆ I_{J'}`, `I_0 = 0` and `I_R = A`.  The obligation is:

  for ideals `J ⊆ J' = J + R·t` with `𝔪t ⊆ J`, the quotient `I_{J'}/I_J` embeds in
  `Γ(X_{R/𝔪}, ⊤)`, which is `R/𝔪` by `h`; so `length_R (I_{J'}/I_J) ≤ 1`.

Proof: `J'/J` is a quotient of `R/𝔪`, and `0 ⟶ J𝒪_X ⟶ J'𝒪_X ⟶ (J'/J) ⊗_R 𝒪_X ⟶ 0` is exact
by flatness; apply left exactness of `Γ`.  Nothing here is derived — no `Rⁱf_*`, no
coherence, no Čech-to-derived comparison, no formal functions.  On a finite affine cover it
is bare hand-work: `Γ(U, J𝒪_X) = J·Γ(U)` for `U` affine, and gluing is the sheaf axiom.

*Step 2 — artinian base.*  If `R` is artinian local, take a composition series
`R = J_0 ⊋ J_1 ⊋ ⋯ ⊋ J_ℓ = 0` with `J_i = J_{i+1} + R·t_i` and `𝔪t_i ⊆ J_{i+1}`.  Step 1
telescopes to `length_R A = length_R I_R ≤ ℓ = length_R R`; with `R ↪ A` this forces `A = R`.
`h` enters the whole route in exactly TWO places, both of them here: as
`Γ(X_{R/𝔪}, ⊤) = R/𝔪` inside Step 1, and — through
`surjective_of_isIso_appTop_fiber` feeding `injective_appTop_of_flat_of_surjective` — as the
injection `R ↪ A` used in Steps 0, 2, 3 and 4.  It appears nowhere else.

*Step 3 — a nonzerodivisor.*  Let `R` be noetherian local and `t ∈ 𝔪` a nonzerodivisor.  Then
`(t) ≅ R` as an `R`-module, so `I_{(t)} = Γ(X, t𝒪_X) = tA` — this is the one case where the
ideal is FREE and Step 1's bound is replaced by an equality.  Hence `A/tA ↪ Γ(X_{R/t}, ⊤)`,
which is `R/t` by the induction hypothesis (`t` avoids every associated, hence every minimal,
prime, so `dim R/t = dim R - 1`), and `R/t ⟶ A/tA` splits that injection.  So `A = R·1 + tA`;
`Module.Finite R A` and Nakayama at `t ∈ 𝔪` give `A = R`.

*Step 4 — depth zero.*  If `dim R ≥ 1` and `𝔪 ∈ Ass R`, let `H = H⁰_𝔪(R) = (0 :_R 𝔪^N)` be
the `𝔪`-power torsion (finite length, `R` noetherian).  Since `dim R ≥ 1`, `H ≠ R` and `H`
lies in every prime, so `Spec R/H = Spec R` and `X_{R/H} ⟶ Spec R/H` has the SAME fibres,
while `depth R/H ≥ 1`.  Step 1 gives `length I_H ≤ length H`, and `H ⊆ I_H`, so `I_H = H`;
Step 3 applied to `R/H` gives `Γ(X_{R/H}, ⊤) = R/H`; so `A/H ↪ R/H`, split by `R/H`, whence
`A = R·1 + H = R` because `H ⊆ R`.

*The induction.*  On `dim R` (finite, `R` noetherian local).  `dim R = 0` is Step 2.  For
`dim R = n ≥ 1`: Step 4 reduces to `depth ≥ 1` at the same dimension, then Step 3 consumes
only dimension `n - 1`.  No step is applied at its own dimension twice.

**WHAT THE ROUTE STILL COSTS, STATED HONESTLY.**  Two things, and neither is cohomology.

1. *Step 1 in `Lean`.*  Quasi-coherent ideal sheaves `J𝒪_X`, `𝒪_X/J𝒪_X = i_*𝒪_{X_{R/J}}`,
   and left exactness of `Γ`.  `Mathlib` has `Scheme.Modules`, `tilde`, the `tilde ⊣ Γ`
   adjunction and `SheafOfModules.IsQuasicoherent` (spelled with a lowercase `c`; the
   capital-`C` grep that "proved" their absence is corrected in the block introduction), so
   this is a build against existing API rather than a new theory.
2. *A NOETHERIAN base.*  Steps 3 and 4 need it and the route does not remove it.  This is
   NOT a new obligation for this file: it is verbatim item 2 of the gap list in the docstring
   of `finiteType_appTop_of_isProper` — noetherian approximation for a proper morphism of
   finite presentation (Stacks 0B91), absent from the pin.  So a single limit-theory build
   unlocks BOTH remaining leaves of this module, which is a materially better trade than
   building coherence and base change for one of them.

**FAITHFULNESS.**  `h` cannot be dropped: it is what makes `Γ(X_{R/𝔪}, ⊤) = R/𝔪` in Steps 1
and 2, and without it `h⁰` jumps and the conclusion is literally FALSE where it does.
`[Flat f]` cannot be dropped: it is what makes `J ⊗_R 𝒪_X ⟶ 𝒪_X` injective in Step 1 and `t`
a nonzerodivisor on `𝒪_X` in Step 3.  Maximality of `𝔪` is used through `κ(s) = R/𝔪`.
Properness enters through `module_finite_appTop_of_isProper` (Nakayama in Step 0 and Step 3)
and through quasi-compactness/separatedness in Step 1.  The conclusion is `≤ 1` in disguise
rather than `= 1` because non-vanishing is cheaper and separate (lying over).

**REFUTING CHECK.**  A single equation, no existential, so there is no vacuity question and
no under-pinning: an adversary has nothing to choose.  The statement is classical
(Hartshorne III.12.11(a) / EGA III 7.8.6 in degree `0`, Stacks 0E0L), so a refutation would
have to refute a step of the route above, not the leaf. -/
theorem eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop)
    (m : Ideal ↥Γ(S, ⊤)) (hm : m.IsMaximal) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (⊤ : Submodule ↥Γ(S, ⊤) ↥Γ(X, ⊤)) =
      Submodule.span ↥Γ(S, ⊤) {(1 : ↥Γ(X, ⊤))} ⊔
        m • (⊤ : Submodule ↥Γ(S, ⊤) ↥Γ(X, ⊤)) := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  obtain ⟨s, hker, hsurj⟩ := exists_point_ker_Γevaluation_eq_of_isMaximal S m hm
  refine le_antisymm ?_ le_top
  intro a _
  obtain ⟨r, hr⟩ := surjective_appTop_fiberι_comp_appTop f s (h s) hsurj
    ((f.fiberι s).appTop.hom a)
  rw [CommRingCat.hom_comp] at hr
  have hvan : (f.fiberι s).appTop.hom (a - algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r) = 0 := by
    have hid : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r = f.appTop.hom r := rfl
    rw [map_sub, hid, ← RingHom.comp_apply, hr, sub_self]
  have hmem := mem_smul_top_of_appTop_fiberι_eq_zero f h s _ hvan
  rw [hker] at hmem
  have h1 : algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤) r ∈
      Submodule.span ↥Γ(S, ⊤) {(1 : ↥Γ(X, ⊤))} :=
    Submodule.mem_span_singleton.mpr ⟨r, by simp [Algebra.smul_def]⟩
  exact Submodule.mem_sup.mpr ⟨_, h1, _, hmem, by ring⟩

/-- **LEAF 3a-G — THE DEGREE-`0` COMPLEX WITH FLAT IMAGE** — **PROVEN** (2026-07-29) over
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` immediately above, by exhibiting the
witness `C₀ := A`, `C₁ := A`, `d := 0` that this docstring's own non-vacuity paragraph
already identified as the cheapest candidate.  Everything below is retained because it is
the record of the Čech/coherence route and of what was tried; the OBSTRUCTION verdict it
reaches is **superseded** — see the elementary route on the leaf above.  This
is the geometric half of Hartshorne III.12.11(a) in degree `0`.

**What it says.**  With `R = Γ(S, ⊤)` and `A = Γ(X, ⊤)` there are `R`-modules `C₀`, `C₁` and
an `R`-linear `d : C₀ ⟶ C₁` with

* `Module.Flat R (range d)` — the image of `d` is a FLAT `R`-module;
* `A ≃ₗ[R] ker d` — the global sections of `𝒪_X` are the equalizer of the two-term complex;
* for every maximal ideal `𝔪`, `d⁻¹(𝔪·C₁) = R·(e 1) + 𝔪·C₀` — the SAME complex computes `H⁰`
  of the fibre after reduction mod `𝔪`, and that `H⁰` is the line spanned by the image of
  `1 ∈ A`.  This last clause is exactly `H⁰(X_s, 𝒪) = κ(s)`, i.e. `h s` read through the
  complex.

**THE RE-CUT, AND A CORRECTION TO THE STATEMENT THIS REPLACES** (2026-07-28).  The previous
form of this leaf, `exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber`, demanded
Grothendieck's **finite free** complex (`Fin n₀ → R ⟶ Fin n₁ → R`), and its docstring
justified that at length: *"the commutative-algebra leaf needs `R^{n₁}/range d` to be finitely
PRESENTED … a Čech term is flat but enormous, and the statement is false for it; this is the
one place the reduction to a finite free complex is load-bearing."*

That reasoning is correct **about the route through
`inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le`**, and wrong as a claim about the
leaf.  Finite freeness there is a *vehicle* for one conclusion and one only:
`ker d ∩ 𝔪C₀ ≤ 𝔪·ker d`.  That conclusion follows from flatness of `range d` alone, with no
finiteness, no finite presentation and no noetherian hypothesis
(`inf_smul_top_le_smul_ker_of_flat_range` above) — finite freeness enters the CA leaf only
because it is what lets the local criterion PROVE `range d` flat from Tor-vanishing.  So the
honest geometric obligation is flatness of the image, and asking for a finite free complex
was asking for strictly more than the consumer needs.

Concretely the finite free clause is now discharged for free: once the leaf below is known,
`f.appTop` is bijective, so `A ≅ R` and the complex `R^1 ⟶ R^0` with `d = 0` satisfies the
old statement.  That is the proof of
`exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber` immediately below, which is
kept — unchanged in statement — because `rank_quotient_appTop_le_one_of_isIso_appTop_fiber`
and the CA leaf consume it.

**Where it comes from, and what is still hard.**  Take a finite affine cover `𝔘 = {U_i}` of
`X`: `f` proper makes `X` quasi-compact and separated over the affine `S`, so every
`U_{i₀…i_p}` is affine.  Let `C^•` be the Čech complex of `𝒪_X` for `𝔘`; its terms are FLAT
`R`-modules because `f` is flat, and it commutes with base change term by term because
`Γ(U ×_S Spec R') = Γ(U) ⊗_R R'` for affine `U`.  In degree `0` the sheaf axiom alone — **no
cohomology theory whatsoever** — gives `Γ(X_{R'}, 𝒪) = ker(C⁰ ⊗ R' ⟶ C¹ ⊗ R')`, which is the
third clause with `R' = R/𝔪`.  Mathlib now has a Čech complex functor to start from
(`CategoryTheory.cechComplexFunctor`, see the corrected pin re-check above), though no
comparison theorem.

What is hard is the FIRST clause.  `Tor₁(range d, Q) = ker(H⁰ ⊗ Q ⟶ C⁰ ⊗ Q)`, so flatness of
`range d⁰` is precisely *degree-zero base change for every `R`-module `Q`* — classically a
corollary of Grothendieck's coherence theorem via Hartshorne III.12.2 / Mumford *AV* §5 (the
finite free complex), which is why this remains a theory build and not a missing-lemma hunt.
Nothing in `Mathlib` computes it: see the corrected pin re-check above.

**NON-VACUITY, checked in both directions.**  The existential is not satisfiable by a
degenerate choice.  The cheapest candidate is `C₀ := A`, `C₁ := 0`, `d := 0`, for which
`range d = 0` is flat and `ker d = ⊤`; the third clause then reads
`⊤ = R·1 + 𝔪·A` for every maximal `𝔪` — which is `surjective_quotientMap_appTop_of_isIso_appTop_fiber`,
the very statement this leaf is used to prove.  So no witness escapes the work.  Being the
last input to the theorem, the leaf is of course *equivalent* to what remains of it; that is
a property of every terminal leaf and not a defect of this cut.

**FAITHFULNESS.**  Without `[Flat f]` the Čech terms are not flat and the complex does not
compute the fibres after base change.  Without `h` the third clause is FALSE exactly where
`h⁰` jumps — that is the whole content of semicontinuity.  Properness enters twice: through
quasi-compactness (a finite cover exists at all) and through coherence (flatness of the
image).  `e 1` rather than an arbitrary generator is deliberate: the fibre `H⁰` is not merely
one-dimensional, it is generated by the image of `1`, and it is that pinning which makes the
bridge give surjectivity of `R/𝔪 ⟶ A/𝔪A` rather than only a dimension count.

**ONE STRENGTHENING DELIBERATELY NOT TAKEN, because it is UNVERIFIED.**  It is tempting to
split this into (i) "a flat two-term complex with the fibre clause exists" — pure Čech, no
coherence — and (ii) "for *any* such complex, `range d` is flat".  Clause (ii) was NOT
adopted: it quantifies over adversarial data, and no counterexample search settled it.  (Over
a local ring, `C₀ = R²`, `C₁ = R`, `d = (a,b) ↦ ax + by` has `ker d ≅ R` and non-flat image,
but fails the fibre clause at the closed point — every attempt to repair it either restored
flatness of the image or broke the clause.)  Splitting on an unverified universally quantified
clause would risk planting a FALSE leaf, so the two halves are left bundled here and the Čech
half is recorded as the route rather than as a separate obligation. -/
theorem exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∃ (C₀ C₁ : ModuleCat.{u} ↥Γ(S, ⊤)) (d : C₀ ⟶ C₁),
      Module.Flat ↥Γ(S, ⊤) ↥(LinearMap.range d.hom) ∧
      ∃ e : ↥Γ(X, ⊤) ≃ₗ[↥Γ(S, ⊤)] LinearMap.ker d.hom,
        ∀ m : Ideal ↥Γ(S, ⊤), m.IsMaximal →
          Submodule.comap d.hom (m • (⊤ : Submodule ↥Γ(S, ⊤) C₁)) =
            Submodule.span ↥Γ(S, ⊤) {((e 1 : LinearMap.ker d.hom) : C₀)} ⊔
              m • (⊤ : Submodule ↥Γ(S, ⊤) C₀) := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  refine ⟨ModuleCat.of _ ↥Γ(X, ⊤), ModuleCat.of _ ↥Γ(X, ⊤), 0, ?_, ?_⟩
  · have h0 : LinearMap.range (ModuleCat.Hom.hom
        (0 : ModuleCat.of ↥Γ(S, ⊤) ↥Γ(X, ⊤) ⟶ ModuleCat.of ↥Γ(S, ⊤) ↥Γ(X, ⊤))) = ⊥ := by
      simp
    rw [h0]
    infer_instance
  · refine ⟨(Submodule.topEquiv (R := ↥Γ(S, ⊤)) (M := ↥Γ(X, ⊤))).symm.trans
      (LinearEquiv.ofEq _ _ (by simp)), fun m hm => ?_⟩
    have hc : Submodule.comap (ModuleCat.Hom.hom
        (0 : ModuleCat.of ↥Γ(S, ⊤) ↥Γ(X, ⊤) ⟶ ModuleCat.of ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
        (m • (⊤ : Submodule ↥Γ(S, ⊤) (ModuleCat.of ↥Γ(S, ⊤) ↥Γ(X, ⊤)))) = ⊤ := by
      simp
    rw [hc]
    simpa using eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber f h m hm

/-- **GROTHENDIECK'S COMPLEX IN DEGREE `0`** — **PROVEN** (2026-07-28) over
`exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber` immediately above, whose
docstring carries the obstruction analysis, the corrected pin re-check and the continuation
plan.  The statement is unchanged from when it was a leaf, because
`rank_quotient_appTop_le_one_of_isIso_appTop_fiber` and the commutative-algebra leaf consume
it in this exact form.

**How the finite free complex is obtained, and why that is not cheating.**  The flat-image
leaf plus `inf_smul_top_le_smul_ker_of_flat_range` gives `ker d ∩ 𝔪C₀ ≤ 𝔪·ker d`, hence
(`exists_sub_algebraMap_mem_of_fibre_span`) `A = R·1 + 𝔪A` at every maximal ideal, hence
(`surjective_algebraMap_of_finite_of_forall_isMaximal`, using `module_finite_appTop_of_isProper`)
`R ⟶ A` SURJECTIVE; `surjective_of_isIso_appTop_fiber` and
`injective_appTop_of_flat_of_surjective` make it injective, so `A ≃ₗ[R] R` and the complex
`R^1 ⟶ R^0` with `d = 0` has `ker d = ⊤ ≅ A` and `d⁻¹(𝔪·R^0) = ⊤ = R·1 + 𝔪·R^1`.

So the *finite free* form of the leaf, which the previous cut argued was load-bearing, is in
fact free once flatness of the image is known: the complex may be taken to be `R` itself.
That is a statement about this cut, not a shortcut — everything hard is upstream, in the leaf.
The proof does establish more than it states (it bijectivises `f.appTop` outright), which is
unavoidable for a terminal leaf and harmless: the downstream chain re-derives the same fact
through the rank bound and is left untouched. -/
theorem exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∃ (n₀ n₁ : ℕ) (d : (Fin n₀ → ↥Γ(S, ⊤)) →ₗ[↥Γ(S, ⊤)] (Fin n₁ → ↥Γ(S, ⊤)))
      (e : ↥Γ(X, ⊤) ≃ₗ[↥Γ(S, ⊤)] LinearMap.ker d),
      ∀ m : Ideal ↥Γ(S, ⊤), m.IsMaximal →
        Submodule.comap d (m • (⊤ : Submodule ↥Γ(S, ⊤) (Fin n₁ → ↥Γ(S, ⊤)))) =
          Submodule.span ↥Γ(S, ⊤) {((e 1 : LinearMap.ker d) : Fin n₀ → ↥Γ(S, ⊤))} ⊔
            m • (⊤ : Submodule ↥Γ(S, ⊤) (Fin n₀ → ↥Γ(S, ⊤))) := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  obtain ⟨C₀, C₁, d, hB, e, hfib⟩ :=
    exists_flatRange_ker_linearEquiv_appTop_of_isIso_appTop_fiber f h
  haveI : Module.Flat ↥Γ(S, ⊤) ↥(LinearMap.range d.hom) := hB
  haveI : Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_finite_appTop_of_isProper f h
  have hsurj : Function.Surjective (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) :=
    surjective_algebraMap_of_finite_of_forall_isMaximal fun m hm a =>
      exists_sub_algebraMap_mem_of_fibre_span e m (hfib m hm)
        (inf_smul_top_le_smul_ker_of_flat_range d.hom m) a
  haveI : Surjective f := surjective_of_isIso_appTop_fiber f h
  have hinj : Function.Injective (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) :=
    injective_appTop_of_flat_of_surjective f
  let eRA : ↥Γ(S, ⊤) ≃ₗ[↥Γ(S, ⊤)] ↥Γ(X, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ⟨hinj, hsurj⟩
  set R := ↥Γ(S, ⊤)
  set d₀ : (Fin 1 → R) →ₗ[R] (Fin 0 → R) := 0 with hd₀
  have hker : (⊤ : Submodule R (Fin 1 → R)) = LinearMap.ker d₀ := LinearMap.ker_zero.symm
  let e₀ : ↥Γ(X, ⊤) ≃ₗ[R] ↥(LinearMap.ker d₀) :=
    ((eRA.symm.trans (LinearEquiv.funUnique (Fin 1) R R).symm).trans
      (Submodule.topEquiv).symm).trans (LinearEquiv.ofEq _ _ hker)
  have h1 : eRA.symm (1 : ↥Γ(X, ⊤)) = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [eRA]
  have hval : ((e₀ (1 : ↥Γ(X, ⊤)) : ↥(LinearMap.ker d₀)) : Fin 1 → R) = fun _ => 1 := by
    simp only [e₀, h1, LinearEquiv.trans_apply]
    funext i
    rfl
  refine ⟨1, 0, d₀, e₀, fun m hm => ?_⟩
  rw [hval]
  have hspan : Submodule.span R {(fun _ => 1 : Fin 1 → R)} = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun v => ?_
    refine Submodule.mem_span_singleton.mpr ⟨v 0, ?_⟩
    funext i
    simp [Subsingleton.elim i 0]
  rw [hspan, top_sup_eq, hd₀, Submodule.comap_zero]

/-- **LEAF 3a — `A/𝔪A` IS AT MOST A LINE OVER `R/𝔪`** — **PROVEN** (2026-07-28) over the
geometric leaf `exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber`, the
commutative-algebra leaf `inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le`, and the
bridge `rank_quotient_le_one_of_fibre_span`, all immediately above.  The docstring of the
first of those carries the obstruction analysis and the pin re-check; the one on
`surjective_quotientMap_appTop_of_isIso_appTop_fiber` below carries what this bound is for. -/
theorem rank_quotient_appTop_le_one_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop)
    (m : Ideal ↥Γ(S, ⊤)) (hm : m.IsMaximal) :
    letI : Algebra (↥Γ(S, ⊤) ⧸ m) (↥Γ(X, ⊤) ⧸ Ideal.map f.appTop.hom m) :=
      (Ideal.quotientMap (I := m) (Ideal.map f.appTop.hom m) f.appTop.hom
        Ideal.le_comap_map).toAlgebra
    Module.rank (↥Γ(S, ⊤) ⧸ m) (↥Γ(X, ⊤) ⧸ Ideal.map f.appTop.hom m) ≤ 1 := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  obtain ⟨n₀, n₁, d, e, hfib⟩ :=
    exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber f h
  have hker : Submodule.span ↥Γ(S, ⊤) {((e 1 : LinearMap.ker d) : Fin n₀ → ↥Γ(S, ⊤))} ≤
      LinearMap.ker d :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (e 1).2)
  have hCA := inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le d
    (fun mm hmm => (hfib mm hmm).le.trans (sup_le_sup_right hker _)) m hm
  exact rank_quotient_le_one_of_fibre_span e m hm (hfib m hm) hCA

/-- **LEAF 3 — DEGREE-ZERO BASE CHANGE AT A CLOSED POINT, SURJECTIVE HALF** (Hartshorne
III.12.11(a) in degree `0`, EGA III 7.8.6): for every maximal ideal `𝔪` of `R = Γ(S, ⊤)` the
map `R/𝔪 ⟶ A/𝔪A` is SURJECTIVE, i.e. `A = R + 𝔪A`.

**PROVEN** (2026-07-28) — the cohomology and base change it used to carry now lives one level
down, in `rank_quotient_appTop_le_one_of_isIso_appTop_fiber` immediately above, whose
docstring holds the obstruction analysis, the pin re-check and the continuation plan.  What
is left here is linear algebra over the field `R/𝔪`: the leaf bounds `dim_{R/𝔪} A/𝔪A ≤ 1`,
`comap_map_appTop_eq_of_isIso_appTop_fiber` gives the injection `R/𝔪 ↪ A/𝔪A`, and an
injective map into a space of dimension at most one from a nonzero space is onto.

Equivalently — and this is the form to attack, in the leaf rather than here — the degree-zero
comparison map

  `A ⊗_R κ(s)  =  A/𝔪A  ⟶  H⁰(X_s, 𝒪_{X_s})  =  Γ(f.fiber s, ⊤)`

is INJECTIVE, where `s ∈ S` is the point cut out by `𝔪`.  Indeed that map is a `κ(s)`-algebra
map, the composite `κ(s) = R/𝔪 ⟶ A/𝔪A ⟶ Γ(X_s, ⊤)` is `(f.fiberToSpecResidueField s).appTop`
(by `Scheme.Hom.fiber_fac` applied to global sections), and `h s` says that composite is an
isomorphism; so `R/𝔪 ⟶ A/𝔪A` is surjective exactly when `A/𝔪A ⟶ Γ(X_s, ⊤)` is injective.

**FAITHFULNESS.**  `h` cannot be dropped: without it `h⁰` jumps and `A/𝔪A` is strictly bigger
than `κ(s)` where it does.  `[Flat f]` cannot be dropped either — it is the hypothesis of
III.12.11.  Maximality of `𝔪` IS used, twice: it makes `R/𝔪` a field, which is what turns
"dimension at most one plus a nonzero vector" into surjectivity, and it makes `κ(s) = R/𝔪`,
which is what makes the leaf's bound the right one.  It is also all the Nakayama assembly
downstream consumes. -/
theorem surjective_quotientMap_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop)
    (m : Ideal ↥Γ(S, ⊤)) (hm : m.IsMaximal) :
    Function.Surjective (Ideal.quotientMap (I := m)
      (Ideal.map f.appTop.hom m) f.appTop.hom Ideal.le_comap_map) := by
  haveI : m.IsMaximal := hm
  letI : Field (↥Γ(S, ⊤) ⧸ m) := Ideal.Quotient.field m
  letI : Algebra (↥Γ(S, ⊤) ⧸ m) (↥Γ(X, ⊤) ⧸ Ideal.map f.appTop.hom m) :=
    (Ideal.quotientMap (I := m) (Ideal.map f.appTop.hom m) f.appTop.hom
      Ideal.le_comap_map).toAlgebra
  -- The injective half of degree-zero base change: lying over, already proven above.
  have hinj : Function.Injective (Ideal.quotientMap (I := m)
      (Ideal.map f.appTop.hom m) f.appTop.hom Ideal.le_comap_map) :=
    Ideal.quotientMap_injective'
      (comap_map_appTop_eq_of_isIso_appTop_fiber f h m hm.isPrime).le
  haveI : Nontrivial (↥Γ(X, ⊤) ⧸ Ideal.map f.appTop.hom m) := hinj.nontrivial
  -- The leaf: `A/𝔪A` is at most a line over `R/𝔪`.
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp
    (rank_quotient_appTop_le_one_of_isIso_appTop_fiber f h m hm)
  obtain ⟨c, hc⟩ := hv₀ 1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hc
    exact zero_ne_one hc
  intro y
  obtain ⟨r, hr⟩ := hv₀ y
  refine ⟨r * c⁻¹, ?_⟩
  have key : algebraMap (↥Γ(S, ⊤) ⧸ m) (↥Γ(X, ⊤) ⧸ Ideal.map f.appTop.hom m) (r * c⁻¹) = y := by
    rw [Algebra.algebraMap_eq_smul_one, ← hc, smul_smul, mul_assoc, inv_mul_cancel₀ hc0,
      mul_one, hr]
  simpa [RingHom.algebraMap_toAlgebra] using key

/-- **LEAF 3 — DEGREE-ZERO BASE CHANGE AT A CLOSED POINT** (Hartshorne III.12.11(a) in degree
`0`, EGA III 7.8.6): for every maximal ideal `𝔪` of `R = Γ(S, ⊤)`, the induced map
`R/𝔪 ⟶ A/𝔪A` is bijective.  **PROVEN** (2026-07-28) over its surjective half; the injective
half is `comap_map_appTop_eq_of_isIso_appTop_fiber` above and needs only that `h` forces `f`
to be surjective, so this leaf's remaining content is entirely in
`surjective_quotientMap_appTop_of_isIso_appTop_fiber`.

This is the *only* place the fibrewise hypothesis enters the final theorem, and it enters
through the identification `A/𝔪A = (f_*𝒪_X) ⊗_R κ(s) ≅ H⁰(X_s, 𝒪_{X_s})` of degree-zero base
change, where `s ∈ S` is the closed point cut out by `𝔪` and `κ(s) = R/𝔪`.  Under that
identification the map `R/𝔪 ⟶ A/𝔪A` *is* `(f.fiberToSpecResidueField s).appTop`, which `h s`
says is an isomorphism.

Only maximal ideals appear because that is all the Nakayama assembly consumes; the base-change
theorem of course gives the statement at every point.

**FAITHFULNESS.**  The two halves are separately load-bearing and separately used:
surjectivity drives Nakayama on the cokernel, and injectivity is what puts `ker φ` inside the
Jacobson radical.  Note also that `h` forces every fibre to be **nonempty** — for `X_s = ∅`
one has `Γ(X_s, ⊤) = 0` and a field never maps isomorphically to the zero ring — which is
correct and intended, since `𝒪_S ⟶ f_*𝒪_X` is not an isomorphism over a point missed by `f`;
that observation is now a lemma, `surjective_of_isIso_appTop_fiber`. -/
theorem bijective_quotientMap_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ m : Ideal ↥Γ(S, ⊤), m.IsMaximal →
      Function.Bijective (Ideal.quotientMap (I := m)
        (m.map (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤))) (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤))
        Ideal.le_comap_map) := fun m hm =>
  ⟨Ideal.quotientMap_injective'
      (comap_map_appTop_eq_of_isIso_appTop_fiber f h m hm.isPrime).le,
    surjective_quotientMap_appTop_of_isIso_appTop_fiber f h m hm⟩

/-- **LEAF 2 — `f_*𝒪_X` IS FLAT OVER THE BASE** (Hartshorne III.12.11(b) in degree `0`,
EGA III 7.8.6; the "constant `h⁰` ⟹ locally free" half of cohomology and base change) —
**PROVEN** (2026-07-28), and NOT by III.12.11(b).

**The re-cut, and why it is sound.**  Over an affine base the conclusion is `Module.Flat R A`
for `A = Γ(X, ⊤)`, and the *only* consumer of it in this file is
`isIso_appTop_of_isIso_appTop_fiber`, which uses it to get `φ = f.appTop` INJECTIVE (through
`injective_algebraMap_of_flat_of_ker_le_jacobson`).  But injectivity of `φ` is available far
more cheaply, from flatness of the MORPHISM rather than of the module: `h` makes `f`
surjective (`surjective_of_isIso_appTop_fiber`), a flat surjective morphism is faithfully flat
on every stalk, and that forces `Γ(S, ⊤) ⟶ Γ(X, ⊤)` to be injective
(`injective_appTop_of_flat_of_surjective`).  Together with surjectivity of `φ` — Nakayama on
the cokernel, from `module_finite_appTop_of_isProper` and
`bijective_quotientMap_appTop_of_isIso_appTop_fiber` — that makes `φ` BIJECTIVE, so `A ≃ₗ[R] R`
and flatness is immediate.

So this leaf is now a corollary of leaf 1 and leaf 3 rather than a second theory build, and
III.12.11(b) is not needed anywhere in this development.  The logical cost is that leaf 2 now
depends on leaf 3; there is no circularity, since leaf 3's proof does not mention flatness of
`A` over `R`.  The mathematical cost is nil: the classical statement "`f_*𝒪_X` is locally free
of rank 1" is strictly stronger than `Module.Flat R A`, but nothing here consumes the
difference.

**FAITHFULNESS — `h` cannot be dropped.**  Without it the statement is false: `h⁰` is only
upper semicontinuous along a proper flat family, and where it jumps `f_*𝒪_X` is not locally
free.  `[Flat f]` cannot be dropped either — it is what makes the stalk maps faithfully flat,
and it is the hypothesis of III.12.11 itself.  Note the route deliberately avoids GRAUERT
(III.12.9), which would demand `S` reduced; the bases fed in here are arbitrary. -/
theorem module_flat_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.Flat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  show Module.Flat ↥Γ(S, ⊤) ↥Γ(X, ⊤)
  haveI : Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_finite_appTop_of_isProper f h
  haveI := surjective_of_isIso_appTop_fiber f h
  have hsurj : Function.Surjective (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) := by
    refine surjective_algebraMap_of_finite_of_forall_isMaximal ?_
    intro mm hmm a
    obtain ⟨x, hx⟩ :=
      (bijective_quotientMap_appTop_of_isIso_appTop_fiber f h mm hmm).2 (Ideal.Quotient.mk _ a)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨r, ?_⟩
    rw [Ideal.quotientMap_mk] at hx
    exact (Ideal.Quotient.eq.mp hx.symm)
  have hinj : Function.Injective (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) :=
    injective_appTop_of_flat_of_surjective f
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective (Algebra.linearMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) ⟨hinj, hsurj⟩).symm

/-- **COHOMOLOGY AND BASE CHANGE IN DEGREE ZERO: `𝒪_S ⟶ f_*𝒪_X` IS AN ISOMORPHISM AS SOON AS
IT IS ONE ON EVERY FIBRE** — **PROVEN** (2026-07-28) over the three leaves above, by the
commutative-algebra assembly in this file (Hartshorne III.12.11, Grauert, Stacks 0E0L /
EGA III 7.8.6).

Note what is *not* here: no geometric connectedness, no geometric reducedness.  Those enter
only through the hypothesis `h`, discharged by `isIso_appTop_of_isProper_over_field` above.
What is left is exactly the classical cohomology-and-base-change statement, with the fibre
input abstracted away.

**THE ROUTE, in the vocabulary `[IsAffine S]` provides.**  Put `R := Γ(S, ⊤)`,
`A := Γ(X, ⊤)`, `φ := f.appTop : R ⟶ A`.  Three inputs give `φ` bijective:

1. *`A` is a finite `R`-module* — `module_finite_appTop_of_isProper`, the finiteness theorem
   for a proper morphism.  (An earlier version of this docstring asked for finite
   *presentation*; the injectivity argument below does not need it, see
   `injective_algebraMap_of_flat_of_ker_le_jacobson`.)
2. *`A` is `R`-flat* — `module_flat_appTop_of_isIso_appTop_fiber`, now **PROVEN**.  This is
   where `Flat f` enters, but NOT through III.12.11(b): `Flat f` plus surjectivity of `f`
   makes every stalk map faithfully flat, hence `φ` injective, and with input 3 that already
   makes `φ` bijective, so `A ≃ₗ[R] R` is flat.  Input 2 is therefore a *consequence* of
   inputs 1 and 3 here, kept as a separate declaration only because the commutative-algebra
   assembly below is stated in terms of it.
3. *For every maximal ideal `𝔪 ⊂ R`, `R/𝔪 ⟶ A/𝔪A` is bijective* —
   `bijective_quotientMap_appTop_of_isIso_appTop_fiber`, degree-zero base change, and the
   only consumer of the hypothesis `h`.  Its injective half is proven (lying over); its
   surjective half is `surjective_quotientMap_appTop_of_isIso_appTop_fiber`, the one open
   leaf of this cluster.

Given those, `φ` is surjective by Nakayama applied to `coker φ` (finitely generated, and zero
modulo every maximal ideal), and injective because flatness plus the equational criterion
turns `k • (1 : A) = 0` into `k * e = 0` for a *unit* `e` — the kernel lies in the Jacobson
radical by the injective half of input 3.  All of that is proven above; nothing of it is
geometric.

**Why `[IsAffine S]` costs nothing**: `isIso_appTop_of_isIso_app_affineOpens` above reduces the
general base to this one, because `f.app U` is the component at `U` of the sheaf map
`𝒪_S ⟶ f_*𝒪_X` and the affine opens are a basis of `S`.  It is what makes `R` and `A` honest
rings and the argument above expressible at all.

**FAITHFULNESS.**  Flatness is essential — without it `h⁰` jumps and the conclusion is false
(blow up a point on a surface and the exceptional fibre still has `H⁰ = κ(s)`, but a
non-flat family does not have `f_*𝒪 = 𝒪`).  The hypothesis `h` also silently forces every
fibre to be *nonempty*: for `X_s = ∅` one has `Γ(X_s, ⊤) = 0`, and a field never maps
isomorphically to the zero ring.  That is correct and intended — `𝒪_S ⟶ f_*𝒪_X` is not an
isomorphism over a point missed by `f`.

**PIN STATE, checked rather than assumed (2026-07-27, re-checked at `122c02b0`).**  `Mathlib`
has no higher direct images of quasi-coherent sheaves, no `Rⁱf_*`, no semicontinuity, no
cohomology-and-base-change: `grep -rn 'higherDirectImage\|directImage\|
cohomologyAndBaseChange' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/ ~/cs/FLT/FLT/
Fermat/` returns zero hits.  So the leaves above are a theory build and not a missing-lemma
hunt.  **That grep is phrased in THIS project's vocabulary and so can only ever confirm
absence; it was re-run in MATHLIB's vocabulary on 2026-07-28** (`QuasiCoherent`,
`SheafCohomology`, `Tor`, `Scheme.Modules`) and the conclusion stands — see the pin re-check
in `rank_quotient_appTop_le_one_of_isIso_appTop_fiber`, which also records the two things
that DO exist now and are the right place to build on: `AlgebraicGeometry.Scheme.Modules`
with its `pushforward`/`pullback` adjunction (degree zero only), and abstract sheaf
cohomology on sites (`Ext` in a sheaf category, with no Čech comparison and no finiteness).  What mathlib *does* supply, and what an earlier version of this docstring did not
record, is `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`,
`AlgebraicGeometry.isField_of_universallyClosed` and
`AlgebraicGeometry.finite_appTop_of_universallyClosed`
(`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`) — the last two under `[IsIntegral X]`. -/
theorem isIso_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    IsIso f.appTop := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  haveI : Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_finite_appTop_of_isProper f h
  haveI : Module.Flat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_flat_appTop_of_isIso_appTop_fiber f h
  have hb := bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap
    (bijective_quotientMap_appTop_of_isIso_appTop_fiber f h)
  rw [RingHom.algebraMap_toAlgebra] at hb
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hb

/-! ### `𝒪_S = p_*𝒪_X` makes `p` an EPIMORPHISM

This is what makes the factorization through the base *unique* for an arbitrary — not
necessarily affine — target, and it is exactly what the gluing step of the rigidity lemma
needs: two local factorizations over `V i` and `V j` agree on the overlap because there is
at most one.

Two ingredients, and both are consequences of the pushforward hypothesis alone:

* `surjective_of_hasUniversallyTrivialPushforward` — the UNIVERSAL form forces `p` to be
  surjective, by base change along `Spec κ(s) ⟶ S`: an empty fibre would give
  `κ(s) ≅ Γ(∅, ⊤) = 0`, and `κ(s)` is a field.  This is the only place the *universal*
  form is used for anything other than an honest base change, and it is why
  `HasTrivialPushforward` alone will not do: `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ 0}` by Hartogs, and
  that `j` is not surjective.
* `eq_of_comp_eq_of_hasTrivialPushforward` — surjectivity plus `IsIso (p.app U)` at every
  open `U` upgrades the affine-target injectivity `eq_of_comp_eq_of_isAffine` to an
  arbitrary target, by covering `Z` with affine opens: surjectivity makes the two
  candidate morphisms agree on POINTS, hence have the same preimage of each affine open,
  and on that preimage the affine case applies to `p ∣_ (c₁ ⁻¹ᵁ U)`. -/

/-- Global sections of an empty scheme form the zero ring — `⊤ = ⊥` there, and
`Subsingleton Γ(X, ⊥)` is a `Mathlib` instance (the sheaf condition over the empty
cover). -/
theorem subsingleton_globalSections_of_isEmpty (W : Scheme.{u}) [IsEmpty W] :
    Subsingleton Γ(W, ⊤) := by
  have h : (⊤ : W.Opens) = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  rw [h]
  infer_instance

/-- **`𝒪_S = p_*𝒪_X` UNIVERSALLY FORCES `p` TO BE SURJECTIVE** (PROVEN).

Base-change `p` along `S.fromSpecResidueField s : Spec κ(s) ⟶ S`, whose range is `{s}`.
If `s` were not in the range of `p` the two ranges would be disjoint, so the fibre
product would be EMPTY (`Scheme.isEmpty_pullback_iff`) and its ring of global sections
would be the zero ring; but the hypothesis makes `(pullback.snd p _).app ⊤` an
isomorphism onto it from `Γ(Spec κ(s), ⊤) ≅ κ(s)`, forcing the field `κ(s)` to be
subsingleton.

Note this genuinely needs the UNIVERSAL form: `HasTrivialPushforward` alone does not
imply surjectivity — Hartogs gives `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ {0}}` for the inclusion `j` of
the complement of a codimension-two point. -/
theorem surjective_of_hasUniversallyTrivialPushforward {p : X ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) : Surjective p := by
  constructor
  intro s
  by_contra hs
  have h : HasTrivialPushforward (pullback.snd p (S.fromSpecResidueField s)) :=
    hpush (pullback.fst p _) _ (pullback.snd p _)
      (IsPullback.of_hasPullback p (S.fromSpecResidueField s)).flip
  haveI : IsEmpty ↥(pullback p (S.fromSpecResidueField s)) := by
    rw [Scheme.isEmpty_pullback_iff, Scheme.range_fromSpecResidueField]
    simpa [Set.disjoint_singleton_right] using hs
  haveI := h ⊤
  haveI : Subsingleton Γ(pullback p (S.fromSpecResidueField s), ⊤) :=
    subsingleton_globalSections_of_isEmpty _
  haveI : Subsingleton Γ(Spec (S.residueField s), ⊤) :=
    (asIso ((pullback.snd p (S.fromSpecResidueField s)).app
      ⊤)).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr inferInstance
  haveI : Subsingleton (S.residueField s) :=
    (Scheme.ΓSpecIso (CommRingCat.of (S.residueField s))).commRingCatIsoToRingEquiv.toEquiv
      |>.subsingleton_congr.mp inferInstance
  exact false_of_nontrivial_of_subsingleton (S.residueField s)

/-- `IsIso (g.app V)` for every open transfers to the RESTRICTED morphism `g ∣_ V`, whose
`appTop` is `g.app (V.ι ''ᵁ ⊤)` composed with an `eqToHom`-induced isomorphism.

Stated in this direction — the composite form first, then `rw [← morphismRestrict_appTop]`
— on purpose: rewriting FORWARDS with `morphismRestrict_appTop` produces a goal that is
not type-correct at `instances` transparency, so instance synthesis then fails on the
`eqToHom` factor even when every ingredient is available. -/
theorem HasTrivialPushforward.isIso_appTop_morphismRestrict {g : X ⟶ S}
    (hg : HasTrivialPushforward g) (V : S.Opens) : IsIso (g ∣_ V).appTop := by
  have h2 : IsIso (g.app (V.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage g V ⊤)).op) := by
    haveI := hg (V.ι ''ᵁ ⊤)
    infer_instance
  rwa [← morphismRestrict_appTop] at h2

/-- **A SURJECTIVE MORPHISM WITH `𝒪_S = g_*𝒪_X` IS AN EPIMORPHISM OF SCHEMES** (PROVEN),
i.e. `(g ≫ ·)` is injective on morphisms into an ARBITRARY scheme `Z`.

`eq_of_comp_eq_of_isAffine` is this statement for affine `Z`; the passage to a general
`Z` is local on `Z` and uses surjectivity twice:

* surjectivity makes `c₁` and `c₂` agree on POINTS, so `c₁ ⁻¹ᵁ U = c₂ ⁻¹ᵁ U` for every
  open `U ⊆ Z` — without which the two restrictions would not even have a common source;
* on `V := c₁ ⁻¹ᵁ U` with `U` an affine open around `c₁ s`, the affine case applies to
  `g ∣_ V`, whose `appTop` is an isomorphism by
  `HasTrivialPushforward.isIso_appTop_morphismRestrict`.

`Scheme.hom_ext_of_forall` then assembles the local equalities. -/
theorem eq_of_comp_eq_of_hasTrivialPushforward {g : X ⟶ S} (hg : HasTrivialPushforward g)
    [Surjective g] {c₁ c₂ : S ⟶ Z} (h : g ≫ c₁ = g ≫ c₂) : c₁ = c₂ := by
  have hbase : ∀ s : S, c₁.base s = c₂.base s := by
    intro s
    obtain ⟨x, rfl⟩ := g.surjective s
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  have hpre : ∀ U : Z.Opens, c₁ ⁻¹ᵁ U = c₂ ⁻¹ᵁ U := by
    intro U
    ext s
    simp [hbase s]
  refine Scheme.hom_ext_of_forall c₁ c₂ fun s => ?_
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Z) (x := c₁.base s) (U := ⊤) (by trivial)
  haveI : IsAffine U.toScheme := hU
  refine ⟨c₁ ⁻¹ᵁ U, hmem, ?_⟩
  have e₂ : (c₁ ⁻¹ᵁ U) ≤ c₂ ⁻¹ᵁ U := (hpre U) ▸ le_rfl
  haveI : IsIso (g.resLE (c₁ ⁻¹ᵁ U) (g ⁻¹ᵁ (c₁ ⁻¹ᵁ U)) le_rfl).appTop := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hg.isIso_appTop_morphismRestrict _
  have key : c₁.resLE U (c₁ ⁻¹ᵁ U) le_rfl = c₂.resLE U (c₁ ⁻¹ᵁ U) e₂ := by
    refine eq_of_comp_eq_of_isAffine
      (p := g.resLE (c₁ ⁻¹ᵁ U) (g ⁻¹ᵁ (c₁ ⁻¹ᵁ U)) le_rfl) ?_
    rw [Scheme.Hom.resLE_comp_resLE, Scheme.Hom.resLE_comp_resLE]
    congr 1
  have := congrArg (fun t => t ≫ U.ι) key
  simpa only [Scheme.Hom.resLE_comp_ι] using this

/-- **THE PROJECTION `X ×_S Y ⟶ Y` IS AN EPIMORPHISM** (PROVEN) when
`HasUniversallyTrivialPushforward p`.

`HasUniversallyTrivialPushforward` is stable under base change, so it passes from `p` to
`pullback.snd p q`, which is then surjective and has trivial pushforward — the two
hypotheses of `eq_of_comp_eq_of_hasTrivialPushforward`.

This is the uniqueness that `exists_comp_snd_eq_of_isAffine` records as an `∃!` in the
affine case, now available for an arbitrary target; it is what makes the local
factorizations of the rigidity lemma agree on overlaps. -/
theorem eq_of_comp_snd_eq {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {c₁ c₂ : Y ⟶ Z}
    (h : pullback.snd p q ≫ c₁ = pullback.snd p q ≫ c₂) : c₁ = c₂ := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  exact eq_of_comp_eq_of_hasTrivialPushforward hu.hasTrivialPushforward h

/-! ### The theorem -/

/-- **`Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY
CONNECTED AND REDUCED FIBRES, OVER AN AFFINE BASE** — **PROVEN** (2026-07-27) over the two
leaves above, by the one-line assembly they were cut for: every fibre
`f.fiberToSpecResidueField s : X_s ⟶ Spec κ(s)` is a base change of `f`, hence proper,
geometrically connected and geometrically reduced over the field `κ(s)`, so
`isIso_appTop_of_isProper_over_field` discharges the fibrewise hypothesis of
`isIso_appTop_of_isIso_appTop_fiber`.

This is the missing classical input behind the whole Jacobian half of this development:
`isAdditiveOn_of_post_zero` (relative rigidity) and `exists_albaneseOfCurve` reduce to it,
which is why it is stated here, once, in the shim tree rather than inside a modular-curve
file.

**CORRECTION 2026-07-29 — this paragraph used to name
`universal_jacobianBaseChangeAj` here as well, and that was FALSE.**  `X0.lean`'s own
"GATE VERDICT" already recorded the refutation: coherent pushforward buys RIGIDITY
(Mumford *AV* §4), and rigidity is not what the base-change direction needs.  What it
needs is REPRESENTABILITY of the rigidified relative Picard functor and compatibility of
`Pic⁰` with base change (FGA 232 / Artin), a strictly larger theory that `f_*𝒪_X = 𝒪_S`
does not deliver.  `universal_jacobianBaseChangeAj` is in any case PROVEN as of
2026-07-29, over the single leaf `isIso_jacobianBaseChangeComparison` in `X0.lean` — and
that leaf is gated on representability, NOT on this file.  Do not dispatch it here.

**The instance plumbing, for the record.**  `f.fiberToSpecResidueField s` is by definition
`pullback.snd f (S.fromSpecResidueField s)`, and mathlib already carries
`GeometricallyConnected (f.fiberToSpecResidueField s)` and
`GeometricallyReduced (f.fiberToSpecResidueField s)` as instances; only `IsProper` has to be
produced by hand, from `MorphismProperty.pullback_snd`. -/
theorem isIso_appTop_of_isProper_of_flat_of_isAffine (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    IsIso f.appTop := by
  refine isIso_appTop_of_isIso_appTop_fiber f fun s => ?_
  haveI : IsProper (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact isIso_appTop_of_isProper_over_field (Field.toIsField _) _

/-- **`Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY
CONNECTED AND REDUCED FIBRES**, over an arbitrary base — **PROVEN** over the affine-base leaf
`isIso_appTop_of_isProper_of_flat_of_isAffine` above.

The base is made affine by `isIso_appTop_of_isIso_app_affineOpens`: `f.app U` is the component
at `U` of the sheaf map `𝒪_S ⟶ f_*𝒪_X`, so it is enough to treat the affine opens, which are a
basis of `S`.  Over an affine open `U`, `isPullback_morphismRestrict` exhibits `f ∣_ U` as a
base change of `f`, so it inherits all five hypotheses, and `morphismRestrict_appTop` together
with `Scheme.Opens.ι_image_top` identifies `(f ∣_ U).appTop` with `f.app U` up to the
`eqToHom`-induced isomorphism.

So the affine reduction and the `universally`/`∀ U` bookkeeping of
`hasUniversallyTrivialPushforward_of_isProper_of_flat` below are all discharged mechanically:
the only remaining mathematics is the global-sections computation over an **affine** base. -/
theorem isIso_appTop_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    IsIso f.appTop := by
  refine isIso_appTop_of_isIso_app_affineOpens f fun U hU => ?_
  haveI : IsAffine U := hU
  haveI : IsProper (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹IsProper f›
  haveI : Flat (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹Flat f›
  haveI : LocallyOfFinitePresentation (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹LocallyOfFinitePresentation f›
  haveI : GeometricallyConnected (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹GeometricallyConnected f›
  haveI : GeometricallyReduced (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹GeometricallyReduced f›
  haveI hiso : IsIso (f.app (U.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) := by
    rw [← morphismRestrict_appTop]
    exact isIso_appTop_of_isProper_of_flat_of_isAffine (f ∣_ U)
  haveI h2 := (isIso_comp_right_iff _ _).mp hiso
  rwa [U.ι_image_top] at h2

/-- **`f_*𝒪_X = 𝒪_S`, UNIVERSALLY, FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY CONNECTED
AND REDUCED FIBRES** — PROVEN over `isIso_appTop_of_isProper_of_flat`.

Both quantifiers are pure bookkeeping and are discharged here, once:

* *the base change*: `IsProper`, `Flat`, `LocallyOfFinitePresentation`,
  `GeometricallyConnected` and `GeometricallyReduced` all carry
  `MorphismProperty.IsStableUnderBaseChange` instances in `Mathlib`, so every leg of a
  pullback square over `f` inherits all five;
* *the open `U ⊆ S`*: `isPullback_morphismRestrict` exhibits `f ∣_ U` as a base change of
  `f`, so it inherits all five as well, and `morphismRestrict_appTop` together with
  `Scheme.Opens.ι_image_top` identifies `(f ∣_ U).appTop` with `f.app U` up to the
  `eqToHom`-induced isomorphism `X.presheaf.map (eqToHom …).op`.

This is why the remaining leaf may be stated at `⊤` over a *fixed* `f`: no generality is
lost, and a cohomological argument that had to thread `universally` through itself would be
considerably worse. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    HasUniversallyTrivialPushforward f := by
  intro X' S' i₁ i₂ f' hpb
  haveI : IsProper f' := MorphismProperty.of_isPullback hpb.flip ‹IsProper f›
  haveI : Flat f' := MorphismProperty.of_isPullback hpb.flip ‹Flat f›
  haveI : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback hpb.flip ‹LocallyOfFinitePresentation f›
  haveI : GeometricallyConnected f' :=
    MorphismProperty.of_isPullback hpb.flip ‹GeometricallyConnected f›
  haveI : GeometricallyReduced f' :=
    MorphismProperty.of_isPullback hpb.flip ‹GeometricallyReduced f›
  intro U
  haveI : IsProper (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip ‹IsProper f'›
  haveI : Flat (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip ‹Flat f'›
  haveI : LocallyOfFinitePresentation (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹LocallyOfFinitePresentation f'›
  haveI : GeometricallyConnected (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹GeometricallyConnected f'›
  haveI : GeometricallyReduced (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹GeometricallyReduced f'›
  haveI hiso : IsIso (f'.app (U.ι ''ᵁ ⊤) ≫
      X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f' U ⊤)).op) := by
    rw [← morphismRestrict_appTop]
    exact isIso_appTop_of_isProper_of_flat (f' ∣_ U)
  haveI h2 := (isIso_comp_right_iff _ _).mp hiso
  rwa [U.ι_image_top] at h2

/-- **`f_*𝒪_X = 𝒪_S` for a PROPER SMOOTH morphism with geometrically connected fibres**
(PROVEN, over the single leaf above).

This is the form every consumer in this development uses, because both an abelian scheme
(`AbelianSchemeStruct`, whose fields are `proper`, `smooth`, `connected`) and a smooth
proper curve are handed over as smooth rather than as flat with reduced fibres.  The
missing implications `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` are
`Mathlib` instances, and geometric reducedness comes from
`AlgebraicGeometry.GeometricallyReduced.of_smooth` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` — see the module
docstring for why this file no longer states that fact itself. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_smooth (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
    HasUniversallyTrivialPushforward f :=
  haveI := GeometricallyReduced.of_smooth f
  hasUniversallyTrivialPushforward_of_isProper_of_flat f

/-! ### The corollary the rigidity lemma consumes: factoring an affine-valued morphism -/

/-- **AN AFFINE-VALUED MORPHISM OUT OF `X` FACTORS UNIQUELY THROUGH `S`** (PROVEN).

If `𝒪_S ⟶ p_*𝒪_X` is an isomorphism then for every ring `R` the map
`(S ⟶ Spec R) → (X ⟶ Spec R)`, `c ↦ p ≫ c`, is a bijection.

This is the promised short corollary of `p_*𝒪_X = 𝒪_S`, and it is pure `Γ ⊣ Spec`
formalism with no geometry in it: under `ΓSpec.adjunction` the map `c ↦ p ≫ c` is
conjugate to `g ↦ Scheme.Γ.rightOp.map p ≫ g` on hom-sets, and `Scheme.Γ.rightOp.map p`
is `(p.appTop).op`, an isomorphism precisely because `HasTrivialPushforward p` says
`p.app ⊤` is one.  No properness, flatness or connectedness is used — the *only* input is
the pushforward hypothesis, which is why every geometric difficulty in the rigidity lemma
sits in reducing to an affine target rather than in this step.

Note it needs only `HasTrivialPushforward`, not the universal form; the universal form is
what lets the CALLER apply it after a base change. -/
theorem existsUnique_comp_eq_of_hasTrivialPushforward {p : X ⟶ S}
    (hp : HasTrivialPushforward p) {R : CommRingCat.{u}} (m : X ⟶ Spec R) :
    ∃! c : S ⟶ Spec R, m = p ≫ c := by
  haveI : IsIso p.appTop := hp ⊤
  haveI : IsIso (Scheme.Γ.rightOp.map p) := by
    show IsIso ((p.appTop).op)
    infer_instance
  set eX := ΓSpec.adjunction.homEquiv X (Opposite.op R) with heX
  set eS := ΓSpec.adjunction.homEquiv S (Opposite.op R) with heS
  have hfun : (fun c : S ⟶ Spec R => p ≫ c)
      = fun c => eX (Scheme.Γ.rightOp.map p ≫ eS.symm c) := by
    funext c
    rw [heX, heS, ΓSpec.adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    rfl
  have hcomp : Function.Bijective
      (fun g : Scheme.Γ.rightOp.obj S ⟶ Opposite.op R => Scheme.Γ.rightOp.map p ≫ g) := by
    constructor
    · intro a b hab
      simpa using congrArg (fun t => inv (Scheme.Γ.rightOp.map p) ≫ t) hab
    · intro b
      exact ⟨inv (Scheme.Γ.rightOp.map p) ≫ b, by simp⟩
  have hbij : Function.Bijective (fun c : S ⟶ Spec R => p ≫ c) := by
    rw [hfun]
    exact eX.bijective.comp (hcomp.comp eS.symm.bijective)
  obtain ⟨c, hc⟩ := hbij.surjective m
  exact ⟨c, hc.symm, fun y hy => hbij.injective (by simpa using hy.symm.trans hc.symm)⟩

/-- **THE RIGIDITY LEMMA FOR AN AFFINE TARGET** (PROVEN).

With `Z = Spec R` the rigidity lemma needs **none** of its geometric hypotheses: no
contracted slice `σ`, no `GeometricallyConnected q`, no separatedness of `r`, not even
properness of `p`.  The factorization is immediate from
`existsUnique_comp_eq_of_hasTrivialPushforward` applied to `pullback.snd p q`, which is a
base change of `p` and therefore inherits `HasUniversallyTrivialPushforward` — this is
exactly what the universal form of the hypothesis is for.  The factorization is moreover
UNIQUE, which the general statement does not record.

**This delimits the general leaf precisely.**  The whole content of
`exists_comp_snd_eq_of_slice_const` is the reduction to an affine target, and that
reduction is genuinely necessary: with `S = Spec k`, `X = Spec k`, `Y = Z = ℙ¹` and
`m = 𝟙` every hypothesis of the general statement holds, `d = 𝟙` is the factorization,
and `m` factors through no affine scheme at all.  So no globally-affine reduction can
exist and the passage must be LOCAL on `Y` — which is what drags in properness (a closed
image in `Y`), the contracted slice (a nonempty open where the image is affine) and
connectedness of `q` (to spread that open over all of `Y`). -/
theorem existsUnique_comp_snd_eq_of_spec {Y : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {R : CommRingCat.{u}}
    (m : pullback p q ⟶ Spec R) :
    ∃! d : Y ⟶ Spec R, m = pullback.snd p q ≫ d := by
  have h : hasTrivialPushforwardProperty.universally (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  exact existsUnique_comp_eq_of_hasTrivialPushforward
    (HasUniversallyTrivialPushforward.hasTrivialPushforward h) m

/-! ### The rigidity lemma -/

/-- **The slice `X ≅ X ×_S σ(S) ⊆ X ×_S Y` cut out by a section `σ` of `q`.**

`sliceIncl p q σ hσ` is the morphism `x ↦ (x, σ(p x))`.  It is a section of
`pullback.fst p q`, and it is the subscheme along which the rigidity lemma's hypothesis is
stated. -/
noncomputable def sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : X ⟶ pullback p q :=
  pullback.lift (𝟙 X) (p ≫ σ)
    (by rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

@[reassoc (attr := simp)]
theorem sliceIncl_fst {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : sliceIncl p q σ hσ ≫ pullback.fst p q = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceIncl_snd {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : sliceIncl p q σ hσ ≫ pullback.snd p q = p ≫ σ :=
  pullback.lift_snd _ _ _

/-- **RIGIDITY WITH AN AFFINE TARGET** (PROVEN).

`HasUniversallyTrivialPushforward p` base-changes along `q` to `HasTrivialPushforward` for
the projection `pullback.snd p q : X ×_S Y ⟶ Y`, and then
`HasTrivialPushforward.existsUnique_comp_eq` factors `m` through `Y` — uniquely.

**No section, no connectedness, no separatedness.**  None of `σ`, `hconst`,
`[GeometricallyConnected q]` or `[IsSeparated r]` appears: for an affine target the whole
statement is the pushforward hypothesis and nothing else.  That is what localises the
remaining content of the rigidity lemma onto the covering step.

The uniqueness is load-bearing downstream: it is what makes local factorizations over an
open cover of `Y` agree on overlaps (`exists_comp_snd_eq_of_open_cover`). -/
theorem exists_comp_snd_eq_of_isAffine {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) [IsAffine Z] (m : pullback p q ⟶ Z) :
    ∃! d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  have h : HasTrivialPushforward (pullback.snd p q) :=
    hpush (pullback.fst p q) q (pullback.snd p q) (IsPullback.of_hasPullback p q).flip
  obtain ⟨d, hd, hu⟩ := h.existsUnique_comp_eq m
  exact ⟨d, hd.symm, fun d' hd' => hu d' hd'.symm⟩

/-- **RIGIDITY WITH A TARGET AFFINE OVER THE BASE** (PROVEN) — the relative form of the
`Γ ⊣ Spec` corollary, obtained by a base change instead of by a relative `Spec`.

`Mathlib` has no relative `Spec` at this pin, so "affine over `S`" cannot be turned into a
sheaf of algebras and split off directly.  It does not need to be: an `S`-morphism
`m : X ×_S Y ⟶ Z` is the same thing as a `Y`-morphism `X ×_S Y ⟶ Y ×_S Z`, and *that*
target is an honest affine scheme as soon as `Y ×_S Z` is one — which is exactly what
"`Z` is affine over `S`" gives over an affine `Y`.  So the hypothesis is stated as
`[IsAffine (pullback q r)]`, which is what the proof needs and is implied by
`[IsAffine Y] [IsAffineHom r]`.

This is the form the classical proof consumes, and it is consumed by
`exists_comp_snd_eq_of_slice_const` below. -/
theorem exists_comp_snd_eq_of_isAffine_pullback {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p) [IsAffine (pullback q r)]
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  have hcomm : pullback.snd p q ≫ q = m ≫ r := by rw [hm, ← pullback.condition]
  obtain ⟨e, he⟩ :=
    (exists_comp_snd_eq_of_isAffine (q := q) hpush (pullback.lift _ _ hcomm)).exists
  refine ⟨e ≫ pullback.snd q r, ?_⟩
  rw [← Category.assoc, ← he, pullback.lift_snd]

/-- **The canonical map `X ×_S V ⟶ X ×_S Y` induced by an open subscheme `V ⊆ Y`.**

This is how "the restriction of `m` to the part of `X ×_S Y` lying over `V`" is written in
the two leaves below, without ever forming an open subscheme of `X ×_S Y`. -/
noncomputable def sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    pullback p (V.ι ≫ q) ⟶ pullback p q :=
  pullback.map p (V.ι ≫ q) p q (𝟙 X) V.ι (𝟙 S) (by simp) (by simp)

/-! ### Ranges: the two point-set facts the covering step needs

Everything in this block is PROVEN and axiom-clean.  It is stated here rather than inside
`exists_isAffineOver_cover_of_slice_const` because it is exactly the part of that leaf's
argument that a diagram chase on points CANNOT supply, and because it is reusable:

**the underlying set of a fibre product of schemes is NOT the fibre product of the
underlying sets.**  So "the fibre of `pullback.snd p q` over `σ.base s` is covered by the
slice" — which is what turns `hconst` (a statement about the slice) into a statement about a
whole fibre, and hence what makes `m ⁻¹ (Z ∖ U)` miss that fibre — is a real theorem and not
bookkeeping.  What supplies it is that `sliceIncl` is a BASE CHANGE of `σ`, together with
`Scheme.Pullback.range_map`: the range of a base change is the preimage of the range.

`sliceOverMap` below is `sliceOverOpen` generalised from an open immersion to an arbitrary
morphism, which is needed because the slice is the base change of the SECTION `σ : S ⟶ Y` —
an immersion, but not an open one. -/

/-- **The canonical map `X ×_S V ⟶ X ×_S Y` induced by an arbitrary `g : V ⟶ Y`.**
`sliceOverOpen p q V` is the special case `g = V.ι`, definitionally. -/
noncomputable def sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) : pullback p (g ≫ q) ⟶ pullback p q :=
  pullback.map p (g ≫ q) p q (𝟙 X) g (𝟙 S) (by simp) (by simp)

theorem sliceOverOpen_eq_sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (V : Y.Opens) : sliceOverOpen p q V = sliceOverMap p q V.ι :=
  rfl

@[reassoc (attr := simp)]
theorem sliceOverMap_fst {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    sliceOverMap p q g ≫ pullback.fst p q = pullback.fst p (g ≫ q) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem sliceOverMap_snd {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    sliceOverMap p q g ≫ pullback.snd p q = pullback.snd p (g ≫ q) ≫ g :=
  pullback.lift_snd _ _ _

/-- **THE RANGE OF `sliceOverMap` IS THE PREIMAGE OF THE RANGE OF `g`** (PROVEN), because
`sliceOverMap p q g` is the base change of `g` along `pullback.snd p q`. -/
theorem range_sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    Set.range (sliceOverMap p q g).base = (pullback.snd p q).base ⁻¹' Set.range g.base := by
  rw [sliceOverMap, Scheme.Pullback.range_map]
  simp

-- (`range_sliceOverOpen` is declared far BELOW, beside `isPullback_sliceOverOpen`.
-- Two branches proved it independently — this position and that one — and the lower
-- copy is the one every consumer in this file `rw`s with, so only it survives.
-- The statement is the same up to the `.base`/coercion spelling.)

section Slice

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)

/-- **The canonical isomorphism `X ≅ X ×_S S` supplied by the section `σ`.**

`σ ≫ q = 𝟙 S` makes `pullback p (σ ≫ q)` a pullback along an identity, hence a copy of `X`.
Composing it with `sliceOverMap p q σ` is `sliceIncl`, which is what exhibits the slice as
the base change of `σ`. -/
noncomputable def sliceIso : X ⟶ pullback p (σ ≫ q) :=
  pullback.lift (𝟙 X) p (by rw [Category.id_comp, hσ, Category.comp_id])

@[reassoc (attr := simp)]
theorem sliceIso_fst : sliceIso p q σ hσ ≫ pullback.fst p (σ ≫ q) = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceIso_snd : sliceIso p q σ hσ ≫ pullback.snd p (σ ≫ q) = p :=
  pullback.lift_snd _ _ _

instance : IsIso (sliceIso p q σ hσ) := by
  refine ⟨pullback.fst p (σ ≫ q), sliceIso_fst p q σ hσ, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sliceIso_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, sliceIso_snd, Category.id_comp, pullback.condition, hσ,
      Category.comp_id]

/-- **THE SLICE IS THE BASE CHANGE OF THE SECTION** (PROVEN). -/
theorem sliceIso_comp : sliceIso p q σ hσ ≫ sliceOverMap p q σ = sliceIncl p q σ hσ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sliceOverMap_fst, sliceIso_fst, sliceIncl_fst]
  · rw [Category.assoc, sliceOverMap_snd, sliceIso_snd_assoc, sliceIncl_snd]

/-! #### **THE SLICE IS EXACTLY THE PART OF `X ×_S Y` LYING OVER `σ(S)`** (PROVEN).

This is the fact the covering step turns on: because the fibre of `pullback.snd p q` over
`σ.base s` is entirely covered by the slice, `hconst` — which constrains `m` only on the
slice — pins `m` on that whole fibre, and so the closed set `m ⁻¹ (Z ∖ U)` misses it.

It is NOT a diagram chase: the underlying set of a fibre product of schemes is not the fibre
product of the underlying sets, and the fibre of `pullback.snd p q` over a point `y` is
`X ×_S Spec κ(y)`, which is larger than `X_{q y}` for a general `y`.  It is the fact that `σ`
is a SECTION — so that `κ(σ.base s) = κ(s)` — that collapses it, and that is exactly the
content of `sliceIncl` being a base change of `σ`. -/
-- (`range_sliceIncl` is declared far BELOW, beside `isPullback_sliceIncl`, for the same
-- reason as `range_sliceOverOpen` above: two branches proved it independently and the
-- lower copy is the one every consumer in this file `rw`s with.)

end Slice

/-- **`X ×_S V` IS THE PART OF `X ×_S Y` LYING OVER `V`** (PROVEN): the square

```
X ×_S V --sliceOverOpen--> X ×_S Y
   | snd                      | snd
   V --------- ι ---------->  Y
```

is cartesian.  Pasting: the outer rectangle obtained by adjoining `pullback.fst p q` and
`q` on the right is `pullback p (V.ι ≫ q)`, and the right-hand square is `X ×_S Y`, so
`IsPullback.of_bot` gives the left one.

Two consequences are used below: `sliceOverOpen` is an open immersion (base change of
`V.ι`), and `X ×_S V` is *the* fibre product `(X ×_S Y) ×_Y V`, which is how the
`sliceOverOpen`s are recognised as members of the pullback of an open cover of `Y`. -/
theorem isPullback_sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    IsPullback (sliceOverOpen p q V) (pullback.snd p (V.ι ≫ q)) (pullback.snd p q) V.ι := by
  refine (IsPullback.of_bot (h₁₁ := pullback.snd p (V.ι ≫ q)) (v₁₁ := sliceOverOpen p q V)
    (v₁₂ := V.ι) (h₂₁ := pullback.snd p q) (v₂₁ := pullback.fst p q) (v₂₂ := q) ?_ ?_
    (IsPullback.of_hasPullback p q).flip).flip
  · have e : sliceOverOpen p q V ≫ pullback.fst p q = pullback.fst p (V.ι ≫ q) := by
      simp [sliceOverOpen, pullback.map, pullback.lift_fst]
    rw [e]
    exact (IsPullback.of_hasPullback p (V.ι ≫ q)).flip
  · simp [sliceOverOpen, pullback.map, pullback.lift_snd]

instance {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    IsOpenImmersion (sliceOverOpen p q V) :=
  MorphismProperty.of_isPullback (isPullback_sliceOverOpen p q V).flip inferInstance

/-! ### The covering step, cut into the properness half and the connectedness half

The two halves of the covering step are separated here, and both are PROVEN:

1. *properness* — `isOpen_setOf_slice_mapsTo`: for a fixed open `U ⊆ Z`, the set of `y : Y`
   whose whole slice is mapped into `U` is OPEN.  This is the tube lemma, and it is exactly
   `IsProper p ⟹ IsClosedMap (pullback.snd p q)` (properness is stable under base change);
   the complement of that set is the image of the closed `m ⁻¹(Z ∖ U)`.
2. *connectedness* — the clopen argument, assembled here as
   `mem_sliceGoodLocus_of_slice_const` over `isClosed_sliceContractedLocus_fiber`, the
   semicontinuity statement proven in the section after next.

The assembly runs on two loci, which the lemmas below prove to be THE SAME SET:

* `sliceGoodLocus` — the set of `y` at which the leaf's conclusion holds.  It is open by
  construction (`isOpen_sliceGoodLocus`), since its defining witness `V` is a
  neighbourhood of every one of its points.
* `sliceContractedLocus` — the set of `y` whose slice `m` maps to a SINGLE POINT of `Z`.

`sliceContractedLocus ⊆ sliceGoodLocus` is the properness half packaged
(`mem_sliceGoodLocus_of_mem_sliceContractedLocus`): the single image point `z` sits in an
affine open `U` lying over an affine `S₀ ∋ q y`, the tube lemma shrinks `Y` to an open on
which the whole slice lands in `U`, and an affine `V` inside that open and inside
`q ⁻¹ᵁ S₀` makes `V ×_S U = V ×_{S₀} U` affine (`isAffine_pullback_ι_comp`).  The reverse
inclusion `sliceContractedLocus_of_sliceGoodLocus` is the affine-target rigidity lemma
already proven above: over `V` the map factors as `pullback.snd ≫ d`, so each slice over
`V` goes to the single point `d v`.  This is where `hpush` is consumed.

`σ` and `hconst` enter only through `slice_const_of_section`: the slice over `σ s` is
exactly the image of `sliceIncl` (`isPullback_sliceIncl` — the slice cut out by a section
is the BASE CHANGE of `σ` along `pullback.snd p q`, so `range (sliceIncl) =
(pullback.snd p q) ⁻¹ (range σ)`), and `hconst` sends all of it to `c s`. -/

/-- **THE TUBE LEMMA** (PROVEN) — the properness half of the covering step.

`{y | m maps the whole slice over y into U}` is OPEN, because its complement is
`(pullback.snd p q) '' (m ⁻¹ (Z ∖ U))`, the image of a closed set under a proper — hence
closed — map.  `pullback.snd p q` is proper as a base change of `p`.

No separatedness, no connectedness, no section: this is the entire content of
"`IsProper ⟹ IsClosedMap` for the base-changed projection". -/
theorem isOpen_setOf_slice_mapsTo {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} [IsProper p]
    (m : pullback p q ⟶ Z) (U : Z.Opens) :
    IsOpen {y : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w ∈ U} := by
  have hcl : IsClosedMap (pullback.snd p q) := (pullback.snd p q).isClosedMap
  have hset : {y : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w ∈ U}
      = (Set.image (pullback.snd p q) (m ⁻¹' (U : Set Z)ᶜ))ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
      not_exists, not_and]
    constructor
    · rintro h w hw rfl
      exact hw (h w rfl)
    · intro h w hw
      by_contra hc
      exact h w hc hw
  rw [hset]
  exact isOpen_compl_iff.mpr (hcl _ ((U.2.isClosed_compl).preimage m.continuous))

/-- **THE SLICE CUT OUT BY A SECTION IS A BASE CHANGE OF THAT SECTION** (PROVEN).

`pullback.snd p q` is the base change of `p` along `q`; base-changing it once more along
`σ` gives the base change of `p` along `σ ≫ q = 𝟙 S`, i.e. `X` itself, and the comparison
map is `sliceIncl`.  Formally this is one pasting: the outer rectangle obtained by
adjoining `pullback.fst p q` on the right is `IsPullback (𝟙 X) p p (𝟙 S)`.

The consequence used below is `range_sliceIncl`: every point of `X ×_S Y` lying over a
point of `σ(S)` — not merely those of the form `(x, σ (p x))` — is in the image of
`sliceIncl`.  That is a statement about the CARRIER of a fibre product and is not formal;
what makes it true is that `κ(σ s) = κ(s)`, so `κ(x) ⊗_{κ(s)} κ(σ s)` has a single prime. -/
theorem isPullback_sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : IsPullback (sliceIncl p q σ hσ) p (pullback.snd p q) σ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p q) (h₂₂ := q) ?_
    (sliceIncl_snd p q σ hσ) (IsPullback.of_hasPullback p q)
  rw [sliceIncl_fst, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **THE IMAGE OF `sliceIncl` IS THE PART OF `X ×_S Y` OVER `σ(S)`** (PROVEN), from
`isPullback_sliceIncl` and `Scheme.Pullback.range_fst`. -/
theorem range_sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) :
    Set.range (sliceIncl p q σ hσ) = (pullback.snd p q) ⁻¹' Set.range σ := by
  have h := isPullback_sliceIncl p q σ hσ
  have e : (sliceIncl p q σ hσ : ↥X → ↥(pullback p q))
      = (pullback.fst (pullback.snd p q) σ) ∘ (h.isoPullback.hom) := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  have hsurj : Function.Surjective
      (h.isoPullback.hom : ↥X → ↥(pullback (pullback.snd p q) σ)) := by
    intro z
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply]; simp⟩
  rw [e, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

/-- **`X ×_S V` IS EXACTLY THE PART OF `X ×_S Y` LYING OVER `V`, ON POINTS** (PROVEN) — the
carrier form of `isPullback_sliceOverOpen`, proven the same way as `range_sliceIncl`. -/
theorem range_sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    Set.range (sliceOverOpen p q V) = (pullback.snd p q) ⁻¹' (V : Set Y) := by
  have h := isPullback_sliceOverOpen p q V
  have e : (sliceOverOpen p q V : ↥(pullback p (V.ι ≫ q)) → ↥(pullback p q))
      = (pullback.fst (pullback.snd p q) V.ι) ∘ (h.isoPullback.hom) := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  have hsurj : Function.Surjective
      (h.isoPullback.hom : ↥(pullback p (V.ι ≫ q)) → ↥(pullback (pullback.snd p q) V.ι)) := by
    intro z
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply]; simp⟩
  rw [e, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst,
    Scheme.Opens.range_ι]

/-- A point of an open subscheme lands in that open. -/
theorem mem_range_ι {W : Scheme.{u}} (V : W.Opens) (v : ↥V) : V.ι v ∈ (V : Set W) := by
  rw [← Scheme.Opens.range_ι]; exact ⟨v, rfl⟩

/-- Affine opens are a basis, in the form used three times below. -/
theorem exists_isAffine_opens_subset {W : Scheme.{u}} {T : Set W} (hT : IsOpen T) (x : W)
    (hx : x ∈ T) : ∃ V : W.Opens, IsAffine V ∧ x ∈ V ∧ (V : Set W) ⊆ T := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hx hT
  exact ⟨V, hV, hxV, hVW⟩

/-- **`V ×_S U` IS AFFINE WHEN `V` AND `U` ARE AFFINE OPENS OVER ONE AFFINE `S₀ ⊆ S`**
(PROVEN).

`Mathlib` has `IsAffine (pullback f g)` for `f` an affine morphism and `g` an affine
scheme, so the only issue is that `V.ι ≫ q` and `U.ι ≫ r` go to `S`, not to `S₀`.  Both
factor through the open immersion `S₀.ι`, which is a MONOMORPHISM, and
`pullbackIsPullbackOfCompMono` says that postcomposing both legs with a mono does not
change the fibre product: `V ×_S U = V ×_{S₀} U`, which is affine. -/
theorem isAffine_pullback_ι_comp {Y Z S : Scheme.{u}} {q : Y ⟶ S} {r : Z ⟶ S} (S₀ : S.Opens)
    (V : Y.Opens) (U : Z.Opens) [IsAffine S₀] [IsAffine V] [IsAffine U]
    (hV : Set.range (V.ι ≫ q) ⊆ (S₀ : Set S)) (hU : Set.range (U.ι ≫ r) ⊆ (S₀ : Set S)) :
    IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) := by
  have hV' : Set.range (V.ι ≫ q) ⊆ Set.range S₀.ι := by
    rw [Scheme.Opens.range_ι]; exact hV
  have hU' : Set.range (U.ι ≫ r) ⊆ Set.range S₀.ι := by
    rw [Scheme.Opens.range_ι]; exact hU
  have hv : IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV' ≫ S₀.ι = V.ι ≫ q :=
    IsOpenImmersion.lift_fac _ _ _
  have hu : IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU' ≫ S₀.ι = U.ι ≫ r :=
    IsOpenImmersion.lift_fac _ _ _
  rw [← hv, ← hu]
  have hpb : IsPullback (pullback.fst (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV')
      (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU'))
      (pullback.snd (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV')
        (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU'))
      (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV' ≫ S₀.ι)
      (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU' ≫ S₀.ι) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono _ _ S₀.ι)
  exact IsAffine.of_isIso hpb.isoPullback.inv

/-- **THE GOOD LOCUS**: the set of points of `Y` at which the conclusion of
`exists_isAffineOpen_slice_nbhd_of_slice_const` holds.  The theorem says it is all of `Y`. -/
def sliceGoodLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : Z ⟶ S)
    (m : pullback p q ⟶ Z) : Set Y :=
  {y | ∃ (V : Y.Opens) (U : Z.Opens), y ∈ V ∧
      IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) ∧
      Set.range (sliceOverOpen p q V ≫ m) ⊆ (U : Set Z)}

/-- **THE CONTRACTED LOCUS**: the set of `y : Y` whose slice `m` maps to a single point. -/
def sliceContractedLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (m : pullback p q ⟶ Z) : Set Y :=
  {y | ∃ z : Z, ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w = z}

/-- **THE GOOD LOCUS IS OPEN** (PROVEN) — immediately, since its witness `V` at `y` is a
neighbourhood of `y` and witnesses membership at each of its own points. -/
theorem isOpen_sliceGoodLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : Z ⟶ S)
    (m : pullback p q ⟶ Z) : IsOpen (sliceGoodLocus p q r m) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨V, U, hyV, haff, hrange⟩
  exact ⟨(V : Set Y), fun y' hy' => ⟨V, U, hy', haff, hrange⟩, V.2, hyV⟩

/-- **CONTRACTED ⟹ GOOD** (PROVEN) — the properness half, packaged.

Given that the slice over `y` goes to the single point `z`: `r z = q y` by `hm`, so an
affine `S₀ ∋ q y`, an affine `U ∋ z` inside `r ⁻¹ᵁ S₀`, the tube lemma, and an affine
`V ∋ y` inside both the tube and `q ⁻¹ᵁ S₀` give the required pair, with `V ×_S U` affine
by `isAffine_pullback_ι_comp`.

`[Surjective (pullback.snd p q)]` is used only to produce ONE point of the slice, which is
what pins `z` over `q y`; it comes from `surjective_of_hasUniversallyTrivialPushforward`. -/
theorem mem_sliceGoodLocus_of_mem_sliceContractedLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [Surjective (pullback.snd p q)]
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) {y : Y}
    (hy : y ∈ sliceContractedLocus p q m) : y ∈ sliceGoodLocus p q r m := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨w₀, hw₀⟩ := (pullback.snd p q).surjective y
  have hzs : r z = q y := by
    rw [← hz w₀ hw₀, ← hw₀]
    simp only [← Scheme.Hom.comp_apply, hm, ← pullback.condition]
  obtain ⟨S₀, hS₀, hsS₀, -⟩ := exists_isAffine_opens_subset isOpen_univ (q y) (Set.mem_univ _)
  haveI := hS₀
  obtain ⟨U, hU, hzU, hUS₀⟩ := exists_isAffine_opens_subset (r ⁻¹ᵁ S₀).2 z
    (show z ∈ ((r ⁻¹ᵁ S₀ : Z.Opens) : Set Z) by simpa [hzs] using hsS₀)
  haveI := hU
  obtain ⟨V, hV, hyV, hVsub⟩ :=
    exists_isAffine_opens_subset
      ((isOpen_setOf_slice_mapsTo m U).inter (q ⁻¹ᵁ S₀).2) y
      (show y ∈ {y' : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y' → m w ∈ U} ∩
          ((q ⁻¹ᵁ S₀ : Y.Opens) : Set Y) from
        ⟨fun w hw => by rw [hz w hw]; exact hzU, by simpa using hsS₀⟩)
  haveI := hV
  refine ⟨V, U, hyV, ?_, ?_⟩
  · refine isAffine_pullback_ι_comp S₀ V U ?_ ?_
    · rintro _ ⟨v, rfl⟩
      simpa using (hVsub (mem_range_ι V v)).2
    · rintro _ ⟨u, rfl⟩
      simpa using hUS₀ (mem_range_ι U u)
  · rintro _ ⟨w', rfl⟩
    have hw : (pullback.snd p q) ((sliceOverOpen p q V) w')
        = V.ι ((pullback.snd p (V.ι ≫ q)) w') := by
      rw [← Scheme.Hom.comp_apply, (isPullback_sliceOverOpen p q V).w, Scheme.Hom.comp_apply]
    have := (hVsub (hw ▸ mem_range_ι V ((pullback.snd p (V.ι ≫ q)) w'))).1
    simpa using this _ rfl

/-- **THE FACTORIZATION AT A POINT OF THE GOOD LOCUS** (PROVEN, over the affine-target
rigidity lemma) — this is where `hpush` is consumed.

At `y` with witnesses `V, U`: `IsOpenImmersion.lift` factors `m` over `V` through `U`, and
`exists_comp_snd_eq_of_isAffine_pullback` (which needs exactly `IsAffine (V ×_S U)`) then
factors it through the projection.  Both consumers of the good locus — contractedness on
points, and the diagonal statement `apply_mem_range_diagonal_of_mem_sliceGoodLocus` — run
off this one morphism-level identity. -/
theorem exists_comp_snd_eq_of_mem_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) {y : Y}
    (hy : y ∈ sliceGoodLocus p q r m) :
    ∃ (V : Y.Opens) (d : V.toScheme ⟶ Z), y ∈ V ∧
      sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d := by
  obtain ⟨V, U, hyV, haff, hrange⟩ := hy
  haveI := haff
  have hrange' : Set.range (sliceOverOpen p q V ≫ m) ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  have hnU : IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange' ≫ U.ι
      = sliceOverOpen p q V ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hnw : IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange' ≫ (U.ι ≫ r)
      = pullback.fst p (V.ι ≫ q) ≫ p := by
    rw [← Category.assoc, hnU, Category.assoc, hm, ← Category.assoc]
    congr 1
    simp [sliceOverOpen, pullback.map, pullback.lift_fst]
  obtain ⟨e, he⟩ := exists_comp_snd_eq_of_isAffine_pullback (p := p) (q := V.ι ≫ q)
    (r := U.ι ≫ r) hpush hnw
  exact ⟨V, e ≫ U.ι, hyV, by rw [← hnU, he, Category.assoc]⟩

/-- **GOOD ⟹ CONTRACTED** (PROVEN): every point of the slice over `y` is in the image of
`sliceOverOpen` by `range_sliceOverOpen`, and `V.ι` is injective, so the factorization above
sends all of them to the single point `d v`, where `v` is the point of `V` over `y`. -/
theorem sliceContractedLocus_of_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    (hm : m ≫ r = pullback.fst p q ≫ p) :
    sliceGoodLocus p q r m ⊆ sliceContractedLocus p q m := by
  intro y hy
  obtain ⟨V, d, hyV, hd⟩ := exists_comp_snd_eq_of_mem_sliceGoodLocus hpush hm hy
  obtain ⟨v, hv⟩ : y ∈ Set.range (V.ι) := by rw [Scheme.Opens.range_ι]; exact hyV
  refine ⟨d v, fun w hw => ?_⟩
  have hwmem : w ∈ Set.range (sliceOverOpen p q V) := by
    rw [range_sliceOverOpen, Set.mem_preimage, hw]
    exact hyV
  obtain ⟨w₁, rfl⟩ := hwmem
  have hvv : (pullback.snd p (V.ι ≫ q)) w₁ = v := by
    apply V.ι.isOpenEmbedding.injective
    rw [hv, ← hw, ← Scheme.Hom.comp_apply, ← (isPullback_sliceOverOpen p q V).w,
      Scheme.Hom.comp_apply]
  rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, hvv]

/-- **THE SLICE OVER `σ s` IS CONTRACTED** (PROVEN) — this is all that `σ` and `hconst` are
for.  Every point of that slice is in the image of `sliceIncl` (`range_sliceIncl`), and
`hconst` sends the image of `sliceIncl` to `c ∘ p`; `σ` is injective because it is a
section, which is what identifies the value as `c s`. -/
theorem slice_const_of_section {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) {m : pullback p q ⟶ Z} (c : S ⟶ Z)
    (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (s : S) :
    σ s ∈ sliceContractedLocus p q m := by
  refine ⟨c s, fun w hw => ?_⟩
  have hmem : w ∈ Set.range (sliceIncl p q σ hσ) := by
    rw [range_sliceIncl]
    exact ⟨s, hw.symm⟩
  obtain ⟨x, rfl⟩ := hmem
  have hps : p x = s := by
    have h1 : σ (p x) = σ s := by
      rw [← hw]
      simp only [← Scheme.Hom.comp_apply, sliceIncl_snd]
    have h2 : (σ ≫ q) (p x) = (σ ≫ q) s := by
      simp only [Scheme.Hom.comp_apply, h1]
    rw [hσ] at h2
    simpa using h2
  rw [← Scheme.Hom.comp_apply, hconst, Scheme.Hom.comp_apply, hps]

/-! ### Semicontinuity: the contracted locus is closed along the fibres of `q`

This is the second half of "clopen", and the only part of the rigidity lemma that is not
either formal or an application of properness.  The mechanism is semicontinuity, and it is
NOT available globally on `Y`: "the slice over `y` is contracted" is a closed condition
only along the fibres of `q`, because what makes it closed is that the projection away from
the proper factor is an OPEN map, which here holds only after restricting to a fibre —
where everything in sight is flat over the FIELD `κ(s)`.

**No flatness hypothesis on `p` is needed or used.**  The flatness that supplies the
openness is the automatic flatness of a scheme over a field, and `Mathlib` packages exactly
that as `instance [IsIntegral Y] [Subsingleton Y] : UniversallyOpen f`
(`Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`): *any* morphism whose target
is the spectrum of a field is universally open.  That instance is the whole geometric input
of `universallyOpen_of_isPullback_residueField` below, and hence of this section.

**The pair scheme.**  Write `P := (X ×_S Y) ×_Y (X ×_S Y)` with projections `pr₁, pr₂` and
`π := pr₁ ≫ pullback.snd p q : P ⟶ Y`, and let `gP : P ⟶ Z ×_S Z` be
`pullback.lift (pr₁ ≫ m) (pr₂ ≫ m)`.  Then `E := gP ⁻¹ (range (pullback.diagonal r))` is
CLOSED, because `[IsSeparated r]` makes the diagonal a closed immersion, and

  `sliceContractedLocus = {y | π ⁻¹ {y} ⊆ E}`,

whose complement is `π '' Eᶜ` — the image of an OPEN set, hence open as soon as `π` is an
open map.  Over a residue-field base `π` is open, because `pr₁` and `pullback.snd p q` are
each base changes of `p` along morphisms that factor through `Spec κ(s)`.

**Why the scheme-theoretic `E` rather than the set-theoretic condition.**  "All points of
the slice have the same image" is NOT the preimage of the diagonal: for `w, w'` in one
slice with `m w = m w'` the induced point of `Z ×_S Z` need not lie on the diagonal, since
`κ(z) ⊗_{κ(s)} κ(z)` has many primes.  The two directions are proven separately —
`{y | π ⁻¹ {y} ⊆ E} ⊆ sliceContractedLocus` from `Mathlib`'s `PullbackCarrier`
(`exists_preimage_pullback`) together with `diagonal_fst`/`diagonal_snd`, and the reverse
through the good locus, where the factorization
`sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d` makes the two composites
`pr₁ ≫ m` and `pr₂ ≫ m` EQUAL AS MORPHISMS over `V`
(`apply_mem_range_diagonal_of_mem_sliceGoodLocus`). -/

/-- **ANY BASE CHANGE ALONG A MORPHISM THAT FACTORS THROUGH A RESIDUE FIELD IS UNIVERSALLY
OPEN** (PROVEN) — the geometric input of the semicontinuity argument.

If `b` is a base change of `p : X ⟶ S` along `g = g₀ ≫ S.fromSpecResidueField s`, then `b`
is also a base change, along `g₀`, of `X ×_S Spec κ(s) ⟶ Spec κ(s)` (this is
`IsPullback.of_right'` applied to the two squares), and that morphism is universally open
because its TARGET is the spectrum of a field — `Mathlib`'s
`[IsIntegral Y] [Subsingleton Y] : UniversallyOpen f`.  `UniversallyOpen` is stable under
base change, so `b` is universally open.

**`p` is arbitrary**: not flat, not proper, not finitely presented.  All the flatness is in
the base being a field. -/
theorem universallyOpen_of_isPullback_residueField {X W W' S : Scheme.{u}} {p : X ⟶ S}
    {a : W' ⟶ X} {b : W' ⟶ W} {g : W ⟶ S} (s : S) (g₀ : W ⟶ Spec (S.residueField s))
    (hg : g = g₀ ≫ S.fromSpecResidueField s) (h : IsPullback a b p g) :
    UniversallyOpen b := by
  subst hg
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right' h (IsPullback.of_hasPullback p (S.fromSpecResidueField s)))
    inferInstance

/-- **OVER THE GOOD LOCUS THE PAIR SCHEME LANDS IN THE DIAGONAL** (PROVEN).

This is the direction that cannot be done on points.  Over the witness `V` of the good
locus the two composites `pr₁ ≫ m` and `pr₂ ≫ m` become EQUAL AS MORPHISMS: both
projections restricted to `π ⁻¹ᵁ V` factor through `sliceOverOpen p q V` (by
`IsOpenImmersion.lift`, using `range_sliceOverOpen`), the two lifts have the same composite
with `pullback.snd p (V.ι ≫ q)` because `V.ι` is a MONOMORPHISM and both become
`π` after composing with it, and the factorization
`sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d` then makes the two composites
literally the same morphism.  Hence `π ⁻¹ᵁ V ⟶ Z ×_S Z` factors through the diagonal, and
in particular each of its points does. -/
theorem apply_mem_range_diagonal_of_mem_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (gP : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback r r)
    (hg₁ : gP ≫ pullback.fst r r
      = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ m)
    (hg₂ : gP ≫ pullback.snd r r
      = pullback.snd (pullback.snd p q) (pullback.snd p q) ≫ m)
    (ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)))
    (hξ : (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ
      ∈ sliceGoodLocus p q r m) :
    gP ξ ∈ Set.range (pullback.diagonal r) := by
  obtain ⟨V, d, hyV, hd⟩ := exists_comp_snd_eq_of_mem_sliceGoodLocus hpush hm hξ
  obtain ⟨ξ', hξ'⟩ : ξ ∈ Set.range
      (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι) := by
    rw [Scheme.Opens.range_ι]; exact hyV
  have hrange : ∀ (t : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback p q),
      t ≫ pullback.snd p q
        = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q →
      Set.range (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ t) ⊆ Set.range (sliceOverOpen p q V) := by
    intro t ht
    rintro _ ⟨x, rfl⟩
    rw [range_sliceOverOpen, Set.mem_preimage, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ht, Scheme.Hom.comp_apply]
    exact mem_range_ι _ x
  have h₁ := hrange (pullback.fst (pullback.snd p q) (pullback.snd p q)) rfl
  have h₂ := hrange (pullback.snd (pullback.snd p q) (pullback.snd p q)) pullback.condition.symm
  have key : (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m
      = (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.snd (pullback.snd p q) (pullback.snd p q)) ≫ m := by
    have e₁ := IsOpenImmersion.lift_fac (sliceOverOpen p q V) _ h₁
    have e₂ := IsOpenImmersion.lift_fac (sliceOverOpen p q V) _ h₂
    have hmono : IsOpenImmersion.lift (sliceOverOpen p q V) _ h₁ ≫ pullback.snd p (V.ι ≫ q)
        = IsOpenImmersion.lift (sliceOverOpen p q V) _ h₂ ≫ pullback.snd p (V.ι ≫ q) := by
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc,
        ← (isPullback_sliceOverOpen p q V).w, ← Category.assoc, ← Category.assoc, e₁, e₂,
        Category.assoc, Category.assoc, pullback.condition]
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, hd, ← Category.assoc, ← Category.assoc,
      hmono]
  have hfac : ((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
      ≫ gP
      = ((((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m) ≫ pullback.diagonal r := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, hg₁,
        Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, hg₂]
      simpa using key.symm
  refine ⟨((((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
    ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m) ξ', ?_⟩
  rw [← hξ', ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]

/-- **THE CONTRACTED LOCUS IS CLOSED WHEN `q` FACTORS THROUGH A RESIDUE FIELD** (PROVEN) —
the semicontinuity statement, in the only generality in which it is true.

The complement of the contracted locus is `π '' Eᶜ` with `E` closed, and `π` is an open map
here: `pullback.snd p q` is a base change of `p` along `q = q₀ ≫ fromSpecResidueField`, and
`pr₁` is a base change of `p` along `pullback.snd p q ≫ q` (paste the pair square onto the
fibre-product square), both of which factor through `Spec κ(s)`, so
`universallyOpen_of_isPullback_residueField` applies to each and `UniversallyOpen` is stable
under composition. -/
theorem isClosed_sliceContractedLocus_of_residueField {X F Z S : Scheme.{u}} {p : X ⟶ S}
    {q : F ⟶ S} {r : Z ⟶ S} [IsProper p] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    (hm : m ≫ r = pullback.fst p q ≫ p) (s : S) (q₀ : F ⟶ Spec (S.residueField s))
    (hq : q = q₀ ≫ S.fromSpecResidueField s) :
    IsClosed (sliceContractedLocus p q m) := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  haveI : IsClosedImmersion (pullback.diagonal r) := IsSeparated.isClosedImmersion_diagonal
  have hover : ∀ t : (pullback (pullback.snd p q) (pullback.snd p q)) ⟶ pullback p q,
      (t ≫ m) ≫ r = (t ≫ pullback.snd p q) ≫ q := by
    intro t
    rw [Category.assoc, hm, pullback.condition, ← Category.assoc]
  obtain ⟨gP, hg₁, hg₂⟩ : ∃ g : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback r r,
      g ≫ pullback.fst r r = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ m ∧
      g ≫ pullback.snd r r = pullback.snd (pullback.snd p q) (pullback.snd p q) ≫ m := by
    refine ⟨pullback.lift _ _ ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hover, hover, pullback.condition]
  have hEclosed : IsClosed
      ((gP : ↥(pullback (pullback.snd p q) (pullback.snd p q)) → ↥(pullback r r))
        ⁻¹' Set.range (pullback.diagonal r)) :=
    (pullback.diagonal r).isClosedEmbedding.isClosed_range.preimage gP.continuous
  have hCeq : sliceContractedLocus p q m
      = {y : F | ∀ ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)),
          (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ = y →
            gP ξ ∈ Set.range (pullback.diagonal r)} := by
    refine Set.Subset.antisymm (fun y hy ξ hξ => ?_) (fun y hy => ?_)
    · exact apply_mem_range_diagonal_of_mem_sliceGoodLocus hpush hm gP hg₁ hg₂ ξ
        (by rw [hξ]; exact mem_sliceGoodLocus_of_mem_sliceContractedLocus hm hy)
    · obtain ⟨w₀, hw₀⟩ := (pullback.snd p q).surjective y
      refine ⟨m w₀, fun w hw => ?_⟩
      obtain ⟨ξ, e₁, e₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p q)
        (g := pullback.snd p q) w w₀ (by rw [hw, hw₀])
      obtain ⟨z, hz⟩ := hy ξ (by rw [Scheme.Hom.comp_apply, e₁, hw])
      have hzw : m w = z := by
        rw [← e₁, ← Scheme.Hom.comp_apply, ← hg₁, Scheme.Hom.comp_apply, ← hz,
          ← Scheme.Hom.comp_apply, pullback.diagonal_fst]
        simp
      have hzw₀ : m w₀ = z := by
        rw [← e₂, ← Scheme.Hom.comp_apply, ← hg₂, Scheme.Hom.comp_apply, ← hz,
          ← Scheme.Hom.comp_apply, pullback.diagonal_snd]
        simp
      rw [hzw, hzw₀]
  have h1 : UniversallyOpen (pullback.fst (pullback.snd p q) (pullback.snd p q)) :=
    universallyOpen_of_isPullback_residueField s (pullback.snd p q ≫ q₀)
      (by rw [Category.assoc, ← hq])
      (IsPullback.paste_horiz
        ((IsPullback.of_hasPullback (pullback.snd p q) (pullback.snd p q)).flip)
        (IsPullback.of_hasPullback p q))
  have h2 : UniversallyOpen (pullback.snd p q) :=
    universallyOpen_of_isPullback_residueField s q₀ hq (IsPullback.of_hasPullback p q)
  haveI hπ : UniversallyOpen (pullback.fst (pullback.snd p q) (pullback.snd p q)
      ≫ pullback.snd p q) := MorphismProperty.comp_mem _ _ _ h1 h2
  rw [hCeq, ← isOpen_compl_iff]
  have hcompl : {y : F | ∀ ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)),
        (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ = y →
          gP ξ ∈ Set.range (pullback.diagonal r)}ᶜ
      = (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ''
        ((gP : ↥(pullback (pullback.snd p q) (pullback.snd p q)) → ↥(pullback r r))
          ⁻¹' Set.range (pullback.diagonal r))ᶜ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage,
      not_forall]
    constructor
    · rintro ⟨ξ, hξ, hξ'⟩
      exact ⟨ξ, hξ', hξ⟩
    · rintro ⟨ξ, hξ', hξ⟩
      exact ⟨ξ, hξ, hξ'⟩
  rw [hcompl]
  exact (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q).isOpenMap _
    (isOpen_compl_iff.mpr hEclosed)

/-- **CONTRACTEDNESS IS A FIBREWISE NOTION** (PROVEN): base-changing `q` along an INJECTIVE
`t` pulls the contracted locus back to the contracted locus.

Only injectivity of `t` on points is used, plus the fact that the base change `j` has range
`(pullback.snd p q) ⁻¹ (range t)` — which for `t = q.fiberι s` is `Mathlib`'s
`Scheme.Pullback.range_map`. -/
theorem sliceContractedLocus_comp_eq {X Y Z T S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (t : T ⟶ Y) (ht : Function.Injective (t : ↥T → ↥Y)) {m : pullback p q ⟶ Z}
    (j : pullback p (t ≫ q) ⟶ pullback p q)
    (hjrange : Set.range (j : ↥(pullback p (t ≫ q)) → ↥(pullback p q))
      = (pullback.snd p q) ⁻¹' Set.range (t : ↥T → ↥Y))
    (hjsnd : j ≫ pullback.snd p q = pullback.snd p (t ≫ q) ≫ t) :
    sliceContractedLocus p (t ≫ q) (j ≫ m)
      = (t : ↥T → ↥Y) ⁻¹' sliceContractedLocus p q m := by
  ext f
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun w hw => ?_⟩
    have hwr : w ∈ Set.range (j : ↥(pullback p (t ≫ q)) → ↥(pullback p q)) := by
      rw [hjrange, Set.mem_preimage, hw]
      exact ⟨f, rfl⟩
    obtain ⟨w₁, rfl⟩ := hwr
    refine (?_ : m (j w₁) = z)
    rw [← Scheme.Hom.comp_apply]
    refine hz w₁ (ht ?_)
    rw [← Scheme.Hom.comp_apply, ← hjsnd, Scheme.Hom.comp_apply, hw]
  · rintro ⟨z, hz⟩
    refine ⟨z, fun w₁ hw₁ => ?_⟩
    rw [Scheme.Hom.comp_apply]
    refine hz _ ?_
    rw [← Scheme.Hom.comp_apply, hjsnd, Scheme.Hom.comp_apply, hw₁]

/-- **THE CONTRACTED LOCUS IS CLOSED IN EACH FIBRE OF `q`** (PROVEN) — the closed half of
the clopen argument, and the last piece of the rigidity lemma.

Restrict to the scheme-theoretic fibre `q.fiber s`, whose structure morphism to `S` factors
through `Spec κ(s)` by `Scheme.Hom.fiber_fac`.  `sliceContractedLocus_comp_eq` identifies
the contracted locus of the base-changed situation with the preimage of this one under
`q.fiberι s` — the fibre inclusion is injective, and `Scheme.Pullback.range_map` gives the
range of the base change — and
`isClosed_sliceContractedLocus_of_residueField` says the former is closed.  Finally
`Scheme.Hom.fiberHomeo` identifies the fibre with `q ⁻¹ {s}` as a topological subspace. -/
theorem isClosed_sliceContractedLocus_fiber {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [IsSeparated r] (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) (s : S) :
    IsClosed {u : ↥((q : ↥Y → ↥S) ⁻¹' {s}) | (u : Y) ∈ sliceContractedLocus p q m} := by
  have hjfst : (pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ pullback.fst p q = pullback.fst p (q.fiberι s ≫ q) := by
    simp only [pullback.map]
    rw [pullback.lift_fst, Category.comp_id]
  have hjsnd : (pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ pullback.snd p q = pullback.snd p (q.fiberι s ≫ q) ≫ q.fiberι s := by
    simp only [pullback.map]
    rw [pullback.lift_snd]
  have hmF : ((pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ m) ≫ r = pullback.fst p (q.fiberι s ≫ q) ≫ p := by
    rw [Category.assoc, hm, ← Category.assoc, hjfst]
  have hclosed := isClosed_sliceContractedLocus_of_residueField hpush hmF s
    (q.fiberToSpecResidueField s) (q.fiber_fac s)
  rw [sliceContractedLocus_comp_eq (q.fiberι s) (q.fiberι s).isEmbedding.injective _
    (by rw [Scheme.Pullback.range_map]; simp) hjsnd] at hclosed
  rw [← (q.fiberHomeo s).isClosed_preimage]
  exact hclosed

/-- **THE CLOPEN ARGUMENT** (PROVEN): the good locus is everything.

`sliceContractedLocus = sliceGoodLocus` by the two inclusions above, so that set is OPEN;
it is closed in each fibre of `q` by `isClosed_sliceContractedLocus_fiber`; it meets each
fibre, at `σ s`, by
`slice_const_of_section`; and the fibres of `q` are CONNECTED — `Mathlib`'s
`Scheme.Hom.isConnected_preimage_singleton` for `[GeometricallyConnected q]`.  A nonempty
clopen subset of a preconnected space is everything.

This is where the FAITHFULNESS NOTE bites: with `Y` two points over `S = Spec k` the fibre
`q ⁻¹ {s}` is disconnected, the clopen subset is a single point, and the conclusion fails. -/
theorem mem_sliceGoodLocus_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p) (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    y ∈ sliceGoodLocus p q r m := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  have hCG : sliceContractedLocus p q m ⊆ sliceGoodLocus p q r m :=
    fun _ hy => mem_sliceGoodLocus_of_mem_sliceContractedLocus hm hy
  have hCeq : sliceContractedLocus p q m = sliceGoodLocus p q r m :=
    Set.Subset.antisymm hCG (sliceContractedLocus_of_sliceGoodLocus hpush hm)
  have hconn : _root_.IsConnected ((q : ↥Y → ↥S) ⁻¹' {q y}) :=
    q.isConnected_preimage_singleton _
  haveI : PreconnectedSpace ↥((q : ↥Y → ↥S) ⁻¹' {q y}) :=
    Subtype.preconnectedSpace hconn.isPreconnected
  have hclopen : IsClopen
      {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m} := by
    refine ⟨isClosed_sliceContractedLocus_fiber hpush hm _, ?_⟩
    rw [hCeq]
    exact (isOpen_sliceGoodLocus p q r m).preimage continuous_subtype_val
  have hσmem : σ (q y) ∈ ((q : ↥Y → ↥S) ⁻¹' {q y}) := by
    have h : (σ ≫ q) (q y) = q (σ (q y)) := Scheme.Hom.comp_apply _ _ _
    rw [hσ] at h
    simpa using h.symm
  have hne : {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m}.Nonempty :=
    ⟨⟨σ (q y), hσmem⟩, slice_const_of_section σ hσ c hconst (q y)⟩
  have huniv := hclopen.eq_univ hne
  have hy : (⟨y, rfl⟩ : ↥((q : ↥Y → ↥S) ⁻¹' {q y}))
      ∈ {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m} := by
    rw [huniv]; trivial
  exact hCG hy

/-- **THE COVERING STEP AT A POINT, IN OPENS ONLY** — PROVEN (2026-07-28) over the single
leaf `isClosed_sliceContractedLocus_fiber`; it is `mem_sliceGoodLocus_of_slice_const`
restated, since `sliceGoodLocus` is by definition the set of `y` at which this holds.

**What is produced at `y`.**  An open `V ∋ y` in `Y` and an open `U ⊆ Z` such that

* `m` maps the whole of `X ×_S V` into `U` — written as the containment of set-theoretic
  ranges, which is precisely `IsOpenImmersion.lift`'s hypothesis; and
* `V ×_S U` is an AFFINE SCHEME — "`U` is affine over the base, over `V`".  In the
  construction `V` and `U` are affine opens lying over one affine open `S₀ ⊆ S`, so
  `V ×_S U = V ×_{S₀} U` is a fibre product of affines over an affine
  (`isAffine_pullback_ι_comp`).

**The proof** (Mumford *AV* §4; BLR 8.4), in the two halves the section above develops.

1. *The properness half*, now PROVEN as `isOpen_setOf_slice_mapsTo`: if the whole slice
   over `y` is mapped into an open `U`, then the same holds over an open neighbourhood of
   `y`, because `m ⁻¹(Z ∖ U)` is closed and `pullback.snd p q` is proper — hence a CLOSED
   MAP — as a base change of `p`.  Packaged with the affine choices this is
   `mem_sliceGoodLocus_of_mem_sliceContractedLocus`.

2. *The connectedness half*, now assembled as `mem_sliceGoodLocus_of_slice_const`: the
   locus where the slice is contracted equals the locus where the conclusion holds (the
   two inclusions above, the second of which is where `hpush` is spent), hence is OPEN; it
   contains `σ(s)` for every `s` by `slice_const_of_section`; and
   `[GeometricallyConnected q]` makes the fibres of `q` connected.  That the locus is also
   CLOSED in each fibre is `isClosed_sliceContractedLocus_fiber`, the semicontinuity
   statement, which is where flatness over the residue field enters.

**WHY THE STATEMENT IS FALSE WITHOUT `[GeometricallyConnected q]`**: with `Y = {y₀, y₁}`
two points over `S = Spec k` the locus produced by (1) is a single point — see the
FAITHFULNESS NOTE in the module docstring.  So half (2) is not decoration.

**AXIS SEARCHED**: the affine and affine-over-the-base cases are DONE and were never what
was missing (`exists_comp_snd_eq_of_isAffine`, `exists_comp_snd_eq_of_isAffine_pullback`);
so is the `Γ ⊣ Spec` corollary, the epimorphism property of the projection
(`eq_of_comp_snd_eq`), the cartesian square (`isPullback_sliceOverOpen`) and the whole
gluing step.  The étale axis (`section_eq_of_formallyUnramified`, diagonal simultaneously
open and closed) is searched and DEAD: `Δ_{B/S}` is an open immersion iff `Ω_{B/S} = 0`,
which fails in relative dimension `> 0`. -/
theorem exists_isAffineOpen_slice_nbhd_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    ∃ (V : Y.Opens) (U : Z.Opens), y ∈ V ∧
      IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) ∧
      Set.range (sliceOverOpen p q V ≫ m) ⊆ (U : Set Z) :=
  mem_sliceGoodLocus_of_slice_const hpush σ hσ hm c hconst y

/-- **THE COVERING STEP, LOCALISED AT A POINT** — PROVEN over
`exists_isAffineOpen_slice_nbhd_of_slice_const`.

At each point `y : Y` there is an open `V ∋ y` over which `m` factors through a scheme
affine over the base.  Given the leaf's opens `V` and `U`, the factorizing morphism is
`IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m)`: `U.ι` is an open immersion and the
leaf's range containment is literally the hypothesis that `lift` requires, so `W = U`,
`w = U.ι ≫ r` and `j = U.ι`.  That `n` is an `S`-morphism is `hm` together with
`sliceOverOpen p q V ≫ pullback.fst p q = pullback.fst p (V.ι ≫ q)`.

Neither `σ`, `hconst`, `hpush` nor any of the three instance hypotheses is used HERE —
they are all consumed inside the leaf; they are carried only so the statement matches
what the covering step needs. -/
theorem exists_isAffineOver_nbhd_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    ∃ (V : Y.Opens) (W : Scheme.{u}) (w : W ⟶ S) (j : W ⟶ Z)
      (n : pullback p (V.ι ≫ q) ⟶ W),
      y ∈ V ∧ IsAffine (pullback (V.ι ≫ q) w) ∧
      n ≫ w = pullback.fst p (V.ι ≫ q) ≫ p ∧
      n ≫ j = sliceOverOpen p q V ≫ m := by
  obtain ⟨V, U, hy, haff, hrange⟩ :=
    exists_isAffineOpen_slice_nbhd_of_slice_const hpush σ hσ hm c hconst y
  have hrange' : Set.range (sliceOverOpen p q V ≫ m) ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨V, U.toScheme, U.ι ≫ r, U.ι,
    IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange', hy, haff, ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hm, ← Category.assoc]
  congr 1
  simp [sliceOverOpen, pullback.map, pullback.lift_fst]

/-- **THE COVERING STEP OF THE RIGIDITY LEMMA** — PROVEN over
`exists_isAffineOver_nbhd_of_slice_const`.

`Y` is covered by opens `V i` over each of which `m` factors through a scheme `W i` that is
**affine over the base**, in the sense that `V i ×_S W i` is an affine scheme.  Given that,
`exists_comp_snd_eq_of_isAffine_pullback` factors `m` over each `V i`, and
`exists_comp_snd_eq_of_open_cover` glues.

The passage from the pointwise statement is pure bookkeeping and is done here once: index
the cover by the POINTS of `Y`, choosing for each `y` the neighbourhood `V y` produced by
the leaf.  Then `⨆ y, V y = ⊤` because `y ∈ V y`, and every other component of the
conclusion is transported unchanged.  That is the whole reason the remaining leaf may be
stated at a single point — no generality is lost, and a topological argument that had to
carry an index set through itself would be strictly worse. -/
theorem exists_isAffineOver_cover_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ (ι : Type u) (V : ι → Y.Opens) (W : ι → Scheme.{u}) (w : ∀ i, W i ⟶ S)
      (j : ∀ i, W i ⟶ Z) (n : ∀ i, pullback p ((V i).ι ≫ q) ⟶ W i),
      (⨆ i, V i) = ⊤ ∧ (∀ i, IsAffine (pullback ((V i).ι ≫ q) (w i))) ∧
      (∀ i, n i ≫ w i = pullback.fst p ((V i).ι ≫ q) ≫ p) ∧
      (∀ i, n i ≫ j i = sliceOverOpen p q (V i) ≫ m) := by
  choose V W w j n hmem haff hnw hnj using
    exists_isAffineOver_nbhd_of_slice_const (r := r) hpush σ hσ hm c hconst
  refine ⟨↥Y, V, W, w, j, n, ?_, haff, hnw, hnj⟩
  refine top_le_iff.mp fun y _ => ?_
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩

/-- **THE GLUING STEP OF THE RIGIDITY LEMMA** (PROVEN): local factorizations of `m`
through the projection, over an open cover of `Y`, glue to a global one.

**The proof, as carried out.**  Two halves, and the first is the one that is not free.

*Overlaps.*  The chosen `d i : V i ⟶ Z` agree on `V i ×_Y V j` because the factorization
through the projection is UNIQUE — that is `eq_of_comp_snd_eq`, the statement that
`pullback.snd p _` is an EPIMORPHISM, which is where the pushforward hypothesis is spent
(via surjectivity of `p` and the affine-target injectivity; see the section above).
Concretely: write `w := pullback.fst (V i).ι (V j).ι ≫ (V i).ι` for the canonical map
`V i ×_Y V j ⟶ Y`, which equals `pullback.snd (V i).ι (V j).ι ≫ (V j).ι` by
`pullback.condition`.  Base-changing `m` along `w` and using the defining property of
`d k` twice — once through the `i`-leg, once through the `j`-leg — expresses
`pullback.snd p (w ≫ q) ≫ (leg ≫ d k)` as ONE AND THE SAME morphism
`pullback.map … ≫ m` in both cases; cancelling the epimorphism gives the agreement.

*Assembly.*  `Scheme.Cover.glueMorphisms` on `Y.openCoverOfIsOpenCover V hV` produces the
global `d`, and `m = pullback.snd p q ≫ d` is checked on the pullback of that cover along
`pullback.snd p q`.  The `i`-th member of THAT cover is `(X ×_S Y) ×_Y V i`, which
`isPullback_sliceOverOpen` identifies with `X ×_S V i` carrying `sliceOverOpen p q (V i)`;
under that identification the goal is exactly the hypothesis `hd i` combined with
`ι_glueMorphisms`.

This is bookkeeping rather than mathematics, but it is not free: it is the reason
`exists_comp_snd_eq_of_isAffine` is stated as an `∃!` rather than an `∃`, and the reason
`eq_of_comp_snd_eq` had to be proven at all. -/
theorem exists_comp_snd_eq_of_open_cover {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    {ι : Type u} (V : ι → Y.Opens) (hV : (⨆ i, V i) = ⊤)
    (hd : ∀ i, ∃ d : (V i).toScheme ⟶ Z,
      sliceOverOpen p q (V i) ≫ m = pullback.snd p ((V i).ι ≫ q) ≫ d) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  choose d hd using hd
  let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover V hV
  have hcompat : ∀ i j : ι, pullback.fst ((V i).ι) ((V j).ι) ≫ d i
      = pullback.snd ((V i).ι) ((V j).ι) ≫ d j := by
    intro i j
    refine eq_of_comp_snd_eq (p := p)
      (q := (pullback.fst ((V i).ι) ((V j).ι) ≫ (V i).ι) ≫ q) hpush ?_
    have key : ∀ (k : ι) (w : pullback ((V i).ι) ((V j).ι) ⟶ Y)
        (c : pullback ((V i).ι) ((V j).ι) ⟶ (V k).toScheme), c ≫ (V k).ι = w →
        pullback.snd p (w ≫ q) ≫ c ≫ d k
          = pullback.map p (w ≫ q) p q (𝟙 X) w (𝟙 S) (by simp) (by simp) ≫ m := by
      intro k w c hc
      have hNs : pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
            (by rw [Category.comp_id, ← Category.assoc, hc]) ≫ pullback.snd p ((V k).ι ≫ q)
          = pullback.snd p (w ≫ q) ≫ c := by
        simp [pullback.map, pullback.lift_snd]
      have hNslice : pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
            (by rw [Category.comp_id, ← Category.assoc, hc]) ≫ sliceOverOpen p q (V k)
          = pullback.map p (w ≫ q) p q (𝟙 X) w (𝟙 S) (by simp) (by simp) := by
        apply pullback.hom_ext <;>
          simp [sliceOverOpen, pullback.map, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_snd_assoc, hc]
      calc pullback.snd p (w ≫ q) ≫ c ≫ d k
          = (pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
              (by rw [Category.comp_id, ← Category.assoc, hc]) ≫
                sliceOverOpen p q (V k)) ≫ m := by
            rw [Category.assoc, hd k, ← Category.assoc, ← hNs, Category.assoc]
        _ = _ := by rw [hNslice]
    rw [key i _ (pullback.fst ((V i).ι) ((V j).ι)) rfl,
      key j _ (pullback.snd ((V i).ι) ((V j).ι)) pullback.condition.symm]
  have hglue : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms d hcompat = d i :=
    fun i => 𝒰.ι_glueMorphisms d hcompat i
  refine ⟨𝒰.glueMorphisms d hcompat, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd p q)) _ _ fun i => ?_
  show pullback.fst (pullback.snd p q) ((V i).ι) ≫ m
      = pullback.fst (pullback.snd p q) ((V i).ι) ≫ pullback.snd p q ≫
        𝒰.glueMorphisms d hcompat
  refine (cancel_epi ((isPullback_sliceOverOpen p q (V i)).isoPullback.hom)).mp ?_
  rw [← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst, hd i,
    ← Category.assoc, (isPullback_sliceOverOpen p q (V i)).w, Category.assoc, hglue i]

/-- **THE RIGIDITY LEMMA** (PROVEN over the covering and gluing leaves above — Mumford
*Abelian Varieties* §4; BLR *Néron Models* 8.4 in the relative case; Mumford *GIT* Prop. 6.1
over a general base).

Let `p : X ⟶ S` be proper with `𝒪_S = p_*𝒪_X` universally, let `q : Y ⟶ S` have
geometrically connected fibres, and let `r : Z ⟶ S` be separated.  An `S`-morphism
`m : X ×_S Y ⟶ Z` that is CONSTANT along one slice `X ×_S σ(S)` — that is, whose
restriction along `sliceIncl` factors through `p` — factors through the projection to `Y`.

**The proof.**  Fix `s ∈ S` and an affine open `U ⊆ Z` containing the image of the
contracted slice.  `m⁻¹(Z ∖ U)` is closed in `X ×_S Y`, and `pullback.snd p q` is proper
(base change of `p`; the earlier version of this note said `pullback.fst`, which is the base
change of `q` and lands in `X`), so its image in `Y` is closed and misses `σ(S)`; on the open
complement `V` the whole slice `X ×_S V` maps into the affine `U`, and a morphism from a
proper scheme with `p_*𝒪 = 𝒪` to an affine scheme over the base factors through the base
— this is where the pushforward hypothesis is consumed, and it is consumed after a base
change to `V`, which is why the hypothesis is the UNIVERSAL one.  So `m` factors through
`Y` over `V`.  The locus where `m` factors is then open and closed, and
`GeometricallyConnected q` makes it everything.

**WHY `[GeometricallyConnected q]` IS NOT DECORATION**: see the FAITHFULNESS NOTE in the
module docstring — with `Y = {y₀, y₁}` two points the statement is false.

**STATUS (2026-07-27).**  The check recorded here — "land
`hasUniversallyTrivialPushforward_of_isProper_of_flat`, add the corollary *an `S`-morphism
from `X` to a scheme affine over `S` factors uniquely through `S`*, and this leaf is the
topological argument and nothing more" — has been RUN, and it came out as predicted.  The
corollary is `HasTrivialPushforward.existsUnique_comp_eq` (equivalently
`existsUnique_comp_eq_of_hasTrivialPushforward`), its relative form is
`exists_comp_snd_eq_of_isAffine_pullback`, and both are PROVEN above and consumed below,
**without** `hasUniversallyTrivialPushforward_of_isProper_of_flat` having landed (that leaf
is an input to the *hypothesis* `hpush`, not to this proof).  What is left is exactly the
topology, split into `exists_isAffineOver_cover_of_slice_const` (the covering — properness,
`σ`, connectedness) and `exists_comp_snd_eq_of_open_cover` (the gluing).

**STATUS (2026-07-27, later).**  The gluing is now PROVEN — over `eq_of_comp_snd_eq`, the
epimorphism property of the projection, which is itself proven from the universal
pushforward hypothesis via surjectivity of `p`.  The covering is PROVEN over
`exists_isAffineOver_nbhd_of_slice_const` (its pointwise form), which is in turn PROVEN
over `exists_isAffineOpen_slice_nbhd_of_slice_const` (its opens-only form).

**STATUS (2026-07-28): PROVEN OUTRIGHT — NO OPEN LEAF REMAINS UNDER THIS THEOREM.**  The
opens-only form is proven from `isOpen_setOf_slice_mapsTo` (properness ⟹ closed map ⟹ the
tube lemma), `mem_sliceGoodLocus_of_slice_const` (the `GeometricallyConnected` clopen
argument) and `isClosed_sliceContractedLocus_fiber` (semicontinuity of contractedness along
the fibres of `q`, over a field).  Nothing under *this* theorem is sorried; the hypothesis
`hpush` is taken in, not proven here.

(Corrected 2026-07-28: this paragraph used to say "the only `sorry` anywhere in this file's
cone is `isIso_appTop_of_isProper_of_flat`".  Both halves were false —
`isIso_appTop_of_isProper_of_flat` is PROVEN, and the open leaves are far upstream of the
rigidity block.  Re-counted 2026-07-30: that correction named the leaves as
`finiteType_appTop_of_isProper` and `surjective_quotientMap_appTop_of_isIso_appTop_fiber`,
and the second has since been proven, as has `finiteType_appTop_of_isProper`; then the set was
`adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` and
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`, and both of those have since been
proven too — the set was then `mem_smul_adjoin_of_appTop_fiberι_eq_zero` and
`mem_smul_top_of_appTop_fiberι_eq_zero`, and those are now proven as well, over the single
`self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero`.  Any count in this file is stale by
construction; run the compiler.)

The concrete obstruction the earlier audit named is still worth recording, because it is
what the covering step had to get past: the reduction to an affine target cannot be done
globally — with `S = Spec k`, `X = Spec k`, `Y = Z = ℙ¹`, `q = r` the structure maps and
`m = 𝟙`, every hypothesis holds, `d = 𝟙` is the factorization, and `m` factors through no
affine scheme.  So the work is genuinely local-to-global on `Y`. -/
theorem exists_comp_snd_eq_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  obtain ⟨ι, V, W, w, j, n, hVtop, hWaff, hnw, hnj⟩ :=
    exists_isAffineOver_cover_of_slice_const hpush σ hσ hm c hconst
  refine exists_comp_snd_eq_of_open_cover hpush V hVtop fun i => ?_
  haveI := hWaff i
  obtain ⟨e, he⟩ := exists_comp_snd_eq_of_isAffine_pullback (p := p) (q := (V i).ι ≫ q)
    (r := w i) hpush (hnw i)
  exact ⟨e ≫ j i, by rw [← hnj i, he, Category.assoc]⟩

/-- **A morphism `A ×_S A ⟶ B` vanishing on BOTH AXES vanishes** (PROVEN, over the
rigidity lemma).

This is Mumford *AV* §4 Cor. 1 in the form in which rigidity is actually applied: `e` is
the zero section of `A`, `z` is the zero section of `B`, and the two hypotheses say that
`m` restricted to `A × {0}` and to `{0} × A` is the composite `A ⟶ S ⟶ B`.  The
conclusion is that `m` itself is that composite.

Feeding it `m = u(x + y) − u(x) − u(y)` for an `S`-morphism `u : A ⟶ B` carrying the
origin to the origin is what turns `u` into a homomorphism. -/
theorem eq_comp_of_rigidity_axes {A B S : Scheme.{u}} {af : A ⟶ S} {bf : B ⟶ S}
    [IsProper af] [GeometricallyConnected af] [IsSeparated bf]
    (hpush : HasUniversallyTrivialPushforward af)
    (e : S ⟶ A) (he : e ≫ af = 𝟙 S) (z : S ⟶ B)
    {m : pullback af af ⟶ B} (hm : m ≫ bf = pullback.fst af af ≫ af)
    (h₁ : sliceIncl af af e he ≫ m = af ≫ z)
    (h₂ : pullback.lift (af ≫ e) (𝟙 A)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ m = af ≫ z) :
    m = pullback.fst af af ≫ af ≫ z := by
  obtain ⟨d, hd⟩ := exists_comp_snd_eq_of_slice_const hpush e he hm z h₁
  have hdz : d = af ≫ z := by
    rw [← h₂, hd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hd, hdz, ← Category.assoc, ← pullback.condition, Category.assoc]

end AlgebraicGeometry
