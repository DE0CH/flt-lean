/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Spreading a proper smooth `ℚ`-scheme out over `ℤ[1/N]`

A proper smooth scheme over `Spec ℚ` is defined by finitely many equations with finitely
many rational coefficients, so it is already defined over `ℤ[1/N]` for a single `N ≠ 0` --
and properness and smoothness, being finitely presented conditions, hold over `ℤ[1/M]` for
some multiple `M` of `N`.  This is **EGA IV 8.8.2** (descent of the object along a filtered
limit of bases), **8.10.5** (descent of properness) and **11.2.6 / 17.7.8** (descent of
flatness and smoothness), specialised to the single limit

  `Spec ℚ = lim_N Spec ℤ[1/N]`.

## Why this module exists, and what it is for

`Fermat/FLT/ModularCurve/X0.lean`'s Néron--Ogg--Shafarevich leaf `exists_inertiaSet_geomPt`
needs a model of an abelian variety over `Spec ℤ_(q)` for all but finitely many primes `q`,
and **cannot even state** étaleness of `[p]` on such a model until the model exists:
`AbelianSchemeStruct` is a structure on a morphism to `Spec ℚ` and carries no reduction of
any kind.  Spreading out is the first sub-node of that, and the one where no Néron model is
needed -- the generic fibre is already proper and smooth, so this is pure limit formalism.

The consumer-facing statement is `exists_properSmooth_subringModel`: it produces ONE `N ≠ 0`
and then, for **every** subring `R ⊆ ℚ` in which `N` is invertible -- in particular
`ℤ_(q)` for every prime `q ∤ N` -- a proper smooth `R`-scheme whose base change to `ℚ` is
the given scheme.

## Main statements

* `zinvSubring N` -- the subring `ℤ[1/N] ⊆ ℚ`, and its elementary API.
* `exists_zinvModel_of_finitePresentation` -- **SORRY LEAF**, EGA IV 8.8.2: the *object*
  descends.  (The 2026-07-29 audit in `ProperPushforward.lean` cites Stacks 01ZM for the
  same statement; the EGA number is the one checked here.)
* `exists_isProper_baseChange_zinvModel` -- **SORRY LEAF**, EGA IV 8.10.5: *properness*
  descends to a finite stage.
* `exists_smooth_baseChange_zinvModel` -- **SORRY LEAF**, EGA IV 11.2.6 + 17.7.8:
  *smoothness* descends to a finite stage.  A different citation from the previous one, and
  neither needs the other, which is why they are two leaves.
* `exists_properSmooth_zinvModel` -- PROVEN over those three.
* `exists_properSmooth_subringModel` -- PROVEN; the form the `X0.lean` consumer wants.
* `isProper_smooth_of_properSmooth_model`, `isIso_of_isPullback_specRatToSubring_id`,
  `exists_properSmooth_zinvModel_id` -- PROVEN faithfulness certificates for the leaves
  (see the audit on each leaf).
* `exists_isPullback_pullbackSnd_specSubringMap` -- PROVEN; base-changing a model twice is
  base-changing it once, which is what combines the two property-descent stages.

## WHY THE CONCRETE FORM, NOT THE GENERAL ONE

`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` is a 1371-line development of
EGA IV 8 / Stacks 01YT: inverse limits of schemes with affine transition maps, with
`Scheme.exists_isAffine_of_isLimit`, `Scheme.exists_isOpenCover_and_isAffine`,
`nonempty_isColimit_Γ_mapCocone` and `Scheme.preservesColimit_yoneda` (EGA IV 8.14.2,
`Hom_S(lim Dᵢ, X) = colim Hom_{Sᵢ}(Dᵢ, X)` for `X` locally of finite presentation).  What
it does **not** contain -- checked 2026-08-01, and this matches the correction recorded in
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean` on 2026-07-29 -- is **object
descent**: given `X` locally of finite presentation over `S = lim Sᵢ`, produce an index `i`
and `Xᵢ ⟶ Sᵢ` with `X ≅ Xᵢ ×_{Sᵢ} S`.  Mathlib has the *morphism* half and not the *object*
half.

So a general statement here would have to quantify over an arbitrary cofiltered diagram
with affine transition maps, and would still be a `sorry`.  The concrete form costs the
consumer nothing (it only ever instantiates at `ℚ`), states the arithmetic in the
vocabulary `X0.lean` and `Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean` already use
(`Subring ℚ`), and -- the deciding reason -- lets the surrounding glue be **proven** rather
than left as a second layer of limit bookkeeping.  Everything except the three named
citations below is discharged in this file.

A prover who later wants the general form should state it over
`AffineTransitionLimit.lean`'s `(D : I ⥤ Scheme) (t : D ⟶ (Functor.const I).obj S)
(c : Cone D) (hc : IsLimit c)` and derive these three leaves from it; that is a strict
generalisation and nothing here would have to change except the three proofs.

## THE LIMIT PRESENTATION IS NOT USED, AND IS NOT NEEDED HERE

`Spec ℚ = lim_N Spec ℤ[1/N]` is true and provable at this pin -- `Spec` is a right adjoint
(`ΓSpec.adjunction`), so it carries the filtered colimit `ℚ = colim_N ℤ[1/N]` in
`CommRingCat` to a limit of schemes, and the transition maps are affine because every scheme
in sight is.  The colimit statement is exactly `mem_zinvSubring_den` +
`zinvSubring_le_zinvSubring_of_dvd` below, which are PROVEN.  It is deliberately **not**
built here: nothing in this file's statements mentions it, so building it would be
free-floating code.  It is the first thing to write when someone attacks
`exists_zinvModel_of_finitePresentation`, and the two lemmas it needs are already here.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ## `ℤ[1/N]` as a subring of `ℚ` -/

/-- `ℤ[1/N] ⊆ ℚ`, as a `Subring`.  Note `zinvSubring 0 = zinvSubring 1 = ℤ`, since
`(0 : ℚ)⁻¹ = 0`; every statement below that cares carries `N ≠ 0` for the CONSUMER's sake
(see `exists_properSmooth_subringModel`), never because the mathematics needs it. -/
def zinvSubring (N : ℕ) : Subring ℚ := Subring.closure {((N : ℚ))⁻¹}

theorem inv_natCast_mem_zinvSubring (N : ℕ) : ((N : ℚ))⁻¹ ∈ zinvSubring N :=
  Subring.subset_closure rfl

/-- A subring of `ℚ` contains `ℤ[1/N]` exactly when it inverts `N`.  This is the whole
interface the consumer needs: to get a model over `ℤ_(q)` it has only to check
`((N : ℚ))⁻¹ ∈ ℤ_(q)`, i.e. `q ∤ N`. -/
theorem zinvSubring_le_iff {N : ℕ} {R : Subring ℚ} :
    zinvSubring N ≤ R ↔ ((N : ℚ))⁻¹ ∈ R := by
  rw [zinvSubring, Subring.closure_le, Set.singleton_subset_iff]
  rfl

/-- The family `N ↦ ℤ[1/N]` is directed: it grows along divisibility. -/
theorem zinvSubring_le_zinvSubring_of_dvd {N M : ℕ} (hNM : N ∣ M) (hM : M ≠ 0) :
    zinvSubring N ≤ zinvSubring M := by
  obtain ⟨k, rfl⟩ := hNM
  have hN : (N : ℚ) ≠ 0 := by
    rintro h
    exact hM (by simpa using Or.inl (Nat.cast_eq_zero.mp h))
  have hk : (k : ℚ) ≠ 0 := by
    rintro h
    exact hM (by simpa using Or.inr (Nat.cast_eq_zero.mp h))
  rw [zinvSubring_le_iff]
  have : ((N : ℚ))⁻¹ = (k : ℚ) * ((N * k : ℕ) : ℚ)⁻¹ := by
    push_cast
    field_simp
  rw [this]
  exact Subring.mul_mem _ (natCast_mem _ _) (inv_natCast_mem_zinvSubring _)

/-- Every rational number lies in `ℤ[1/N]` for `N` its denominator.  Together with
`zinvSubring_le_zinvSubring_of_dvd` this is the statement `ℚ = colim_N ℤ[1/N]`, which is
what makes `exists_zinvModel_of_finitePresentation` true. -/
theorem mem_zinvSubring_den (x : ℚ) : x ∈ zinvSubring x.den := by
  have h : (x.num : ℚ) * ((x.den : ℚ))⁻¹ ∈ zinvSubring x.den :=
    Subring.mul_mem _ (intCast_mem _ _) (inv_natCast_mem_zinvSubring _)
  rwa [← div_eq_mul_inv, Rat.num_div_den] at h

theorem exists_ne_zero_mem_zinvSubring (x : ℚ) : ∃ N : ℕ, N ≠ 0 ∧ x ∈ zinvSubring N :=
  ⟨x.den, x.den_nz, mem_zinvSubring_den x⟩

/-! ## The arithmetic bases as schemes -/

/-- `Spec ℚ ⟶ Spec R` for a subring `R ⊆ ℚ`: the generic point of the arithmetic base. -/
noncomputable def specRatToSubring (R : Subring ℚ) :
    Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ↥R) :=
  Spec.map (CommRingCat.ofHom R.subtype)

/-- `Spec S ⟶ Spec R` for an inclusion `R ≤ S` of subrings of `ℚ`. -/
noncomputable def specSubringMap {R S : Subring ℚ} (h : R ≤ S) :
    Spec (CommRingCat.of ↥S) ⟶ Spec (CommRingCat.of ↥R) :=
  Spec.map (CommRingCat.ofHom (Subring.inclusion h))

@[reassoc (attr := simp)]
theorem specRatToSubring_comp_specSubringMap {R S : Subring ℚ} (h : R ≤ S) :
    specRatToSubring S ≫ specSubringMap h = specRatToSubring R := by
  rw [specRatToSubring, specSubringMap, specRatToSubring, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem specSubringMap_comp {R S T : Subring ℚ} (hRS : R ≤ S) (hST : S ≤ T) :
    specSubringMap hST ≫ specSubringMap hRS = specSubringMap (hRS.trans hST) := by
  rw [specSubringMap, specSubringMap, specSubringMap, ← Spec.map_comp]
  rfl

/-- **Base-changing a model twice is base-changing it once.**  The canonical comparison
`XZ ×_R T ⟶ XZ ×_R S` is cartesian over `Spec T ⟶ Spec S`, so every base-change-stable
property of `XZ ×_R S ⟶ Spec S` is inherited by `XZ ×_R T ⟶ Spec T`.  PROVEN, and it is
what lets the two property-descent leaves below be combined at a common stage. -/
theorem exists_isPullback_pullbackSnd_specSubringMap {R S T : Subring ℚ} (hRS : R ≤ S)
    (hST : S ≤ T) {XZ : Scheme.{0}} (fZ : XZ ⟶ Spec (CommRingCat.of ↥R)) :
    ∃ u : pullback fZ (specSubringMap (hRS.trans hST)) ⟶ pullback fZ (specSubringMap hRS),
      IsPullback u (pullback.snd fZ (specSubringMap (hRS.trans hST)))
        (pullback.snd fZ (specSubringMap hRS)) (specSubringMap hST) := by
  have t : IsPullback (pullback.fst fZ (specSubringMap hRS))
      (pullback.snd fZ (specSubringMap hRS)) fZ (specSubringMap hRS) :=
    IsPullback.of_hasPullback _ _
  have s : IsPullback (pullback.fst fZ (specSubringMap (hRS.trans hST)))
      (pullback.snd fZ (specSubringMap (hRS.trans hST))) fZ (specSubringMap (hRS.trans hST)) :=
    IsPullback.of_hasPullback _ _
  have hw : pullback.fst fZ (specSubringMap (hRS.trans hST)) ≫ fZ =
      (pullback.snd fZ (specSubringMap (hRS.trans hST)) ≫ specSubringMap hST) ≫
        specSubringMap hRS := by
    rw [Category.assoc, specSubringMap_comp]
    exact s.w
  refine ⟨t.lift (pullback.fst fZ (specSubringMap (hRS.trans hST)))
    (pullback.snd fZ (specSubringMap (hRS.trans hST)) ≫ specSubringMap hST) hw, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst fZ (specSubringMap hRS)) ?_
    (t.lift_snd _ _ _) t
  rw [t.lift_fst, specSubringMap_comp]
  exact s

/-! ## The three citation leaves

Both are stated about `f : X ⟶ Spec ℚ` and pin the generic fibre by an explicit
`IsPullback` square.  Read the FAITHFULNESS AUDIT on each before attacking it. -/

/-- **EGA IV 8.8.2, at the limit `Spec ℚ = lim_N Spec ℤ[1/N]`: the OBJECT descends**
(sorry leaf, cut 2026-08-01).

A quasi-compact quasi-separated scheme of finite presentation over `ℚ` is already defined
over `ℤ[1/N]` for some `N ≠ 0`, compatibly: the square

```
    X  ────φ────▶  XZ
    │              │
    f              fZ
    ▼              ▼
  Spec ℚ ──────▶ Spec ℤ[1/N]
```

is cartesian.

## THE PROOF, so that nobody re-derives the shape

`ℚ = colim_N ℤ[1/N]` (`mem_zinvSubring_den` + `zinvSubring_le_zinvSubring_of_dvd` above,
both PROVEN), so `Spec ℚ = lim_N Spec ℤ[1/N]` with affine transition maps, `Spec` being a
right adjoint.  Then: cover `X` by finitely many affines (`QuasiCompact f`); each affine is
`Spec` of a finitely presented `ℚ`-algebra, and a finitely presented algebra over a filtered
colimit descends to a finite stage (`Mathlib/Algebra/Category/Ring/FinitePresentation.lean`);
the gluing data descends because `Hom` into a locally-finitely-presented scheme is a filtered
colimit (`AlgebraicGeometry.Scheme.preservesColimit_yoneda`, EGA IV 8.14.2, IN THE PIN); and
the cocycle condition descends because the colimit is FILTERED (finitely many equations
between finitely many morphisms, each holding at some stage, all hold at a common stage).
`QuasiSeparated f` is what makes the intersections quasi-compact, so that finitely many
equations suffice.

## WHAT IS AND IS NOT IN THE PIN (checked 2026-08-01)

`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` HAS the limit machinery and the
*morphism* half of approximation; it does NOT have this object-descent statement.  See the
module docstring.  `Mathlib/AlgebraicGeometry/SpreadingOut.lean` is a DIFFERENT theorem --
it spreads a morphism defined on stalks out to an open neighbourhood -- and gives nothing
here.

## FAITHFULNESS AUDIT (2026-08-01)

**NOT VACUOUS, and the pullback square is the whole reason.**  Drop it and
`XZ := Spec ℤ[1/N]`, `fZ := 𝟙` satisfies every remaining clause for EVERY `X`, so the
statement would be trivially true and useless.  With it, `X` is determined by `XZ` up to
canonical isomorphism, and the degenerate witness is refuted:
`isIso_of_isPullback_specRatToSubring_id` below PROVES that a cartesian square over
`fZ = 𝟙` forces `f` to be an isomorphism.

**Every hypothesis is load-bearing, and each is CONVERSELY implied by the conclusion**, so
none may be dropped: `QuasiCompact`, `QuasiSeparated` and `LocallyOfFinitePresentation` are
all stable under base change, so the cartesian square carries each clause of the conclusion
back to the corresponding hypothesis on `f`.  (`isProper_smooth_of_properSmooth_model`
below is this argument written out for the two properties the consumer cares about.)

**`N ≠ 0` is free for the prover and load-bearing for the consumer.**  `zinvSubring 0 =
zinvSubring 1 = ℤ`, so a witness at `N = 0` is a witness at `N = 1`; and the consumer needs
`N ≠ 0` for `{q prime : q ∤ N}` to be cofinite, which is the whole point of the statement.
It is therefore NOT the clause that makes the leaf true -- there is no claim here that a
model exists over `ℤ`, which would be FALSE (an elliptic curve over `ℚ` with bad reduction
has no proper smooth model over `Spec ℤ`; indeed by Fontaine and Abrashkin there is no
nonzero abelian scheme over `Spec ℤ` at all).  What makes the leaf true is the `∃ N`.

**The base may be taken of the form `ℤ[1/N]` with no loss.**  A subring of `ℚ` is `ℤ[1/S]`
for a set `S` of primes, and a finitely generated one has `S` finite, hence equals
`ℤ[1/N]` for `N` the product of `S`.  So restricting the shape of the base costs nothing;
the descent produces a finitely generated base by construction. -/
theorem exists_zinvModel_of_finitePresentation
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f] :
    ∃ (N : ℕ) (_ : N ≠ 0) (XZ : Scheme.{0}) (fZ : XZ ⟶ Spec (CommRingCat.of ↥(zinvSubring N)))
      (φ : X ⟶ XZ), QuasiCompact fZ ∧ QuasiSeparated fZ ∧ LocallyOfFinitePresentation fZ ∧
        IsPullback φ f fZ (specRatToSubring (zinvSubring N)) :=
  sorry

/-- **EGA IV 8.10.5: PROPERNESS descends to a finite stage** (sorry leaf, cut 2026-08-01).

Given a finitely presented model `fZ` over `ℤ[1/N]` whose base change to `ℚ` is proper, some
further localisation `ℤ[1/M]` -- `M` a multiple of `N` -- already sees properness.  The model
over `ℤ[1/M]` is the CANONICAL base change `pullback.snd fZ (specSubringMap hNM)`, so no new
scheme is existentially quantified and its compatibility with `fZ` is automatic.

## THE PROOF

`IsProper` is `IsSeparated ⊓ UniversallyClosed ⊓ LocallyOfFiniteType ⊓ QuasiCompact`.  Three
of the four are already hypotheses here (`LocallyOfFiniteType` follows from
`LocallyOfFinitePresentation`), and all four are stable under base change, so the content is
universal closedness alone.  That is EGA IV 8.10.5: a constructible-set argument -- the image
of the closed complement of a chart is constructible, is empty at the limit, and a
constructible set empty at the limit of a filtered system is empty at a finite stage.

## FAITHFULNESS AUDIT (2026-08-01)

**NOT VACUOUS.**  The conclusion is about the CANONICAL base change of the given `fZ`, so
there is no existentially quantified scheme that could satisfy it junk-wise; the only freedom
is `M`.  It is inhabited -- see `exists_properSmooth_zinvModel_id` below, which exhibits the
whole chain at `X = Spec ℚ`, `f = 𝟙`.

**`hp` is load-bearing and is EXACTLY necessary.**  If the conclusion holds at `M` then `f`
is proper, being the base change of `pullback.snd fZ (specSubringMap hNM)` along
`Spec ℚ ⟶ Spec ℤ[1/M]` (paste `sq` with the pullback square, exactly as
`exists_properSmooth_zinvModel` below does).  So hypothesis and conclusion are equivalent
here and the hypothesis cannot be weakened; `isProper_smooth_of_properSmooth_model` below is
this argument, PROVEN.

**`sq` is load-bearing and is the ONLY thing tying `fZ` to `f`.**  Without it `fZ` is an
arbitrary finitely presented morphism and the statement is FALSE: take `N = 1` and
`fZ : Spec ℤ[x] ⟶ Spec ℤ`, which is finitely presented and even smooth, together with
`X = Spec ℚ`, `f = 𝟙` (proper).  No base change of `fZ` along `ℤ ⟶ ℤ[1/M]` is proper, the
affine line over a nonzero ring never being universally closed.

**`LocallyOfFinitePresentation fZ` is load-bearing.**  It is what the citation asks for, it
is free at the call site (`exists_zinvModel_of_finitePresentation` produces it), and dropping
it would make the leaf harder rather than easier.  Kept for that reason; no witness against
the weaker hypothesis is claimed here.

**`_hN : N ≠ 0` is DECORATION on this leaf** -- nothing in the conclusion needs it, and
`zinvSubring 0 = zinvSubring 1` anyway.  It is carried only because the call site holds it
for free.  It is load-bearing for the CONSUMER, not here; see
`exists_properSmooth_subringModel`. -/
theorem exists_isProper_baseChange_zinvModel
    {N : ℕ} (_hN : N ≠ 0) {XZ : Scheme.{0}}
    (fZ : XZ ⟶ Spec (CommRingCat.of ↥(zinvSubring N)))
    [QuasiCompact fZ] [QuasiSeparated fZ] [LocallyOfFinitePresentation fZ]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℚ)} {φ : X ⟶ XZ}
    (_sq : IsPullback φ f fZ (specRatToSubring (zinvSubring N)))
    (_hp : IsProper f) :
    ∃ (M : ℕ) (_ : M ≠ 0) (hNM : zinvSubring N ≤ zinvSubring M),
      IsProper (pullback.snd fZ (specSubringMap hNM)) :=
  sorry

/-- **EGA IV 11.2.6 (flatness) + 17.7.8 (smoothness): SMOOTHNESS descends to a finite stage**
(sorry leaf, cut 2026-08-01).

The sibling of `exists_isProper_baseChange_zinvModel`, and a genuinely different citation:
properness descends by a constructible-set argument on the topology, smoothness by a
finite-presentation argument on the Jacobian.  Neither implies the other and neither is
needed for the other, which is why they are two leaves and not one.

## THE PROOF

Smoothness is flat + locally of finite presentation + smooth geometric fibres, and each is a
condition expressible by finitely many equations and inequations in the finitely many
coefficients of a chart: flatness descends by EGA IV 11.2.6 and the Jacobian criterion
descends by EGA IV 17.7.8.  So smoothness of the base change to `ℚ` -- which is the limit --
is already visible at a finite stage.

## FAITHFULNESS AUDIT (2026-08-01)

**NOT VACUOUS**, for the same reason as its sibling: the conclusion constrains the CANONICAL
base change of the given `fZ`, and is inhabited by `exists_properSmooth_zinvModel_id`.

**`hs` is load-bearing and EXACTLY necessary** -- the conclusion at `M` implies `Smooth f` by
base change along `Spec ℚ ⟶ Spec ℤ[1/M]`, which is
`isProper_smooth_of_properSmooth_model` below, PROVEN.

**`sq` is load-bearing.**  Without it, take `N = 1`, `X = Spec ℚ`, `f = 𝟙` (smooth) and
`fZ : Spec (ℤ[x]/(x²)) ⟶ Spec ℤ`, which is finitely presented and is not smooth after ANY
base change to `ℤ[1/M]` -- `ℤ[1/M][x]/(x²)` is not reduced, while a smooth algebra over a
reduced ring is reduced.  So the statement without `sq` is FALSE.

**PROPERNESS IS NOT ASSUMED HERE, deliberately.**  Smoothness descent is a local statement and
does not see the topology; requiring `IsProper f` would make this leaf strictly harder to
apply and would not make it easier to prove.  A prover who wants both at once should prove
this and its sibling separately and combine them with
`exists_isPullback_pullbackSnd_specSubringMap` above, which is exactly what
`exists_properSmooth_zinvModel` does. -/
theorem exists_smooth_baseChange_zinvModel
    {N : ℕ} (_hN : N ≠ 0) {XZ : Scheme.{0}}
    (fZ : XZ ⟶ Spec (CommRingCat.of ↥(zinvSubring N)))
    [QuasiCompact fZ] [QuasiSeparated fZ] [LocallyOfFinitePresentation fZ]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℚ)} {φ : X ⟶ XZ}
    (_sq : IsPullback φ f fZ (specRatToSubring (zinvSubring N)))
    (_hs : Smooth f) :
    ∃ (M : ℕ) (_ : M ≠ 0) (hNM : zinvSubring N ≤ zinvSubring M),
      Smooth (pullback.snd fZ (specSubringMap hNM)) :=
  sorry

/-! ## Faithfulness certificates for the leaves

These are PROVEN, and they are what the audits above cite. -/

/-- **The degenerate witness is refuted.**  If a cartesian square presents `X` as the base
change of the IDENTITY of `Spec R`, then `f` is an isomorphism.  So the clause
"`XZ := Spec ℤ[1/N]`, `fZ := 𝟙`" -- which satisfies every non-cartesian clause of both
leaves above, for every `X` -- forces `X ≅ Spec ℚ`, and the leaves are not vacuous. -/
theorem isIso_of_isPullback_specRatToSubring_id {R : Subring ℚ} {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)} {φ : X ⟶ Spec (CommRingCat.of ↥R)}
    (sq : IsPullback φ f (𝟙 (Spec (CommRingCat.of ↥R))) (specRatToSubring R)) : IsIso f :=
  sq.isIso_snd_of_isIso

/-- **The two hypotheses `IsProper f` and `Smooth f` are exactly necessary**: they follow
from the conclusion of `exists_properSmooth_zinvModel` by base change.  So neither may be
dropped, and the leaves are stated at the sharp generality. -/
theorem isProper_smooth_of_properSmooth_model {R : Subring ℚ} {X XR : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of ℚ)} {fR : XR ⟶ Spec (CommRingCat.of ↥R)} {φ : X ⟶ XR}
    (sq : IsPullback φ f fR (specRatToSubring R)) (hp : IsProper fR) (hs : Smooth fR) :
    IsProper f ∧ Smooth f :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hp,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hs⟩

/-- **The conclusion of `exists_properSmooth_zinvModel` is INHABITED**, so the three leaves
above are jointly satisfiable and none of them is a disguised contradiction: at
`X = Spec ℚ`, `f = 𝟙`, the model over `ℤ = ℤ[1/1]` is `𝟙 (Spec ℤ)`, and `Spec ℚ` really is
its base change.  PROVEN, with no appeal to any leaf.

This is the positive half of the faithfulness audit; `isIso_of_isPullback_specRatToSubring_id`
is the negative half, and together they say that the cartesian square is exactly as strong as
it should be -- satisfiable, and satisfiable at `fZ = 𝟙` only for `X ≅ Spec ℚ`. -/
theorem exists_properSmooth_zinvModel_id :
    ∃ (N : ℕ) (_ : N ≠ 0) (XZ : Scheme.{0})
      (fZ : XZ ⟶ Spec (CommRingCat.of ↥(zinvSubring N))) (φ : Spec (CommRingCat.of ℚ) ⟶ XZ),
      IsProper fZ ∧ Smooth fZ ∧
        IsPullback φ (𝟙 (Spec (CommRingCat.of ℚ))) fZ (specRatToSubring (zinvSubring N)) :=
  ⟨1, one_ne_zero, _, 𝟙 _, specRatToSubring (zinvSubring 1),
    inferInstance, inferInstance, IsPullback.of_id_snd⟩

/-! ## The assembly, and the consumer-facing statement -/

/-- **A proper smooth `ℚ`-scheme has a proper smooth model over `ℤ[1/N]` for some `N ≠ 0`,
with the given scheme as its generic fibre.**  PROVEN over the three citation leaves above.

This is the statement `X0.lean`'s `exists_inertiaSet_geomPt` docstring names as its first
sub-node: *"a proper smooth `J → Spec ℚ` descends to a proper smooth scheme over
`Spec ℤ[1/N]` for some `N`"*.

The two property-descent leaves are combined at `M = M₁ * M₂` by
`exists_isPullback_pullbackSnd_specSubringMap`: each property is stable under the further
base change from its own stage to the common one.  Note the two proofs of
`zinvSubring N ≤ zinvSubring (M₁ * M₂)` obtained that way are definitionally equal by proof
irrelevance, which is why no transport appears below. -/
theorem exists_properSmooth_zinvModel {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f] [Smooth f] :
    ∃ (N : ℕ) (_ : N ≠ 0) (XZ : Scheme.{0})
      (fZ : XZ ⟶ Spec (CommRingCat.of ↥(zinvSubring N))) (φ : X ⟶ XZ),
      IsProper fZ ∧ Smooth fZ ∧ IsPullback φ f fZ (specRatToSubring (zinvSubring N)) := by
  obtain ⟨N, hN, XZ, fZ, φ, hqc, hqs, hfp, sq⟩ :=
    exists_zinvModel_of_finitePresentation f
  obtain ⟨M₁, hM₁, h₁, hprop₁⟩ :=
    exists_isProper_baseChange_zinvModel hN fZ sq ‹IsProper f›
  obtain ⟨M₂, hM₂, h₂, hsm₂⟩ :=
    exists_smooth_baseChange_zinvModel hN fZ sq ‹Smooth f›
  -- combine the two stages at `M = M₁ * M₂`
  have hM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero hM₁ hM₂
  have hu₁ : zinvSubring M₁ ≤ zinvSubring (M₁ * M₂) :=
    zinvSubring_le_zinvSubring_of_dvd ⟨M₂, rfl⟩ hM
  have hu₂ : zinvSubring M₂ ≤ zinvSubring (M₁ * M₂) :=
    zinvSubring_le_zinvSubring_of_dvd ⟨M₁, mul_comm M₁ M₂⟩ hM
  have hNM : zinvSubring N ≤ zinvSubring (M₁ * M₂) := h₁.trans hu₁
  have hprop : IsProper (pullback.snd fZ (specSubringMap hNM)) := by
    obtain ⟨u, hu⟩ := exists_isPullback_pullbackSnd_specSubringMap h₁ hu₁ fZ
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hu hprop₁
  have hsm : Smooth (pullback.snd fZ (specSubringMap hNM)) := by
    obtain ⟨u, hu⟩ := exists_isPullback_pullbackSnd_specSubringMap h₂ hu₂ fZ
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hu hsm₂
  clear hprop₁ hsm₂
  -- the model over `ℤ[1/M]` is the canonical base change of `fZ`
  set M := M₁ * M₂ with hMdef
  set g := specSubringMap hNM with hg
  have t : IsPullback (pullback.fst fZ g) (pullback.snd fZ g) fZ g :=
    IsPullback.of_hasPullback fZ g
  have hcomp : specRatToSubring (zinvSubring M) ≫ g = specRatToSubring (zinvSubring N) :=
    specRatToSubring_comp_specSubringMap hNM
  have hw : φ ≫ fZ = (f ≫ specRatToSubring (zinvSubring M)) ≫ g := by
    rw [Category.assoc, hcomp]; exact sq.w
  refine ⟨M, hM, pullback fZ g, pullback.snd fZ g,
    t.lift φ (f ≫ specRatToSubring (zinvSubring M)) hw, hprop, hsm, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst fZ g) ?_ (t.lift_snd _ _ _) t
  rw [t.lift_fst, hcomp]
  exact sq

/-- **The form the `X0.lean` consumer wants.**  One `N ≠ 0` works for EVERY subring of `ℚ`
in which `N` is invertible: for a prime `q ∤ N` take `R = ℤ_(q)` and this hands over a
proper smooth `ℤ_(q)`-scheme whose generic fibre is `X`.  PROVEN.

The `((N : ℚ))⁻¹ ∈ R` hypothesis is the whole interface: by `zinvSubring_le_iff` it is
equivalent to `ℤ[1/N] ≤ R`, and it is what a consumer checks by hand at `R = ℤ_(q)`. -/
theorem exists_properSmooth_subringModel {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f] [Smooth f] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ R : Subring ℚ, ((N : ℚ))⁻¹ ∈ R →
      ∃ (XR : Scheme.{0}) (fR : XR ⟶ Spec (CommRingCat.of ↥R)) (φ : X ⟶ XR),
        IsProper fR ∧ Smooth fR ∧ IsPullback φ f fR (specRatToSubring R) := by
  obtain ⟨N, hN, XZ, fZ, φ, hprop, hsm, sq⟩ := exists_properSmooth_zinvModel f
  refine ⟨N, hN, fun R hR => ?_⟩
  have hle : zinvSubring N ≤ R := zinvSubring_le_iff.2 hR
  set g := specSubringMap hle with hg
  have t : IsPullback (pullback.fst fZ g) (pullback.snd fZ g) fZ g :=
    IsPullback.of_hasPullback fZ g
  have hcomp : specRatToSubring R ≫ g = specRatToSubring (zinvSubring N) :=
    specRatToSubring_comp_specSubringMap hle
  have hw : φ ≫ fZ = (f ≫ specRatToSubring R) ≫ g := by
    rw [Category.assoc, hcomp]; exact sq.w
  have hprop' : IsProper (pullback.snd fZ g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback t hprop
  have hsm' : Smooth (pullback.snd fZ g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback t hsm
  refine ⟨pullback fZ g, pullback.snd fZ g,
    t.lift φ (f ≫ specRatToSubring R) hw, hprop', hsm', ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst fZ g) ?_ (t.lift_snd _ _ _) t
  rw [t.lift_fst, hcomp]
  exact sq

end AlgebraicGeometry
