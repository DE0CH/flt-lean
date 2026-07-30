/-
ModularCurve/X1.lean — own work for the Fermat project (not vendored from
the FLT project).

# `Y_1(N)` and `X_1(N)` as coarse moduli spaces over `ℚ`

This module is the **`Γ₁` companion of `ModularCurve/X0.lean`**, written
for one consumer: `MazurX1Plane.exists_isX1TwentyFiveDatum` in
`FreyCurve/MazurTorsion.lean`, i.e. Mazur 1977 Thm 8 at level `25`.

## Why a separate `Γ₁` layer, and exactly how much of it is new

`X0.lean` already carries a complete `Γ₀` development — the moduli
problem, its coarse space, the compactification, the cusps, the Jacobian
and the rank-`0` reduction bound.  The level-`25` argument cannot use it,
and not for a fixable reason: `IsX0Compactification`'s `coarse` field
pins `Y` as a coarse space for the **`Γ₀(N)`** problem, and at `N = 25`
the `X_0` route is not merely unavailable but REFUTED.  `X_0(25)` has
genus `0`, and a rational cyclic `25`-isogeny genuinely exists (the class
`11a`), so a rational `25`-subgroup puts **no** constraint on `j(E)`.
The level-`25` statement is about a rational POINT of order `25`, which
is the `Γ₁` problem.

What is genuinely new here is therefore only the **moduli** layer:

* `PointOfExactOrder` — a section of exact order `N`, the `Γ₁(N)`-level
  structure, replacing `CyclicSubgroupOfOrder`;
* `Gamma1Datum`, `IsBaseChangeOfGamma1`, `IsCoarseModuliY1`,
  `IsX1Compactification` — the same four-step tower as `X0.lean`, with
  the level structure swapped.

Everything downstream of the curve is **reused verbatim from `X0.lean`**,
and this is the point of the file's shape:

* `RelPoint`, `RelPoint.pre`, `RelPoint.along`, `sectionAlong`, `SpecQ`,
  `SpecF`, `AbelianSchemeStruct`, `GeomFibrePt`;
* `IsJacobianOf` and **`HasRankZeroJacobian`**, which are stated for an
  arbitrary `strX : X ⟶ SpecQ` and contain nothing `Γ₀`-specific — so
  `hasRankZeroJacobian_x1TwentyFive` is a statement in `X0.lean`'s own
  vocabulary, not a duplicate of it;
* `exists_ellipticScheme_of_weierstrass`, the bridge from a Weierstrass
  curve over `ℚ` to an elliptic scheme.

**RECONCILIATION with `card_le_of_rankZeroJacobian`** (`X0.lean`), which
the level-`25` docstring asked for.  That theorem bounds
`s.card ≤ #X_0(N)(𝔽_ℓ)` for every `Finset s` of rational points.  Its
proof — as its own docstring records — goes through an *injection*
`X(ℚ) ↪ X(𝔽_ℓ)` obtained from Abel–Jacobi plus injectivity of reduction
on the torsion of a rank-`0` Jacobian.  The injection is therefore the
primitive and the cardinality bound is its corollary, so the `Γ₁`
analogue is stated here in the **injective** form
(`exists_injective_reduction_of_rankZeroJacobian`), which is what a
`Nat.card` hypothesis such as `IsX1TwentyFiveDatum.card_ptF3` actually
consumes.  Nothing in `X0.lean` is edited: its `Γ₀`-shaped statement has
several concurrent owners, and the two forms are related by
`Nat.card_le_card_of_injective` at any site that wants both.

## The three inputs at level `25`, and where their weight really sits

`X_1(25)` has genus `12`; `J_1(25)` is `ℚ`-isogenous to `A₄ × A₈` with
`LRatio(A₄, 1) = 1/5041` and `LRatio(A₈, 1) = 1/10272025`, both nonzero,
so `rank J_1(25)(ℚ) = 0` by Kolyvagin–Logachev (or Kato).

* **`hasRankZeroJacobian_x1TwentyFive`** (stated here over `X0.lean`'s
  `HasRankZeroJacobian`) was the deep input.  It is now PROVEN, and the
  level's weight has been localised: the genus half is CLOSED by
  computation (`x1Genus_twentyFive` proves `genus X_1(25) = 12` by
  `decide` on the classical formula), and the rank half is PROVEN over a
  Kolyvagin–Logachev interface that is stated ONCE for `Γ₀` and `Γ₁`
  together.  Of the seven leaves left under it, **two are `X0.lean`
  theorems reused verbatim** — Mordell–Weil
  (`fg_relPoint_of_abelianScheme`) and Riemann–Roch
  (`injective_aj_of_not_isIso_jacobian`), both stated level-freely there
  — **three more are stated here in a form that CONSUMES the
  corresponding `X0.lean` statement**, all three now PROVEN wrappers:
  `exists_jacobianOf_curve` (over `X0.lean`'s two relative-Picard
  theorems) and the two shape-free statements of the Kolyvagin-Logachev
  subsection, whose `.gamma0` branches cite the `Γ₀` theorems and whose
  `.gamma1` branches are the two leaves this layer genuinely owes.  Only
  TWO leaves are specific to this level: the genus bound and the
  computation of the twelve `L`-values of `S_2(Γ_1(25))` at `s = 1`.
  **No second Kolyvagin-Logachev was written**, which was the main risk
  this layer carried.

  (Corrected 2026-07-27: this list previously said the three rows SUBSUME
  the `X0.lean` statements and that the Kolyvagin rows were leaves.  The
  `Γ₀` statements are PROVEN over finer cuts, so the arrow points the
  other way; see the Kolyvagin–Logachev subsection docstring.)
* **`exists_x1Compactification_mod_prime` at `(25, 3, 10)` is SHALLOW**,
  and this corrects the impression left by the level-`25` docstring that
  `#X_1(25)(𝔽_3) = 10` is an Eichler–Shimura computation.  It is not.
  It is now PROVEN (2026-07-27) over four leaves, three of which carry no
  modular content at all; see its docstring for the split.
  The value equals `φ(25)/2`, which is the *cusp count*, so the content
  is "`X_1(25)` has no non-cuspidal `𝔽_3`-point" — i.e. no pair
  `(E, P)/𝔽_3` with `P` of order `25`.  A point of order `25` in
  `E(𝔽_3)` forces `25 ∣ #E(𝔽_3)`, and Hasse gives
  `#E(𝔽_3) ≤ 3 + 1 + 2√3 < 8`; indeed the crude Weierstrass bound
  `#E(𝔽_q) ≤ 2q + 1 = 7` already suffices and needs no Hasse at all.
  Corroborated: `G₂₅ mod 3` vanishes on `𝔽_3 × 𝔽_3` only at `(0, 0)`.
  See that theorem's docstring for the decomposition and for the one
  genuinely modular half that remains (the `10` cusps over `𝔽_3`).
* **`exists_rationalCuspsX1`** needs only the EASY half of Ogg's cusp
  description, for the reason `X0.lean`'s `CuspIndexing` records: an
  injection suffices, so the classification of which cusps are *not*
  rational is not an obligation here.

## Faithfulness note carried out of the `gp` reconnaissance

`MazurX1Plane.IsX1TwentyFiveDatum.exists_notCusp_of_plane` was originally
stated for arbitrary `b c : ℚ` with `G₂₅(b, c) = 0`, `b ≠ 0`, `b ≠ c`,
with no non-degeneracy on `tateNormalForm b c`.  As stated it carried a
hidden obligation that has nothing to do with modular curves: a rational
point of the plane model at which the family DEGENERATES would be a cusp,
so producing a *non*-cuspidal point from it is not possible.  The locus
is empty — writing `Δ = b³ · D₀` with
`D₀ = c⁴ − 3c³ + (−8b+3)c² + (−20b−1)c + 16b² + b`, one has
`Res_c(G₂₅, D₀) = b^90 · Q(b)` with `Q` monic of degree `10`,
**irreducible over `ℚ`** and with constant term `−1`, hence with no
rational root at all — but discharging that in Lean needs a bivariate
elimination certificate with cofactors of the size of `G₂₅` itself.
Since the sole consumer (`x1TwentyFive_plane_ne_zero`) carries
`[IsElliptic]` already, the hypothesis is now carried by the field
instead.  The certificate is recorded there so that a successor wanting
the general form knows exactly what to prove.
-/
module

public import Fermat.FLT.ModularCurve.X0
-- `IsCurveReductionModel`, `IsNeronReductionDatum` and
-- `exists_neronReductionDatum_of_curveModel`: the moduli-free core of the rank-`0`
-- reduction argument, hoisted out of `X0.lean`'s `Γ₀`-shaped packaging so that the
-- `Γ₁` side instantiates it rather than re-mirroring a 200-line structure.  PUBLIC
-- because `IsCurveReductionModel` appears in the SIGNATURE of
-- `exists_x1CurveModel_of_base`, not only in proof bodies.
public import Fermat.FLT.ModularCurve.NeronReduction
-- `CuspSymbolX1`, `cuspFrobX1`, `IsPrimitiveCuspSymbolX1`, `FixedCuspSymbolX1` and
-- `card_fixedCuspSymbolX1`: the `Γ_1(N)∖ℙ¹(ℚ)` cusp combinatorics and the count of the
-- Frobenius-fixed symbols, which is the arithmetic half of Ogg's description of the cusps.
-- PUBLIC because `CuspSymbolX1` and `cuspFrobX1` appear in the SIGNATURE of
-- `exists_cuspSymbolEmbedding_x1_finiteField` below.
public import Fermat.FLT.ModularCurve.CuspSymbolX1
public import Mathlib.NumberTheory.DirichletCharacter.Basic
-- infinite Galois theory: `InfiniteGalois.mem_range_algebraMap_iff_fixed`, the field-theoretic
-- half of `exists_specSection_of_specGal_invariant` below.  `public` because that theorem's
-- statement mentions `Field.absoluteGaloisGroup`; see the private-import trap in the doctrine.
public import Mathlib.FieldTheory.Galois.Infinite
-- the analytic inputs of `exists_cuspForm_gamma1GL_zero_lacunary` below:
-- `differentiableOn_tsum_of_summable_norm` (holomorphy of a locally-uniformly convergent
-- series), `UpperHalfPlane.mdifferentiable_iff` and the `MDiff` notation,
-- `summable_pow_mul_geometric_of_norm_lt_one`, `Real.pi_gt_three`, and
-- `OnePoint.IsZeroAt` / `UpperHalfPlane.IsZeroAtImInfty.slash`.  `public` because `MDiff`
-- appears in the SIGNATURE of `mdiff_lacunaryTwoSeries`; see the private-import trap in
-- the doctrine, whose second shape bites proof bodies too.
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace Fermat

/-! ### Sections, and the `Γ₁(N)`-level structure -/

/-- **The relative point cut out by a section `sec : T ⟶ E`.**

A section of `f : E ⟶ T` gives a `T'`-point of `E` over every
`g : T' ⟶ T`, by precomposition.  Naturality is automatic — the induced
family is `g ↦ g ≫ sec`, so `RelPoint.pre` of it is again of this shape
— which is exactly why the `Γ₁`-level structure below needs no
naturality axiom, whereas `CyclicSubgroupOfOrder` has to state its
conditions at every base. -/
def RelPoint.ofSection {E T : Scheme.{u}} {f : E ⟶ T} (sec : T ⟶ E)
    (hsec : sec ≫ f = 𝟙 T) {T' : Scheme.{u}} (g : T' ⟶ T) : RelPoint f g :=
  ⟨g ≫ sec, by rw [Category.assoc, hsec, Category.comp_id]⟩

/-- **A point of exact order `N` on an abelian scheme**: a section whose
value on every geometric fibre has additive order exactly `N`.

This is the Katz–Mazur `Γ₁(N)`-structure at levels invertible on the
base, which is the only case used here (`N = 25` over `ℚ` and over
`𝔽_3`).  Katz–Mazur's general definition is an inclusion
`(ℤ/N)_T ↪ E[N]` of group schemes; over a base where `N` is invertible
the two agree, and the section form is the one every consumer here
evaluates.

**Why exactness is stated on GEOMETRIC fibres**, matching
`CyclicSubgroupOfOrder.geom_cyclic`: the order of a section is not a
condition that can be tested at a single base, and at a non-reduced base
"order `N`" is not even the right notion.  Testing on geometric fibres is
what makes the condition insensitive to the base and is the form the
descent leaf `nonempty_gamma1Datum_of_ratPoint` naturally produces.

Note that `PointOfExactOrder ab N` refines `CyclicSubgroupOfOrder ab N`:
the multiples of the section span a cyclic subgroup of order `N`.  That
comparison — the forgetful map `X_1(N) → X_0(N)` — is not built here
because nothing below consumes it, and at `N = 25` it is precisely the
map that loses all the information (`X_0(25)` has genus `0`). -/
structure PointOfExactOrder {E T : Scheme.{u}} {f : E ⟶ T}
    (ab : AbelianSchemeStruct f) (N : ℕ) where
  /-- the section carrying the level structure -/
  sec : T ⟶ E
  /-- it really is a section of the structure morphism -/
  sec_comp : sec ≫ f = 𝟙 T
  /-- on every geometric fibre the section has additive order exactly `N` -/
  geom_order : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ T),
      letI := ab.addCommGroup t
      addOrderOf (RelPoint.ofSection sec sec_comp t) = N

/-! ### The `Γ₁(N)`-moduli problem -/

/-- **A `Γ₁(N)`-structure over a scheme `T`**: an elliptic scheme over
`T` together with a point of exact order `N`.

Identical to `Gamma0Datum` except in the level structure, and for the
same reasons: "elliptic scheme" is spelled out as *abelian scheme of
relative dimension one*, `AbelianSchemeStruct f` supplying properness,
smoothness, geometrically connected fibres, a zero section and a
commutative group law on the functor of points.

This is the moduli problem `[Γ₁(N)]` of Katz–Mazur; its coarse space over
`ℚ` is `Y_1(N)`. -/
structure Gamma1Datum (N : ℕ) (T : Scheme.{u}) where
  /-- the total space of the elliptic scheme -/
  E : Scheme.{u}
  /-- the structure morphism of the elliptic scheme -/
  f : E ⟶ T
  /-- the abelian-scheme structure on `f` -/
  ab : AbelianSchemeStruct f
  /-- relative dimension one: the fibres are curves -/
  relativeDimensionOne : SmoothOfRelativeDimension 1 f
  /-- the `Γ₁(N)`-level structure -/
  pt : PointOfExactOrder ab N

/-- **`d'` is a base change of `d` along `h : T' ⟶ T`.**

The `Γ₁` analogue of `IsBaseChangeOf`, and stated the same way rather
than constructed: a morphism `map` on total spaces making a cartesian
square, compatible with the group law and with the level structure.

The level-structure clause is `map_sec`, and it is *simpler* than
`IsBaseChangeOf.liesIn_iff`: a section is transported by a single
equation between morphisms `T' ⟶ d.E`, where a subgroup scheme needs a
biconditional at every base.  Taking `h = 𝟙` recovers isomorphism of
`Γ₁(N)`-data over a fixed base, so a natural transformation out of the
moduli problem is automatically constant on isomorphism classes. -/
structure IsBaseChangeOfGamma1 {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T)
    (d' : Gamma1Datum N T') (d : Gamma1Datum N T) where
  /-- the morphism on total spaces -/
  map : d'.E ⟶ d.E
  /-- the square over `h` is cartesian -/
  isPullback : IsPullback d'.f map h d.f
  /-- the zero section is preserved -/
  map_zero : ∀ {T'' : Scheme.{u}} (g : T'' ⟶ T'),
    RelPoint.along map isPullback.w (d'.ab.zero g) = d.ab.zero (g ≫ h)
  /-- the group law is preserved -/
  map_add : ∀ {T'' : Scheme.{u}} {g : T'' ⟶ T'} (x y : RelPoint d'.f g),
    RelPoint.along map isPullback.w (d'.ab.add x y)
      = d.ab.add (RelPoint.along map isPullback.w x)
          (RelPoint.along map isPullback.w y)
  /-- the level structure is the pullback of the level structure -/
  map_sec : d'.pt.sec ≫ map = h ≫ d.pt.sec

/-! ### The coarse moduli space `Y_1(N)` -/

/-- **`str : Y ⟶ S` is a coarse moduli space for the `Γ₁(N)`-moduli
problem.**

Verbatim the definition of `IsCoarseModuliY0` with `Gamma0Datum` replaced
by `Gamma1Datum`: a classifying map sending a `Γ₁(N)`-structure over an
`S`-scheme `T` to a `T`-point of `Y`, natural in cartesian squares, and
*initial* among all such.  Initiality alone determines `(Y, classify)` up
to unique isomorphism, which is what faithfulness of the level statements
requires; bijectivity on geometric points is deliberately omitted for the
same reason as there.

Over `S = Spec ℚ` the unique such `Y` is the modular curve `Y_1(N)`.

**`Y_1(N)` is a FINE moduli space for `N ≥ 4`** — the automorphism group
of a pair `(E, P)` with `P` of order `≥ 4` is trivial — so at `N = 25`
this coarse space is in fact fine.  That is *not* recorded as a field:
nothing below consumes representability, and asking for it would make the
structure strictly harder to satisfy for no gain.  It is worth knowing
because it is why the `Γ₁` problem is the well-behaved one, and why the
rational points of `Y_1(25)` really are pairs `(E, P)/ℚ` rather than
merely `ℚ̄`-pairs fixed by Galois. -/
structure IsCoarseModuliY1 (N : ℕ) {Y S : Scheme.{u}} (str : Y ⟶ S) where
  /-- the classifying map of the moduli problem -/
  classify : ∀ {T : Scheme.{u}} (g : T ⟶ S), Gamma1Datum N T → RelPoint str g
  /-- the classifying map is natural: a base change of data is sent to the
  precomposed point -/
  classify_natural : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S}
    {g' : T' ⟶ S} (hg : h ≫ g = g') {d' : Gamma1Datum N T'}
    {d : Gamma1Datum N T}, IsBaseChangeOfGamma1 h d' d →
    classify g' d' = RelPoint.pre h hg (classify g d)
  /-- `(Y, classify)` is initial among `S`-schemes receiving a natural
  transformation from the moduli problem -/
  universal : ∀ {Y' : Scheme.{u}} (str' : Y' ⟶ S)
    (c : ∀ {T : Scheme.{u}} (g : T ⟶ S), Gamma1Datum N T → RelPoint str' g),
    (∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
      (hg : h ≫ g = g') {d' : Gamma1Datum N T'} {d : Gamma1Datum N T},
      IsBaseChangeOfGamma1 h d' d → c g' d' = RelPoint.pre h hg (c g d)) →
    ∃! u : Y ⟶ Y', u ≫ str' = str ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (d : Gamma1Datum N T),
        (c g d).1 = (classify g d).1 ≫ u

/-! ### The compactification `X_1(N)`, and its cusps -/

/-- **`strX : X ⟶ S` is the smooth compactification of the coarse moduli
space `strY : Y ⟶ S`, with `jY : Y ⟶ X` the open immersion.**

The `Γ₁` analogue of `IsX0Compactification`, field for field.  `X` is
proper and smooth of relative dimension `1` over `S`, geometrically
connected, and contains `Y` as an open subscheme with FINITE complement —
that complement is the cusp locus.

`finite_compl` is what pins `X` as the genuine `X_1(N)` rather than an
arbitrary curve receiving `Y`; dropping it would make the cusp count
meaningless.  The base `S` is general on purpose: the same structure over
`Spec 𝔽_ℓ` with `ℓ ∤ N` is the good reduction `X_1(N)_{𝔽_ℓ}`, and
`exists_injective_reduction_of_rankZeroJacobian` relates the two. -/
structure IsX1Compactification (N : ℕ) {X Y S : Scheme.{0}} (strX : X ⟶ S)
    (strY : Y ⟶ S) (jY : Y ⟶ X) where
  /-- `jY` is a morphism over the base -/
  comm : jY ≫ strX = strY
  /-- `Y` is a coarse moduli space for the `Γ₁(N)`-problem -/
  coarse : IsCoarseModuliY1 N strY
  /-- `Y` is an open subscheme of `X` -/
  isOpen : IsOpenImmersion jY
  /-- `X` is proper over the base -/
  isProper : IsProper strX
  /-- `X` is a smooth curve over the base -/
  smooth : SmoothOfRelativeDimension 1 strX
  /-- `X` is geometrically connected -/
  connected : GeometricallyConnected strX
  /-- the complement of `Y` in `X` — the cusp locus — is finite -/
  finite_compl : (Set.range jY.base)ᶜ.Finite

/-- **A rational point of the compactification is a cusp when it does not
come from the open part.**

Verbatim `IsX0Compactification.IsCusp`, and phrased through
`sectionAlong` for the same reason: that is the form the consumers use. -/
def IsX1Compactification.IsCusp {N : ℕ} {X Y S : Scheme.{0}} {strX : X ⟶ S}
    {strY : Y ⟶ S} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY)
    (x : RelPoint strX (𝟙 S)) : Prop :=
  ¬ ∃ y : RelPoint strY (𝟙 S), sectionAlong jY h.comm y = x

/-- **The number of `ℚ`-rational cusps of `X_1(N)` that this development
claims**, namely `φ(N)/2`.

The cusps of `X_1(N)` are `Γ_1(N)\ℙ¹(ℚ)`; for `N ≥ 5` there are
`½ Σ_{d ∣ N} φ(d)φ(N/d)` of them (`28` at `N = 25`).  They fall into
Galois orbits, and one distinguished orbit of `φ(N)/2` cusps — indexed by
`(ℤ/N)ˣ/±1` — is `ℚ`-RATIONAL, the Galois action on it being trivial.  At
`N = 25` that is `10`, and the remaining `18` are not rational (one orbit
of `10` is defined over `ℚ(ζ₂₅)⁺`, of degree `10`).

**WHICH orbit is the rational one, corrected 2026-07-28.**  This docstring
used to name it as the orbit lying over the cusp `∞` of `X_0(N)`, and that
is BACKWARDS for the moduli problem this file actually formalises.
`Gamma1Datum` is Katz–Mazur `[Γ₁(N)]`, a POINT of exact order `N`
(`PointOfExactOrder`), not an embedding `μ_N ↪ E`; and in the
Deligne–Rapoport description the rational cusps are then the pairs (Néron
`N`-gon, generator of the component group `ℤ/N`), while the pairs (Néron
`1`-gon, generator of `μ_N`) are defined over `ℚ(ζ_N)⁺`.  The check, over
`K((q))`: the Tate curve `E_q = 𝔾_m/q^ℤ` has `E_q(K((q))) = K((q))ˣ/q^ℤ`,
in which `x = q^k u` (`u` a unit of `K[[q]]`) satisfies `x^m ∈ q^ℤ` iff
`u^m = 1` — so a point of exact order `N` forces `u` to be a primitive
`N`-th root of unity IN `K`, and the `1`-gon orbit carries no `K`-rational
level structure unless `ζ_N + ζ_N⁻¹ ∈ K`.  The `N`-gon orbit instead has
`E_{q^N}` with the level point `q`, defined over `K((q))` for every `K`.
Concretely at `N = 5` over `ℚ`: the two cusps of `X_1(5)` over `∞` have
residue field `ℚ(√5) = ℚ(ζ₅)⁺` and are NOT rational, while the two over
`0` are.  `IsX1Compactification.CuspLocus`'s docstring already recorded
this correctly and is the authority.  The `∞` labelling survives in
several other docstrings in this file; read them in the moduli language
above, since the literature's two conventions for the `(E, P)` model
disagree about the `0`/`∞` LABELS and only the moduli description is
convention-free.

**Nothing in this development depends on the answer.**  The COUNT is
`φ(N)/2` on either convention, and the count is all that is consumed —
`exists_rationalCuspSectionsX1_field` says "some `φ(N)/2` cusps are
rational" and never says which.  The correction matters for the ROUTE, not
for any statement: a prover who takes the `∞`-orbit as the target is trying
to prove that `(1`-gon, `ζ_N)` is `K`-rational, which is FALSE over `ℚ` for
every `N` with `φ(N) > 2`, and false over `𝔽_ℓ` whenever `ζ_N ∉ 𝔽_ℓ`.

**This is deliberately a LOWER bound on the rational cusps, not the exact
count**, which is the same economy `X0.lean`'s
`IsX0Compactification.CuspIndexing` records: the counting arguments need
*enough* distinct rational cusps, never that these are all of them.  So
the hard half of the cusp classification — that no cusp outside the
`∞`-orbit is rational — is not an obligation of this development.  Naming
the quantity `numRationalCuspsX1` rather than `numCuspsOverInfinity` is
therefore a slight abuse, kept for symmetry with `numRationalCusps`; at
`N = 25` the two coincide. -/
def numRationalCuspsX1 (N : ℕ) : ℕ := N.totient / 2

/-- **`numRationalCuspsX1 25 = 10`** (PROVEN, by computation).

`φ(25) = 20`.  Stated so that the level-`25` assembly never has to unfold
the definition, and so that the `10` in `IsX1TwentyFiveDatum.cusp` and the
`10` in `IsX1TwentyFiveDatum.card_ptF3` are visibly the same number — that
coincidence is the entire content of Mazur's counting argument at this
level. -/
theorem numRationalCuspsX1_twentyFive : numRationalCuspsX1 25 = 10 := by
  rw [numRationalCuspsX1]; decide

/-! ### The leaves

These are the `Γ₁`-specific inputs.  Every one of them is TRUE and
classical; none of them is available at this pin, and the module
docstring records which are deep and which are not.

**Reorganised 2026-07-27.**  Three of the former leaves —
`exists_x1Compactification`, `exists_rationalCuspsX1` and
`exists_x1Compactification_mod_prime` — are now THEOREMS, and what was
open in them has been split along the theories it needed:

| open leaf | theory | base |
|---|---|---|
| `exists_gamma1RigidifiedModuliScheme` | Katz-Mazur 4.7.1/4.7.2 + 5.1.1 + 6.6.2: the rigidified moduli problem of `[Γ₁(N)], [Γ(n)]` is REPRESENTABLE, affineness not mentioned.  Split off `exists_gamma1RigidifiedModuli` on 2026-07-30 — that node is now PROVEN over this row and the next, and it is still what `exists_gamma1Rigidification`, `exists_gamma1GITPresentation`, `nonempty_gamma1GITPresentation_of_rigidification`, `isDomain_of_`, `smoothOfRelativeDimension_of_` and `geometricallyConnected_of_gamma1GITPresentation` are PROVEN over. | any `K`, `char K ∤ N`, `char K ∤ n` |
| `isAffine_of_gamma1RigidifiedModuliScheme` | Katz-Mazur, the affineness parenthesis of 8.1.1 and nothing else: `𝔐([Γ₁(N)], [Γ(n)])` is AFFINE.  The second half of the same 2026-07-30 split.  Legitimate as a `∀` because `universal` is a FINE moduli property; see its docstring. | any `K`, `char K ∤ N`, `char K ∤ n` |
| `exists_torsionBasisCover_field` | Katz-Mazur 2.3.1 / 5.1.1, Silverman *AEC* III.6.4: after a flat surjective quasi-compact cover the `n`-torsion of an abelian scheme of relative dimension one acquires a basis.  Stated for a BARE abelian scheme — no `Gamma1Datum`, no moduli scheme — and it is all that is left under `exists_gamma1FullLevelStructure_cover`, which is PROVEN over it (2026-07-28).  It is the general-base form of `X0.lean`'s `exists_torsionBasis_geomPoint` + `exists_torsionBasis_cover_of_geomPoint`, both of which are stated only over `SpecQ`. | any `K`, `char K ∤ n` |
| `isOpenImmersion_equalizer_of_abelianFullLevelStructure` | NO citation beyond Katz–Mazur 2.3.1 — the equalizer of two `n`-torsion sections of an elliptic scheme over an ARBITRARY base carrying a full level-`n` structure is OPEN.  Step 2, and after the 2026-07-30 cut the ONLY step, of `exists_openCover_twist_of_abelianFullLevelStructure`, which is now PROVEN over it and over `exists_openCover_comb_of_abelianFullLevelStructure`; that node in turn is what `exists_gamma1DeckAction` (REFUTED 2026-07-29, restated with its over-`S` clause, then PROVEN) rests on.  Identical to `X0.lean`'s `isOpenImmersion_equalizer_of_nsmul_eq_zero` except that `L` replaces `g : Z ⟶ SpecQ` as the source of invertibility of `n`. | any base scheme, no characteristic hypothesis — see its FALSITY AUDIT for why `L` already pins `n` invertible |
| `smoothCurve_A_of_gamma1GITPresentation` | Katz-Mazur 8.2.1, stated ONCE and on the rigidified ring where 8.2.1 is proved: `Spec A` is a smooth affine curve over `K` (`Algebra.Smooth K A` and `ringKrullDim A = 1`).  Replaced `isReduced_A_of_gamma1GITPresentation` and the dimension conjunct of `smooth_coarseRing_of_gamma1GITPresentation` on 2026-07-28; BOTH of those are now PROVEN over it. | any `K`, `char K ∤ N` |
| `formallySmoothInvariants_of_gamma1GITPresentation` | Deligne-Rapoport III.1, Katz-Mazur 8.2.1: `B = A^G` is FORMALLY smooth over `K`.  Cut 2026-07-30 out of `smoothInvariants_of_gamma1GITPresentation` (now PROVEN over it) by unfolding `Algebra.Smooth` and paying for the second conjunct: `finitePresentation_invariants_of_gamma1GITPresentation` is Noether's theorem on invariants, PROVEN over `smoothCurve_A_of_gamma1GITPresentation` and the new `Gamma1GITPresentation.isScalarTower`.  What is left still needs Stacks `02VL` plus freeness of the `G`-action, neither of which the structure supplies. | any `K`, `char K ∤ N` |
| ~~`exists_weierstrassCurve_pointOfExactOrder`~~ | PROVEN 2026-07-30: Silverman *AEC* III.6.4 was already in cone as `WeierstrassCurve.n_torsion_dimension` (`EllipticCurve/Torsion.lean`), so the leaf was that theorem at `WeierstrassCurve.ofJ (0 : L)` plus additive-order bookkeeping; no longer a leaf | — |
| `nonempty_gamma1Datum_of_weierstrassPoint` | the base-generalisation of `nonempty_gamma1Datum_of_ratPoint`, which is the SAME statement at `ℚ` and is PROVEN.  Its whole obstruction is that `EllipticScheme.lean` is written at the concrete base `ℚ`; no new mathematics.  Cut out of `exists_gamma1Datum_fieldExtension` 2026-07-28, which is PROVEN over it and the row above (and `geometricComponents_of_gamma1GITPresentation` over that plus the two rows below, and `nontrivial_A_of_gamma1GITPresentation` over that alone). | any field `L` |
| ~~`isReduced_A_of_gamma1GITPresentation`~~ | PROVEN 2026-07-28 over `smoothCurve_A_of_gamma1GITPresentation` and the in-tree `Algebra.Smooth.isReduced_of_isField`; no longer a leaf | — |
| `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation` | Deligne-Rapoport IV.5.5: `det` is onto, so `G` permutes the components of `Spec (A ⊗[K] L)` transitively for EVERY field extension `L/K`.  MERGED 2026-07-30 out of the two former leaves `transitiveMinimalPrimes_of_gamma1GITPresentation` and `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation`, BOTH of which are now PROVEN over it — the first at `L := K` through `Algebra.TensorProduct.rid`, the second through the new `isDomain_of_minimalPrimes_transitive_family` plus `smoothCurve_A_of_gamma1GITPresentation` and `nontrivial_A_of_gamma1GITPresentation`.  Two leaves stating one sentence of IV.5.5 at two generalities became one leaf at the stronger generality. | any `K`, `char K ∤ N`, any field extension `L/K` |
| ~~`transitiveMinimalPrimes_of_gamma1GITPresentation`~~ | PROVEN 2026-07-30 over the row above at `L := K`; no longer a leaf | — |
| ~~`isPrime_nilradical_tensorProduct_of_gamma1GITPresentation`~~ | PROVEN 2026-07-30 over the row above; no longer a leaf.  `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` and `connectedSpace_tensorProduct_of_gamma1GITPresentation` are unchanged and still read it | — |
| `exists_rationalCuspPointsX1_field` | `φ(N)/2` rational cusps of `X_1(N)` (Deligne-Rapoport VI.5).  Base field FREED 2026-07-28: this single leaf now carries the former `exists_rationalCuspPointsX1` (over `ℚ`, PROVEN over it) and the `≥` half of the former `card_cuspLocusPoints_x1_finiteField` (over `𝔽_3`) — one sentence of Deligne-Rapoport that used to be two open leaves at two bases. | any `K` with `N` invertible |
| `exists_isFineGamma1Moduli` | Katz–Mazur 4.7.1: `[Γ₁(N)]` is REPRESENTABLE at `N ≥ 4`, `ℓ` prime, `ℓ ∤ N` — a universal family `dM` over `M`, classified uniquely.  (`exists_fineGamma1Atlas` is PROVEN over it, 2026-07-28, through the formal `Gamma1Atlas.ofFineModuli`; that node was itself `nonempty_relPoint_atlas_of_relPoint`, REFUTED and restated the same day — see its FALSITY AUDIT.) | `𝔽_ℓ` |
| `nonempty_gamma1Datum_baseChange` | base change of a `Γ₁(N)`-datum — formal, no arithmetic | any |
| `exists_weierstrassModel_of_abelianSchemeStruct_finiteField` | **Riemann-Roch on a genus-one curve** — a Weierstrass model of an abelian scheme of relative dimension one over `Spec 𝔽_ℓ`; NO modular curves and no level structure.  Cut 2026-07-28 as the geometry half of `exists_weierstrassEquiv_of_gamma1Datum` (now PROVEN over it).  The ℚ-side chain in `EllipticScheme.lean` is hardcoded to `Spec ℚ` and its own three leaves are open, so there is nothing to instantiate. | `𝔽_ℓ` |
| `exists_relPointAddEquiv_of_weierstrassModel_finiteField` | the transport half of the same cut: given the model, the `𝔽_ℓ`-SECTIONS are `W(𝔽_ℓ)`.  The content is that the abelian scheme's group law agrees with the chord-and-tangent law (rigidity); strictly easier than the ℚ-side `exists_geomFibreAddEquiv_of_weierstrassModel`, which needs a `Γ_ℚ`-equivariant equivalence on geometric fibres. | `𝔽_ℓ` |
| `exists_cuspSymbolEmbedding_x1_finiteField` | the hard direction of Ogg's description, DECOMPOSED 2026-07-28 into geometry and arithmetic: the `𝔽_ℓ`-rational cusp points inject into the Frobenius-fixed cusp symbols `Γ_1(N)∖ℙ¹(ℚ)`.  Carries NO counting — that is `card_fixedCuspSymbolX1` (`ModularCurve/CuspSymbolX1.lean`), PROVEN, and `card_cuspLocusPoints_x1_finiteField_le` is PROVEN over the two.  The lower bound is the `exists_rationalCuspPointsX1_field` row above. | `𝔽_ℓ`, `ℓ ∤ N`, `N ≥ 5` |
| `exists_x1SmoothProperCurveModel` | Deligne-Rapoport VI.6.9: the smooth proper model over `ℤ_(ℓ)` together with the identification of its GENERIC fibre.  NO moduli in the conclusion — the modular input is the hypothesis `hX`.  (Replaces `exists_x1CurveReductionModel`, which is **PROVEN** over this row alone since 2026-07-30: the special fibre is the pullback along the closed point, so `spX`/`spX_nat` are `fibreIdentPullback`, and `properX` is `bijective_pre_generic_of_isProper` — the three obligations that need no modular geometry, discharged as `X0.lean` had already done on the `Γ₀` side.) | `ℚ → 𝔽_ℓ` |
| `exists_isX1Compactification_specialFibre` | Igusa / Katz-Mazur 5.1.1: the special fibre of that model IS `X_1(N)` over `𝔽_ℓ`.  (`exists_x1CurveModel_of_base` is PROVEN over this row and the one above, 2026-07-28, splitting the two classical theorems it had cited jointly; `exists_x1ReductionAt` is PROVEN over that plus the moduli-free `NeronReduction.lean`.  Since 2026-07-30 the row above is the weaker `exists_x1SmoothProperCurveModel`; the leaf COUNT here is unchanged.) | `ℚ → 𝔽_ℓ` |
| `exists_section_of_galoisInvariant` | Galois descent of a rational point to a section | `ℚ` |
| `exists_heckeCorrespondenceFamilyGamma1` | the `Γ₁` Hecke correspondence as a natural family on points — the geometric half, and the `Γ₁` twin of `X0.lean`'s `exists_heckeCorrespondenceFamily`.  (`exists_heckeAction_isotypicQuotients_gamma1` was a leaf until 2026-07-28 and is now **PROVEN** over this row and the next, via the `Γ₁` moduli pin `IsModularHeckeActionGamma1`; `exists_modularHeckeAction_gamma1` is PROVEN over this row alone.) | `ℚ` |
| `isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1` | Shimura's algebraicity theorem for `Γ₁(N)`: the `a n` are algebraic integers.  MENTIONS NO SCHEME — the only obligation of `IsIsotypicQuotient` that does not, and it can be attacked from the integral-homology side or from the Hecke recursions plus a bound.  Cannot be an instance of `X0.lean`'s `isIntegral_coeff_of_isWeightTwoEigenform`: the `Γ₁` coefficients generate `ℚ(χ)`. | `ℚ` |
| `exists_isotypicQuotient_of_isIntegral_gamma1` | Shimura's `A_f` on `Γ₁(N)`, one factor, given the PINNED Hecke action AND algebraicity — the "build one factor" half of Eichler-Shimura, and the `Γ₁` twin of `X0.lean`'s `exists_isotypicQuotient_of_isIntegral`.  (`IsIsotypicQuotient` is reused verbatim from `X0.lean`; it is shape-free.  `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` is **PROVEN** over this row and the one above since 2026-07-30, transporting the `Γ₀` recut of the same day; its FALSITY AUDIT was discharged that day too and the statement is TRUE.) | `ℚ` |
| `exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1` | the "assemble the factors" half: finiteness of the index set, the oldform multiplicities, `finite_ker`, and the `neben` labelling.  It no longer owns the `N = 0` case: that case was REFUTED on 2026-07-28 (`isEmpty_isHeckeIsotypicDecompositionGamma1_zero`) and the leaf now carries `hN : N ≠ 0`; see its docstring | `ℚ` |
| `isTorsion_factor_of_heckeIsotypic_gamma1` | Kolyvagin-Logachev on an isotypic factor | `ℚ` |
| `cuspPeriod_ne_zero_x1TwentyFive` | the `L`-value numerics — the DEEP one, and the only row where `25` survives.  (`lFunction_apply_one_ne_zero_x1TwentyFive` was decomposed along the period 2026-07-28; its analytic half `lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` is PROVEN the same day, as the `G = Γ₁(N)` instance of `lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn`, which is in turn the group-generic form of `X0.lean`'s proven theorem.) | `ℚ` |
| `not_birationalOver_affineLine_of_one_le_x1Genus_algClosed` | the genus formula and nothing else — Diamond–Shurman Thm 3.1.1: a fibre of `X_1(N)` with `genus ≥ 1` is not birational to `𝔸¹` over an ALGEBRAICALLY CLOSED field.  The only declaration in the `Γ₁` genus formula that still mentions `N`.  (Cut 2026-07-30 out of `exists_nonconstant_toAbelianScheme_of_one_le_x1Genus`, which is PROVEN over it and the row below.)  **RESTATED 2026-07-30 with `hchar : (N : K) ≠ 0`**: without it the leaf and its three proven consumers are FALSE, refuted by the Igusa curve `Ig(11)` in characteristic `11` — the falsity audit and the genus computation are on the declaration, and the hypothesis is discharged at the `SpecQ` base of `hasNonconstantAbelianMap_of_one_le_x1Genus`. | alg. closed `K`, `char K ∤ N` |
| `exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` | `Pic⁰` and the degree-`n` Abel–Jacobi map: a GEOMETRICALLY non-rational fibre receives a nonconstant map to an abelian variety.  LEVEL-FREE — no `N` in it, and the `Γ₀` sibling leaf would close over it verbatim; see its RELOCATION NOTE.  The same statement with the hypothesis taken over `K` rather than over `K̄` is FALSE (pointless conic over `ℝ`); the falsity audit is on the declaration. | any |

(Table regenerated at the release-10 integration, 2026-07-28, from the
compiler's `declaration uses 'sorry'` set rather than from any branch's prose;
it agrees row-for-row with a comment-stripped source scan.  Fourteen rows.
The last row was replaced 2026-07-28 when the node above it closed; a stray
duplicate of it, left by a merge, was removed at the same time.  It was
replaced AGAIN later the same day, for the same reason: the fibrewise genus
leaf `hasNoFibreAffineLine_of_one_le_x1Genus` was PROVEN by decomposition
along the birational/Lüroth axis, and what is open in its place is the
single arithmetic leaf now named in the row.

Four further rows — the analytic quartet `exists_frickeInvolutionOn`,
`isBigO_atTop_axisRestrictOn`, `locallyIntegrableOn_axisRestrictOn` and
`isBigO_atTop_coeffOn` of the Kolyvagin–Logachev subsection — were removed
2026-07-28 when all four were PROVEN, over the `Γ₀` Fricke machinery of
`WeightTwoEigenform.lean` plus one new normalisation lemma
(`frickeMatrix_conj_mem_of_le`) and mathlib's `Bounds.lean`.  Ten rows.
`isBigO_atTop_coeffOn` gained a `hN : N ≠ 0` hypothesis at the same time —
it was FALSE at `N = 0`; see its FALSITY AUDIT.

The last row was replaced a THIRD time on 2026-07-30, and this time it
became TWO rows: `exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` was
PROVEN by separating the genus formula from the `Pic⁰` construction, so the
genus entry is now the arithmetic leaf plus the level-free geometric one.
Eleven rows.)

**This table was REGENERATED at integration (2026-07-27) from a
comment-stripped scan of the merged source, not merged as prose** — three
branches rewrote it in the same release and each was correct on its own base.
`exists_isCoarseModuliY1_isSmoothCurve`, `isEmpty_gamma1Datum_finiteField`,
`exists_injective_reduction_of_rankZeroJacobian`,
`nonempty_gamma1Datum_of_ratPoint` and `hasRankZeroJacobian_x1TwentyFive` all
stood in one version of it or another and are all PROVEN in the merged tree.

**Reorganised a third time 2026-07-28, along the BASE-FIELD axis.**  The two
residue-degree leaves the 2026-07-27 reorganisation left — one over `ℚ`, one
over `𝔽_3` — were the SAME sentence of Deligne-Rapoport VI.5 at two bases, and
each had its own owner.  `residueDegreeOver` writes the residue degree once
over an arbitrary field (`residueQDegree` and `residueFDegree` are `rfl`-equal
to it), `exists_rationalCuspPointsX1_field` states the cusp sentence once, and
`exists_rationalCuspPointsX1` is now PROVEN over it.  Only the direction that
genuinely differs between the bases survived as a separate leaf:
`card_cuspLocusPoints_x1_finiteField_le`, the `≤` half, which needs the count
EXACTLY and so cannot be shared with a `ℚ` side that is a lower bound.

**Reorganised a fourth time 2026-07-28, along the GEOMETRY-vs-ARITHMETIC
axis, and that closed the `≤` half.**  `card_cuspLocusPoints_x1_finiteField_le`
was one leaf doing two unrelated jobs: identifying the cusp locus with
`Γ_1(N)∖ℙ¹(ℚ)` carrying its Galois action, and computing at `(25, 3)` that
only `10` of the `28` symbols are Frobenius-fixed.  The second job is finite
arithmetic and is now PROVEN, uniformly in `(N, t)`, as
`card_fixedCuspSymbolX1` in `ModularCurve/CuspSymbolX1.lean`; the first is
`exists_cuspSymbolEmbedding_x1_finiteField`, which mentions no prime, no
level and no count.  The split also made the failure mode visible: the bound
`≤ φ(N)/2` is FALSE for `ℓ ≡ ±1 (mod N)`, and what rules that out is the
hypothesis `IsUnit (ℓ - 1) ∧ IsUnit (ℓ + 1)` in `ZMod N`, which the witness
row `(25, 3, 10)` discharges by `2` and `4` being units mod `25`.

**Updated again 2026-07-27** for the reduction/descent cluster.
`exists_inverse_of_smoothCompactification` is now PROVEN outright, over
`AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve` — its own
"absent from the pin" grep was aimed at the conclusion rather than at the
proof's input, and the input was there.  `exists_x1ReductionAt` and
`exists_section_of_galoisInvariant` are now PROVEN over the three leaves listed
in the table, which is a net `+1` on the direct-sorry count and is disclosure,
not regression: each of the three names a strictly smaller obligation than the
node it replaced.

**Reorganised again 2026-07-27, along the RESIDUE-FIELD axis at both bases.**
`nonempty_cuspLocusX1` and `card_cusp_x1_finiteField` are now THEOREMS; what
was open in them is `exists_rationalCuspPointsX1_field` and (until the fourth
reorganisation above closed it over
`exists_cuspSymbolEmbedding_x1_finiteField`)
`card_cuspLocusPoints_x1_finiteField_le`, which speak about the finite set of
POINTS `X ∖ Y` and their residue degrees rather than about `Spec`-valued cusp
data or about sections of `strX`.  The two dictionaries that do it —
`nonempty_cuspLocusX1_of_rationalCuspPoints` over `ℚ` and
`cuspEquivResidueDegreeOne` over `𝔽_ℓ` — are sorry-free, and the second rests
on `relPointEquivResidueDegreeOne`, which identifies `X(𝔽_ℓ)` with the
residue-degree-one points of `X` and is not `Γ₁`-specific at all.

Everything else in this file — the compactification geometry, the
finiteness of `X_1(N)(𝔽_ℓ)`, the passage from the cusp locus to indexed
rational cusps, the cusp-locus datum, the `𝔽_ℓ` point dictionary, and all
three assemblies — is now sorry-free. -/

/-! ### The Katz–Mazur atlas for `[Γ₁(N)]`, over an arbitrary base

**Added 2026-07-27**, cutting `exists_isCoarseModuliY1_isSmoothCurve`
along the GIT axis its own docstring named as NOT SEARCHED.  This is the
`Γ₁` analogue of `X0.lean`'s `Gamma0Atlas` / `Gamma0GITPresentation` /
`Gamma0AffineModel` tower, declaration for declaration:

| `X0.lean` (over `ℚ`) | here (over an arbitrary base scheme `S`) |
|---|---|
| `Gamma0Atlas` | `Gamma1Atlas` |
| `Gamma0Atlas.toIsCoarseModuliY0` (PROVEN) | `Gamma1Atlas.toIsCoarseModuliY1` (PROVEN) |
| `Gamma0GITPresentation` | `Gamma1GITPresentation` |
| `Gamma0GITPresentation.toGamma0Atlas` (PROVEN) | `Gamma1GITPresentation.toGamma1Atlas` (PROVEN) |
| `exists_gamma0GITPresentation` (PROVEN) | `exists_gamma1GITPresentation` (PROVEN) |
| `exists_gamma0GITPresentation_of_rigidified` (PROVEN) | `nonempty_gamma1GITPresentation_of_rigidification` (PROVEN) |
| `RigidifiedModuli` | `Gamma1RigidifiedModuli` |
| `FullLevelStructure` | `AbelianFullLevelStructure` (a DUPLICATE — see the coordination note at the cut below) |
| `exists_rigidifiedModuli` (PROVEN over `exists_rigidifiedModuliScheme` + `isAffine_of_rigidifiedModuliScheme`, both leaves) | `exists_gamma1RigidifiedModuli` (PROVEN 2026-07-30 over `exists_gamma1RigidifiedModuliScheme` + `isAffine_of_gamma1RigidifiedModuliScheme`, both leaves — the same three-way split, made here for the same reason) |
| `exists_fullLevelStructure_cover` (PROVEN, over `exists_torsionBasis_geomPoint` + `exists_torsionBasis_cover_of_geomPoint`, both `SpecQ`-only leaves) | `exists_gamma1FullLevelStructure_cover` (PROVEN 2026-07-28, over the single general-base leaf `exists_torsionBasisCover_field`, plus the PROVEN `nonempty_abelianFullLevelStructure_of_geomBasis` and the `IsBaseChangeOfGamma1.toRelPoint` API) |
| `exists_deckAction` (PROVEN over `exists_openCover_twist_of_fullLevelStructure`) | `exists_gamma1DeckAction` (REFUTED, restated with `a ≫ strM = b ≫ strM` and PROVEN 2026-07-29, over the single leaf `exists_openCover_twist_of_abelianFullLevelStructure`) |
| `FullLevelStructure.twist` API + `exists_fullLevelStructure_baseChange` + `twist_baseChange` (PROVEN) | `AbelianFullLevelStructure.twist` API + `exists_abelianFullLevelStructure_baseChange` + `twist_baseChange` (PROVEN 2026-07-29 — a TRANSCRIPTION, deletable once `X0.lean`'s `FullLevelStructure` is generalised to `AbelianSchemeStruct`) |
| `exists_openCover_deckTranslation` (PROVEN) | `exists_openCover_gamma1DeckTranslation` (PROVEN 2026-07-29) |
| — | `nonempty_gamma1Rigidification_of_rigidifiedModuli` (PROVEN); `exists_gamma1Rigidification` (PROVEN over the three leaves) |
| `exists_descendClassify` (PROVEN) | `exists_descendClassifyGamma1` (PROVEN) |
| `exists_gamma0Datum_baseChange` (PROVEN) | `exists_gamma1Datum_baseChange` (PROVEN) |
| `gamma0Atlas_isIso` + `isAffine_of_gamma0Atlas` (PROVEN) | not needed — see the section comment on the geometry below |
| `isDomain_of_gamma0GITPresentation` (leaf) | `geometricComponents_of_gamma1GITPresentation` (PROVEN 2026-07-28 over `exists_gamma1Datum_fieldExtension`, `isReduced_A_of_gamma1GITPresentation` — itself PROVEN later the same day over `smoothCurve_A_of_gamma1GITPresentation` — and `transitiveMinimalPrimes_of_gamma1GITPresentation`, itself PROVEN 2026-07-30 over `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`); `isDomain_of_gamma1GITPresentation` is PROVEN over it |
| `smoothOfRelativeDimension_of_gamma0GITPresentation` (leaf) | `locallyStandardSmooth_of_gamma1GITPresentation` (leaf); `smoothOfRelativeDimension_of_gamma1GITPresentation` is PROVEN over it |
| `geometricallyConnected_of_gamma0GITPresentation` (leaf) | `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation` (leaf, 2026-07-30); `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation`, `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation`, `connectedSpace_tensorProduct_of_gamma1GITPresentation` and `geometricallyConnected_of_gamma1GITPresentation` are PROVEN over it |
| `Gamma0AffineModel` / `exists_gamma0AffineModel` (PROVEN) | `Gamma1AffineModel` / `exists_gamma1AffineModel` (PROVEN) |

`specInvariants_universal` (`X0.lean`, PROVEN and sorry-free) is REUSED
verbatim: it is a statement about a finite group acting on a commutative
ring and mentions no moduli problem and no base field, so the `Γ₁` side
needs no analogue of it.

**THE ONE PLACE THIS IS NOT A TRANSCRIPTION: the base.**  `Gamma0Atlas`
is stated over `SpecQ`, and its `toIsCoarseModuliY0` leans three times on
`subsingleton_hom_specQ` — `Hom(Z, Spec ℚ)` is a subsingleton because `ℚ`
is initial among rings.  **That is FALSE over a general field**: for
`K = ℚ(i)` and `Z = Spec K` there are two morphisms `Z ⟶ Spec K`, the
identity and complex conjugation.  So each of the three uses is replaced
by an explicit hypothesis, and the two structures carry the resulting
"over `S`" clauses that `Gamma0Atlas` gets for free:

* `Gamma1Atlas.cover` carries `p ≫ g = m ≫ strM` — the rigidifying cover
  is a cover **of `S`-schemes**;
* `Gamma1Atlas.quotient` is the categorical quotient in the category of
  `S`-schemes: it takes `φ ≫ str' = strM`, its separation hypothesis is
  restricted to pairs `a, b` with `a ≫ strM = b ≫ strM`, and it returns
  `ψ` together with `ψ ≫ str' = str`;
* `Gamma1GITPresentation.strM_invariant` says the deck group acts over
  `S`, which is what discharges the restricted separation hypothesis at
  `a = 𝟙`, `b = Spec σ` and what pins `ψ ≫ str' = str` through the
  uniqueness half of `specInvariants_universal`.

All three are true of the Katz–Mazur construction and none of them is a
strengthening in disguise over `ℚ`, where `subsingleton_hom_specQ` makes
each of them automatic.

**A CORRECTION to `isDomain_of_gamma0Atlas`'s docstring, which matters
exactly because the base is now general.**  That docstring proposes
folding `IsDomain A` — integrality of the RIGIDIFIED moduli scheme — into
the GIT presentation, whereupon `Function.Injective.isDomain` closes the
leaf.  Over `ℚ` that is right.  Over a general `K` it is **FALSE**:
`𝔐([Γ₁(N)], [Γ(n)])` acquires `φ(n)` geometric components permuted by
`Gal(ℚ(ζ_n)/ℚ)` through the Weil pairing, so as soon as `ζ_n ∈ K` the
scheme is disconnected and `A` is not a domain.  What survives base
change is `IsDomain B` for the INVARIANTS, since `G = GL₂(ℤ/n)` permutes
those components transitively.

**That correction is now CARRIED OUT rather than merely recorded**
(2026-07-27): `isDomain_of_gamma1GITPresentation` is PROVEN, over
`geometricComponents_of_gamma1GITPresentation` — which asks for exactly
"`Spec A` is nonempty and reduced and `G` is transitive on its
components" — and the general commutative algebra that turns that into
`IsDomain B` is `isDomain_of_minimalPrimes_transitive`.  Nothing is
folded into `Gamma1GITPresentation` itself, for the reason `X0.lean`
gives: a prover sent at `exists_gamma1GITPresentation` should have to
build the construction and nothing else.

**Split again 2026-07-28.**  `geometricComponents_of_gamma1GITPresentation`
is now itself PROVEN, over its three conjuncts taken separately, because
they are three unrelated classical inputs:
`exists_gamma1Datum_fieldExtension` (an elliptic curve with a point of
exact order `N` over *some* field — no modular curves in it, and the only
thing `Nontrivial A` needs), `isReduced_A_of_gamma1GITPresentation`
(8.2.1, smoothness — itself PROVEN later the same day over
`smoothCurve_A_of_gamma1GITPresentation`) and
`transitiveMinimalPrimes_of_gamma1GITPresentation` (IV.5.5, the
`det`-surjectivity — itself PROVEN 2026-07-30 over its base-changed form
`transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`, which is
where the open obligation now sits).  The ROUTE AUDIT on the last of those records why
neither `Algebra.IsInvariant.exists_smul_of_under_eq` nor an
existentially-quantified algebra of components cuts it any further, and
that the honest next step is a Weil-pairing FIELD on
`Gamma1Rigidification` — the same shape as `coequalises`. -/

/-- **A Katz–Mazur atlas for the `Γ₁(N)`-problem over a base scheme `S`.**

The `Γ₁` analogue of `Gamma0Atlas`, over an arbitrary base rather than
over `Spec ℚ`; see the section comment for the field-by-field
correspondence and for the three "over `S`" clauses that replace
`subsingleton_hom_specQ`.

The data is: a candidate coarse space `(Y, str)` with a natural
classifying map, a rigidified moduli scheme `(M, strM)` carrying a
universal family `dM`, the statement that `dM` rigidifies every datum
after an fpqc base change, and the categorical-quotient property of the
classifying map of `dM`.  `Y` is `M/GL₂(ℤ/n)`; the structure does not
name the group, because only the two properties are used. -/
structure Gamma1Atlas (N : ℕ) (S : Scheme.{0}) where
  /-- the coarse space to be -/
  Y : Scheme.{0}
  /-- its structure morphism to the base -/
  str : Y ⟶ S
  /-- the classifying map of the moduli problem, Katz–Mazur (8.1.3) -/
  classify : ∀ {T : Scheme.{0}} (g : T ⟶ S), Gamma1Datum N T → RelPoint str g
  /-- the classifying map is natural in the base -/
  classify_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') {d' : Gamma1Datum N T'} {d : Gamma1Datum N T},
    IsBaseChangeOfGamma1 h d' d → classify g' d' = RelPoint.pre h hg (classify g d)
  /-- the rigidified moduli scheme `𝔐([Γ₁(N)], [Γ(n)])` -/
  M : Scheme.{0}
  /-- its structure morphism -/
  strM : M ⟶ S
  /-- the universal family it carries -/
  dM : Gamma1Datum N M
  /-- **rigidification**: every datum over an `S`-scheme is, after a
  faithfully flat quasi-compact base change **of `S`-schemes**, a base
  change of `dM`.

  The clause `p ≫ g = m ≫ strM` is what `Gamma0Atlas.cover` gets for
  free from `subsingleton_hom_specQ`, and it is load-bearing in
  `toIsCoarseModuliY1`: without it the two naturality equations for `c`
  and for `classify` are stated at unrelated base points and cannot be
  compared.  Note also the binder `g`, whose necessity is the subject of
  the FALSITY AUDIT on `Gamma0Atlas.cover`: dropping it makes the field
  false and the structure empty. -/
  cover : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T),
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T') (m : T' ⟶ M),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      p ≫ g = m ≫ strM ∧
      Nonempty (IsBaseChangeOfGamma1 p d' d) ∧ Nonempty (IsBaseChangeOfGamma1 m d' dM)
  /-- **categorical quotient in the category of `S`-schemes**: an
  `S`-morphism out of `M` that does not separate two rigidifications of
  one datum factors uniquely, and over `S`, through the classifying map
  of `dM`. -/
  quotient : ∀ {Y' : Scheme.{0}} (str' : Y' ⟶ S) (φ : M ⟶ Y'), φ ≫ str' = strM →
    (∀ {Z : Scheme.{0}} (a b : Z ⟶ M) (d₁ : Gamma1Datum N Z), a ≫ strM = b ≫ strM →
      IsBaseChangeOfGamma1 a d₁ dM → IsBaseChangeOfGamma1 b d₁ dM → a ≫ φ = b ≫ φ) →
    ∃! ψ : Y ⟶ Y', ψ ≫ str' = str ∧ (classify strM dM).1 ≫ ψ = φ

/-- **An atlas IS a coarse moduli space** (PROVEN 2026-07-27) — the
initiality clause of `IsCoarseModuliY1` derived from Katz–Mazur's
construction rather than cited alongside it.

Verbatim the proof of `Gamma0Atlas.toIsCoarseModuliY0` with the three
appeals to `subsingleton_hom_specQ` replaced by the explicit "over `S`"
clauses of `cover` and `quotient`.  The argument: a cocone cannot
separate two rigidifications of one datum, because its own naturality
equates both composites with its value at that datum; so it factors
through the quotient, uniquely; and the factorisation computes the
cocone at an arbitrary datum after pulling back along the fpqc
rigidifying cover, which is an epimorphism and may be cancelled. -/
def Gamma1Atlas.toIsCoarseModuliY1 {N : ℕ} {S : Scheme.{0}} (A : Gamma1Atlas N S) :
    IsCoarseModuliY1 N A.str where
  classify := A.classify
  classify_natural := A.classify_natural
  universal := by
    intro Y' str' c hc
    -- A cocone cannot separate two rigidifications of one datum.
    have hconst : ∀ {Z : Scheme.{0}} (a b : Z ⟶ A.M) (d₁ : Gamma1Datum N Z),
        a ≫ A.strM = b ≫ A.strM →
        IsBaseChangeOfGamma1 a d₁ A.dM → IsBaseChangeOfGamma1 b d₁ A.dM →
        a ≫ (c A.strM A.dM).1 = b ≫ (c A.strM A.dM).1 := by
      intro Z a b d₁ hab ha hb
      have h1 : (c (a ≫ A.strM) d₁).1 = a ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc a rfl ha)
      have h2 : (c (b ≫ A.strM) d₁).1 = b ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc b rfl hb)
      rw [← h1, ← h2, hab]
    -- so it factors through the quotient, over `S`, uniquely.
    obtain ⟨u, ⟨hu0, hu⟩, huniq⟩ :=
      A.quotient str' (c A.strM A.dM).1 (c A.strM A.dM).2 hconst
    refine ⟨u, ⟨hu0, ?_⟩, ?_⟩
    · -- `u` computes `c` at an arbitrary datum: pull back to the
      -- rigidifying cover, where both sides are statements about `dM`,
      -- and cancel the cover.
      intro T g d
      obtain ⟨T', p, d', m, hflat, hsurj, hqc, hst, ⟨hbp⟩, ⟨hbm⟩⟩ := A.cover g d
      haveI := hflat
      haveI := hsurj
      haveI := hqc
      have hcp : (c (p ≫ g) d').1 = p ≫ (c g d).1 :=
        congrArg Subtype.val (hc p rfl hbp)
      have hcm : (c (m ≫ A.strM) d').1 = m ≫ (c A.strM A.dM).1 :=
        congrArg Subtype.val (hc m rfl hbm)
      have hAp : (A.classify (p ≫ g) d').1 = p ≫ (A.classify g d).1 :=
        congrArg Subtype.val (A.classify_natural p rfl hbp)
      have hAm : (A.classify (m ≫ A.strM) d').1 = m ≫ (A.classify A.strM A.dM).1 :=
        congrArg Subtype.val (A.classify_natural m rfl hbm)
      rw [hst] at hcp hAp
      have key : p ≫ (c g d).1 = p ≫ ((A.classify g d).1 ≫ u) := by
        rw [← hcp, hcm, ← hu, ← Category.assoc, ← hAm, hAp, Category.assoc]
      exact (cancel_epi p).mp key
    · -- uniqueness: a rival `u₁` factors `c dM` through the quotient too.
      rintro u₁ ⟨h₀, h₁⟩
      exact huniq u₁ ⟨h₀, (h₁ A.strM A.dM).symm⟩

/-- **A Katz–Mazur atlas presented the way (8.1.1) actually builds it**:
the rigidified moduli scheme as `Spec A` with a finite group `G` acting,
and the coarse space as `Spec` of the invariants.

The `Γ₁` analogue of `Gamma0GITPresentation`, over an arbitrary base.
This is `Gamma1Atlas` with its `quotient` field replaced by the data that
*produces* it; the fields it shares with `Gamma1Atlas` are documented
there.  What differs:

* `A`, `B`, `G` with `Algebra.IsInvariant B A G`: the rigidified moduli
  scheme is `M = Spec A`, affine, the deck group `G = GL₂(ℤ/n)` is
  finite, and the coarse space is `Y = Spec B` with `B = A^G`.
* `classify_dM`: the classifying map of the universal family IS the
  quotient map `π = Spec (B → A)`.
* `strM_invariant`: `G` acts over the base — the clause that has no
  counterpart on the `Γ₀` side, where `Hom(Spec A, Spec ℚ)` is a
  subsingleton and it is automatic.
* `dM_equivariant`: `σ^*dM ≅ dM`, phrased through `IsBaseChangeOfGamma1`
  at `𝟙` and at `Spec σ` because that is the only comparison of
  `Γ₁(N)`-data this development has. -/
structure Gamma1GITPresentation (N : ℕ) (S : Scheme.{0}) where
  /-- the coordinate ring of the rigidified moduli scheme -/
  A : Type
  [commRing_A : CommRing A]
  /-- the ring of invariants, whose spectrum is the coarse space -/
  B : Type
  [commRing_B : CommRing B]
  [algebra_BA : Algebra B A]
  /-- the deck group `GL₂(ℤ/n)` of the rigidification -/
  G : Type
  [group_G : Group G]
  [finite_G : Finite G]
  [action_GA : MulSemiringAction G A]
  [smulComm_GBA : SMulCommClass G B A]
  [isInvariant_BAG : Algebra.IsInvariant B A G]
  /-- `B` is a subring of `A`, not merely an algebra over it -/
  injective_algebraMap : Function.Injective (algebraMap B A)
  /-- the structure morphism of the coarse space -/
  str : Spec (CommRingCat.of B) ⟶ S
  /-- the structure morphism of the rigidified moduli scheme -/
  strM : Spec (CommRingCat.of A) ⟶ S
  /-- the classifying map of the moduli problem, Katz–Mazur (8.1.3) -/
  classify : ∀ {T : Scheme.{0}} (g : T ⟶ S), Gamma1Datum N T → RelPoint str g
  /-- the classifying map is natural in the base -/
  classify_natural : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') {d' : Gamma1Datum N T'} {d : Gamma1Datum N T},
    IsBaseChangeOfGamma1 h d' d → classify g' d' = RelPoint.pre h hg (classify g d)
  /-- the universal family carried by the rigidified moduli scheme -/
  dM : Gamma1Datum N (Spec (CommRingCat.of A))
  /-- the classifying map of the universal family is the quotient map -/
  classify_dM : (classify strM dM).1 = Spec.map (CommRingCat.ofHom (algebraMap B A))
  /-- **rigidification**, exactly as in `Gamma1Atlas.cover` -/
  cover : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T),
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T')
      (m : T' ⟶ Spec (CommRingCat.of A)),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      p ≫ g = m ≫ strM ∧
      Nonempty (IsBaseChangeOfGamma1 p d' d) ∧ Nonempty (IsBaseChangeOfGamma1 m d' dM)
  /-- **the deck group acts over the base** -/
  strM_invariant : ∀ σ : G,
    Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)) ≫ strM = strM
  /-- **`G`-equivariance of the universal family**: `σ^*dM ≅ dM` -/
  dM_equivariant : ∀ σ : G, ∃ d₁ : Gamma1Datum N (Spec (CommRingCat.of A)),
    Nonempty (IsBaseChangeOfGamma1 (𝟙 (Spec (CommRingCat.of A))) d₁ dM) ∧
    Nonempty (IsBaseChangeOfGamma1
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ))) d₁ dM)

/-- **A GIT presentation IS an atlas** (PROVEN 2026-07-27): the
`quotient` field of `Gamma1Atlas` derived from the affine presentation
and `specInvariants_universal`.

Two steps have content.  Turning the separation hypothesis into
`G`-invariance of `φ` is `dM_equivariant` together with
`strM_invariant`, which is what makes `𝟙` and `Spec σ` an admissible
pair for the restricted hypothesis.  Producing the "over `S`" half of
the conclusion is the uniqueness clause of `specInvariants_universal`
applied a SECOND time, with target `S` and `φ := strM`: both `ψ ≫ str'`
and `str` are factorisations of `strM` through `π`, hence equal.  On the
`Γ₀` side that second application is invisible, because
`Subsingleton (Spec B ⟶ Spec ℚ)` closes the same goal. -/
noncomputable def Gamma1GITPresentation.toGamma1Atlas {N : ℕ} {S : Scheme.{0}}
    (P : Gamma1GITPresentation N S) : Gamma1Atlas N S :=
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  letI := P.isInvariant_BAG
  { Y := Spec (CommRingCat.of P.B)
    str := P.str
    classify := P.classify
    classify_natural := P.classify_natural
    M := Spec (CommRingCat.of P.A)
    strM := P.strM
    dM := P.dM
    cover := P.cover
    quotient := by
      intro Y' str' φ hφ hsep
      -- the quotient map is a morphism over `S`
      have hπ : Spec.map (CommRingCat.ofHom (algebraMap P.B P.A)) ≫ P.str = P.strM := by
        rw [← P.classify_dM]; exact (P.classify P.strM P.dM).2
      -- `𝟙` and `Spec σ` are two rigidifications of the SAME datum, and
      -- they agree over `S`, so the separation hypothesis applies.
      have hinv : ∀ σ : P.G,
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom P.G P.A σ)) ≫ φ = φ := by
        intro σ
        obtain ⟨d₁, ⟨h1⟩, ⟨h2⟩⟩ := P.dM_equivariant σ
        have h := hsep (𝟙 _) _ d₁ (by rw [Category.id_comp, P.strM_invariant σ]) h1 h2
        rw [Category.id_comp] at h
        exact h.symm
      obtain ⟨ψ, hψ, huniq⟩ := specInvariants_universal P.G P.injective_algebraMap φ hinv
      -- the SECOND application, with target `S`, is what pins `ψ` over `S`
      obtain ⟨w, -, huniq2⟩ :=
        specInvariants_universal P.G P.injective_algebraMap P.strM P.strM_invariant
      rw [P.classify_dM]
      refine ⟨ψ, ⟨?_, hψ⟩, ?_⟩
      · rw [huniq2 (ψ ≫ str')
            (show Spec.map (CommRingCat.ofHom (algebraMap P.B P.A)) ≫ (ψ ≫ str') = P.strM by
              rw [← Category.assoc, hψ, hφ]),
          huniq2 P.str hπ]
      · rintro ψ' ⟨-, h⟩
        exact huniq ψ' h }

/-! #### Base change of a `Γ₁(N)`-datum, as a construction

**Added 2026-07-27**, cutting `exists_gamma1GITPresentation` along the
same axis `X0.lean` cuts `exists_gamma0GITPresentation`: the `Γ₁`-moduli
problem is a FUNCTOR, every datum pulls back along every `h : T' ⟶ T`,
and that is what the fpqc descent of the classifying map below runs on.

This is the `Γ₁` transcription of `Gamma0BaseChange`, and it is strictly
SHORTER, because the level structure is a SECTION rather than a subgroup
scheme: transporting it is one `pullback.lift`, where `Gamma0BaseChange`
has to build `C ×_T T'`, recover the closed immersion by pullback
pasting, and prove `liesIn_iota_iff` in both directions.  What survives
verbatim is `AbelianSchemeStruct.baseChange` and its bijection
`RelPoint.baseChangeDown` / `RelPoint.baseChangeUp`, and the one step
with content — `geom_order` — transports for the same reason
`geom_cyclic` does: `downHom` is an INJECTIVE additive map, so
`addOrderOf_injective` carries the order across. -/

namespace Gamma1BaseChange

open CategoryTheory.Limits

variable {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T) (d : Gamma1Datum N T)

/-- the projection of the base-changed total space to `E` -/
noncomputable abbrev qq : pullback d.f h ⟶ d.E := pullback.fst d.f h

/-- the structure morphism of the base-changed total space -/
noncomputable abbrev fb : pullback d.f h ⟶ T' := pullback.snd d.f h

/-- **The base-changed section**, `h ≫ sec` paired with the identity.
This is the whole of the `Γ₁` level-structure base change, and it is the
place where this development is shorter than the `Γ₀` one. -/
noncomputable def secBC : T' ⟶ pullback d.f h :=
  pullback.lift (h ≫ d.pt.sec) (𝟙 T') (by
    rw [Category.assoc, d.pt.sec_comp, Category.comp_id, Category.id_comp])

lemma secBC_fst : secBC h d ≫ qq h d = h ≫ d.pt.sec := pullback.lift_fst _ _ _

lemma secBC_snd : secBC h d ≫ fb h d = 𝟙 T' := pullback.lift_snd _ _ _

/-- **`baseChangeDown` as an additive map on relative points.**  This is
what carries `addOrderOf` between the two sides in `geom_order`; it is
injective by `RelPoint.baseChangeDown_injective`. -/
noncomputable def downHom {U : Scheme.{u}} (g : U ⟶ T') :
    letI := (d.ab.baseChange h).addCommGroup g
    letI := d.ab.addCommGroup (g ≫ h)
    RelPoint (fb h d) g →+ RelPoint d.f (g ≫ h) :=
  letI := (d.ab.baseChange h).addCommGroup g
  letI := d.ab.addCommGroup (g ≫ h)
  { toFun := RelPoint.baseChangeDown h
    map_zero' := by
      show RelPoint.baseChangeDown h ((d.ab.baseChange h).zero g) = d.ab.zero (g ≫ h)
      rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
    map_add' := by
      intro x y
      show RelPoint.baseChangeDown h ((d.ab.baseChange h).add x y)
          = d.ab.add (RelPoint.baseChangeDown h x) (RelPoint.baseChangeDown h y)
      rw [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp] }

lemma downHom_apply {U : Scheme.{u}} (g : U ⟶ T') (x : RelPoint (fb h d) g) :
    downHom h d g x = RelPoint.baseChangeDown h x := rfl

/-- **The base-changed point of exact order `N`.**  The order is read at
`t ≫ h` and transported back by the injective additive `downHom`. -/
noncomputable def ptBC : PointOfExactOrder (d.ab.baseChange h) N where
  sec := secBC h d
  sec_comp := secBC_snd h d
  geom_order := by
    intro K _ _ t
    letI := (d.ab.baseChange h).addCommGroup t
    letI := d.ab.addCommGroup (t ≫ h)
    have hinj : Function.Injective (downHom h d t) :=
      RelPoint.baseChangeDown_injective h
    have hmap : downHom h d t (RelPoint.ofSection (secBC h d) (secBC_snd h d) t)
        = RelPoint.ofSection d.pt.sec d.pt.sec_comp (t ≫ h) := by
      refine Subtype.ext ?_
      show (t ≫ secBC h d) ≫ pullback.fst d.f h = (t ≫ h) ≫ d.pt.sec
      rw [Category.assoc, secBC_fst, ← Category.assoc]
    rw [← addOrderOf_injective (downHom h d t) hinj, hmap]
    exact d.pt.geom_order K (t ≫ h)

/-- **The base-changed `Γ₁(N)`-datum.** -/
noncomputable def datumBC : Gamma1Datum N T' where
  E := pullback d.f h
  f := fb h d
  ab := d.ab.baseChange h
  relativeDimensionOne :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (IsPullback.of_hasPullback d.f h) d.relativeDimensionOne
  pt := ptBC h d

/-- **And it IS a base change**, with the cartesian square the defining
one; `map_sec` is `secBC_fst` and needs no argument at all, which is the
`Γ₁` analogue of `Gamma0BaseChange.isBaseChangeBC`'s `liesIn_iff`. -/
noncomputable def isBaseChangeBC : IsBaseChangeOfGamma1 h (datumBC h d) d where
  map := qq h d
  isPullback := (IsPullback.of_hasPullback d.f h).flip
  map_zero := by
    intro U g
    show RelPoint.baseChangeDown h ((d.ab.baseChange h).zero g) = d.ab.zero (g ≫ h)
    rw [AbelianSchemeStruct.baseChange_zero, RelPoint.baseChangeDown_baseChangeUp]
  map_add := by
    intro U g x y
    show RelPoint.baseChangeDown h ((d.ab.baseChange h).add x y)
        = d.ab.add (RelPoint.baseChangeDown h x) (RelPoint.baseChangeDown h y)
    rw [AbelianSchemeStruct.baseChange_add, RelPoint.baseChangeDown_baseChangeUp]
  map_sec := secBC_fst h d

end Gamma1BaseChange

/-- **Base change of a `Γ₁(N)`-datum, as a CONSTRUCTION** (PROVEN
2026-07-27) — the `Γ₁` analogue of `exists_gamma0Datum_baseChange`.

Given any `h : T' ⟶ T` and any datum over `T`, there is a datum over `T'`
which is a base change of it.  Nothing here mentions a level `n`, a base
field, or any moduli scheme: it is the statement that the
`Γ₁(N)`-moduli problem is a FUNCTOR, and `exists_descendClassifyGamma1`
below consumes it purely to produce the data living over the fibre
products of the rigidifying cover.

Stated at universe `u` rather than at `0` because nothing in it is
specific to the modular-curve layer. -/
theorem exists_gamma1Datum_baseChange {N : ℕ} {T' T : Scheme.{u}} (h : T' ⟶ T)
    (d : Gamma1Datum N T) :
    ∃ d' : Gamma1Datum N T', Nonempty (IsBaseChangeOfGamma1 h d' d) :=
  ⟨Gamma1BaseChange.datumBC h d, ⟨Gamma1BaseChange.isBaseChangeBC h d⟩⟩

namespace IsBaseChangeOfGamma1

variable {N : ℕ}

/-- **A datum is a base change of itself along the identity** (PROVEN).

Consumed by `nonempty_gamma1GITPresentation_of_rigidification` to compute
the classifying map of the universal family: the trivial cover `𝟙` of
`Spec A`, rigidified by `𝟙`, is what forces `classify strM dM = π`. -/
def refl {T : Scheme.{u}} (d : Gamma1Datum N T) : IsBaseChangeOfGamma1 (𝟙 T) d d where
  map := 𝟙 d.E
  isPullback := IsPullback.of_id_snd
  map_zero := by
    intro T'' g
    have h0 : d.ab.zero (g ≫ 𝟙 T)
        = RelPoint.transport (Category.comp_id g).symm (d.ab.zero g) :=
      (RelPoint.transport_zero d.ab _).symm
    refine Subtype.ext ?_
    rw [h0]
    simp only [RelPoint.along_val, RelPoint.transport_val, Category.comp_id]
  map_add := by
    intro T'' g x y
    have hal : ∀ z : RelPoint d.f g,
        RelPoint.along (𝟙 d.E) (IsPullback.of_id_snd (f := d.f)).w z
          = RelPoint.transport (Category.comp_id g).symm z :=
      fun z => Subtype.ext (by
        simp only [RelPoint.along_val, RelPoint.transport_val, Category.comp_id])
    rw [hal, hal, hal, RelPoint.transport_add]
  map_sec := by rw [Category.comp_id, Category.id_comp]

/-- **Base changes compose** (PROVEN): `d₁` a base change of `d₂` along
`a` and `d₂` one of `d₃` along `b` make `d₁` one of `d₃` along `a ≫ b`.
The cartesian square is `IsPullback.paste_vert`; the base-point
associativity is absorbed by `AbelianSchemeStruct.zero_val_congr` /
`add_val_congr`, and `map_sec` is three rewrites. -/
noncomputable def comp {T₁ T₂ T₃ : Scheme.{u}} {a : T₁ ⟶ T₂} {b : T₂ ⟶ T₃}
    {d₁ : Gamma1Datum N T₁} {d₂ : Gamma1Datum N T₂} {d₃ : Gamma1Datum N T₃}
    (bc₁ : IsBaseChangeOfGamma1 a d₁ d₂) (bc₂ : IsBaseChangeOfGamma1 b d₂ d₃) :
    IsBaseChangeOfGamma1 (a ≫ b) d₁ d₃ where
  map := bc₁.map ≫ bc₂.map
  isPullback := bc₁.isPullback.paste_vert bc₂.isPullback
  map_zero := by
    intro U g
    refine Subtype.ext ?_
    have h₁ : (d₁.ab.zero g).1 ≫ bc₁.map = (d₂.ab.zero (g ≫ a)).1 :=
      congrArg Subtype.val (bc₁.map_zero g)
    have h₂ : (d₂.ab.zero (g ≫ a)).1 ≫ bc₂.map = (d₃.ab.zero ((g ≫ a) ≫ b)).1 :=
      congrArg Subtype.val (bc₂.map_zero (g ≫ a))
    show (d₁.ab.zero g).1 ≫ bc₁.map ≫ bc₂.map = (d₃.ab.zero (g ≫ a ≫ b)).1
    rw [← Category.assoc, h₁, h₂]
    exact AbelianSchemeStruct.zero_val_congr d₃.ab (Category.assoc g a b)
  map_add := by
    intro U g x y
    refine Subtype.ext ?_
    have h₁ : (d₁.ab.add x y).1 ≫ bc₁.map
        = (d₂.ab.add (RelPoint.along bc₁.map bc₁.isPullback.w x)
            (RelPoint.along bc₁.map bc₁.isPullback.w y)).1 :=
      congrArg Subtype.val (bc₁.map_add x y)
    have h₂ : ∀ z w : RelPoint d₂.f (g ≫ a), (d₂.ab.add z w).1 ≫ bc₂.map
        = (d₃.ab.add (RelPoint.along bc₂.map bc₂.isPullback.w z)
            (RelPoint.along bc₂.map bc₂.isPullback.w w)).1 :=
      fun z w => congrArg Subtype.val (bc₂.map_add z w)
    show (d₁.ab.add x y).1 ≫ bc₁.map ≫ bc₂.map
        = (d₃.ab.add (RelPoint.along (bc₁.map ≫ bc₂.map) (bc₁.isPullback.paste_vert
              bc₂.isPullback).w x)
            (RelPoint.along (bc₁.map ≫ bc₂.map) (bc₁.isPullback.paste_vert
              bc₂.isPullback).w y)).1
    rw [← Category.assoc, h₁, h₂]
    exact AbelianSchemeStruct.add_val_congr d₃.ab (Category.assoc g a b) _ _ _ _
      (Category.assoc _ _ _) (Category.assoc _ _ _)
  map_sec := by
    show d₁.pt.sec ≫ bc₁.map ≫ bc₂.map = (a ≫ b) ≫ d₃.pt.sec
    rw [← Category.assoc, bc₁.map_sec, Category.assoc, bc₂.map_sec, ← Category.assoc]

/-- The morphism induced by cancelling a base change: `e.E ⟶ d'.E`, from
the universal property of `d'.E` as a fibre product. -/
noncomputable def cancelMap {T'' T' T : Scheme.{u}}
    {h₁ : T'' ⟶ T'} {h₂ : T' ⟶ T} {e : Gamma1Datum N T''}
    {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}
    (hb : IsBaseChangeOfGamma1 (h₁ ≫ h₂) e d) (hb₂ : IsBaseChangeOfGamma1 h₂ d' d) :
    e.E ⟶ d'.E :=
  hb₂.isPullback.lift (e.f ≫ h₁) hb.map (by rw [Category.assoc]; exact hb.isPullback.w)

@[reassoc] theorem cancelMap_fst {T'' T' T : Scheme.{u}}
    {h₁ : T'' ⟶ T'} {h₂ : T' ⟶ T} {e : Gamma1Datum N T''}
    {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}
    (hb : IsBaseChangeOfGamma1 (h₁ ≫ h₂) e d) (hb₂ : IsBaseChangeOfGamma1 h₂ d' d) :
    hb.cancelMap hb₂ ≫ d'.f = e.f ≫ h₁ :=
  hb₂.isPullback.lift_fst _ _ _

@[reassoc] theorem cancelMap_snd {T'' T' T : Scheme.{u}}
    {h₁ : T'' ⟶ T'} {h₂ : T' ⟶ T} {e : Gamma1Datum N T''}
    {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}
    (hb : IsBaseChangeOfGamma1 (h₁ ≫ h₂) e d) (hb₂ : IsBaseChangeOfGamma1 h₂ d' d) :
    hb.cancelMap hb₂ ≫ hb₂.map = hb.map :=
  hb₂.isPullback.lift_snd _ _ _

/-- **Base changes CANCEL** (PROVEN) — the exact converse of
`IsBaseChangeOfGamma1.comp`, and the `Γ₁` analogue of
`IsBaseChangeOf.cancel`.

Both `e` and `d'` are pullbacks of `d`, so `e.E` maps to `d'.E` by the
universal property and the resulting square is cartesian by the converse
of pullback pasting (`IsPullback.of_bot`).  The remaining fields
transport because `IsPullback.hom_ext` lets a morphism into `d'.E` be
checked against `d'.f` and `hb₂.map` separately, and `cancelMap_fst` /
`cancelMap_snd` say what those two composites are.

Consumed by `exists_descendClassifyGamma1` at `h₁ := g₂`, `h₂ := p`, to
recognise that a base change of the rigidified cover along `g₁` is *also*
one along any `g₂` with `g₁ ≫ p = g₂ ≫ p`. -/
noncomputable def cancel {T'' T' T : Scheme.{u}}
    {h₁ : T'' ⟶ T'} {h₂ : T' ⟶ T} {e : Gamma1Datum N T''}
    {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}
    (hb : IsBaseChangeOfGamma1 (h₁ ≫ h₂) e d) (hb₂ : IsBaseChangeOfGamma1 h₂ d' d) :
    IsBaseChangeOfGamma1 h₁ e d' where
  map := hb.cancelMap hb₂
  isPullback := by
    refine IsPullback.of_bot ?_ (hb.cancelMap_fst hb₂).symm hb₂.isPullback
    rw [hb.cancelMap_snd hb₂]
    exact hb.isPullback
  map_zero g := by
    refine Subtype.ext (hb₂.isPullback.hom_ext ?_ ?_)
    · simp only [RelPoint.along]
      rw [Category.assoc, hb.cancelMap_fst hb₂, ← Category.assoc, (e.ab.zero g).2,
        (d'.ab.zero (g ≫ h₁)).2]
    · have e1 : (e.ab.zero g).1 ≫ hb.map = (d.ab.zero (g ≫ h₁ ≫ h₂)).1 :=
        congrArg Subtype.val (hb.map_zero g)
      have e2 : (d'.ab.zero (g ≫ h₁)).1 ≫ hb₂.map = (d.ab.zero ((g ≫ h₁) ≫ h₂)).1 :=
        congrArg Subtype.val (hb₂.map_zero (g ≫ h₁))
      simp only [RelPoint.along]
      rw [Category.assoc, hb.cancelMap_snd hb₂, e1, e2, Category.assoc]
  map_add := fun {_} {g} x y => by
    refine Subtype.ext (hb₂.isPullback.hom_ext ?_ ?_)
    · simp only [RelPoint.along]
      rw [Category.assoc, hb.cancelMap_fst hb₂, ← Category.assoc, (e.ab.add x y).2,
        (d'.ab.add _ _).2]
    · have e1 : (e.ab.add x y).1 ≫ hb.map
          = (d.ab.add (RelPoint.along hb.map hb.isPullback.w x)
              (RelPoint.along hb.map hb.isPullback.w y)).1 :=
        congrArg Subtype.val (hb.map_add x y)
      have e2 : ∀ a b : RelPoint d'.f (g ≫ h₁), (d'.ab.add a b).1 ≫ hb₂.map
          = (d.ab.add (RelPoint.along hb₂.map hb₂.isPullback.w a)
              (RelPoint.along hb₂.map hb₂.isPullback.w b)).1 :=
        fun a b => congrArg Subtype.val (hb₂.map_add a b)
      simp only [RelPoint.along]
      rw [Category.assoc, hb.cancelMap_snd hb₂, e1, e2]
      refine d.ab.add_val_congr (Category.assoc g h₁ h₂) _ _ _ _ ?_ ?_ <;>
        · simp only [RelPoint.along]
          rw [Category.assoc, hb.cancelMap_snd hb₂]
  map_sec := by
    refine hb₂.isPullback.hom_ext ?_ ?_
    · rw [Category.assoc, hb.cancelMap_fst hb₂, ← Category.assoc, e.pt.sec_comp,
        Category.id_comp, Category.assoc, d'.pt.sec_comp, Category.comp_id]
    · rw [Category.assoc, hb.cancelMap_snd hb₂, hb.map_sec, Category.assoc,
        Category.assoc, hb₂.map_sec]

/-- **`RelPoint.along` is injective at a cartesian square** (PROVEN 2026-07-30),
stated on the underlying morphisms so that no base-point transport is involved
— the `Γ₁` transcription of `X0.lean`'s `IsBaseChangeOf.along_injective`, and
the only piece of that file's `along` API that
`nonempty_gamma1RigidifiedModuli_of_iso` below needs.  `alongInv` and
`alongEquiv` are NOT transcribed: the level-structure half of that transport is
`exists_abelianFullLevelStructure_baseChange`, which is already PROVEN, so the
additive equivalence never has to be built here. -/
lemma along_injective {T' T : Scheme.{u}} {h : T' ⟶ T} {d' : Gamma1Datum N T'}
    {d : Gamma1Datum N T} (bc : IsBaseChangeOfGamma1 h d' d) {U : Scheme.{u}} {g : U ⟶ T'}
    {a b : RelPoint d'.f g} (hab : a.1 ≫ bc.map = b.1 ≫ bc.map) : a = b :=
  Subtype.ext (bc.isPullback.hom_ext (by rw [a.2, b.2]) hab)

end IsBaseChangeOfGamma1

/-! #### The rigidified moduli scheme, and the two halves of (8.1.1)/(8.1.3)

**The cut of `exists_gamma1GITPresentation`, 2026-07-27.**  What was one
sorry leaf is now ONE leaf plus proven glue, along the same line
Katz–Mazur themselves draw and the same line `X0.lean` draws between
`exists_rigidifiedModuli` and `exists_gamma0GITPresentation_of_rigidified`:

| what | where | status |
|---|---|---|
| the rigidified moduli scheme, its deck group, its cover and its torsor property | `Gamma1Rigidification` / `exists_gamma1Rigidification` | **PROVEN** (2026-07-28), over the three leaves of the cut below — see the section comment "The cut of `exists_gamma1Rigidification`" |
| the invariants `B = A^G`, the structure morphism of the coarse space, and the DESCENT of the classifying map | `exists_descendClassifyGamma1` / `nonempty_gamma1GITPresentation_of_rigidification` | **PROVEN** (8.1.3) |

**`coequalises` is REQUIRED and its absence makes the descent half FALSE
— here is the counterexample that found it.**  The tempting
`Gamma1Rigidification` is `Gamma1GITPresentation` minus the `classify`
block, i.e. `cover` + `strM_invariant` + `dM_equivariant`.  That is not
enough.  Take `A = A₀ × A₀` with `G` acting diagonally on a genuine
rigidified `A₀`, `dM` the disjoint union of two copies of the universal
family, and `strM` the same on both factors.  Then `cover` holds (map
into the first copy), `strM_invariant` and `dM_equivariant` hold, and
`B = A^G = B₀ × B₀`.  But the two inclusions `ι₁, ι₂ : Spec A₀ ⟶ Spec A`
pull `dM` back to ISOMORPHIC data, so naturality of any `classify` at
`h = 𝟙` forces `ι₁ ≫ π = ι₂ ≫ π`, which is false because the two land in
different factors of `Spec (B₀ × B₀)`.  So `classify` with
`classify_dM` cannot exist over that rigidification, and a descent leaf
stated without `coequalises` would be FALSE, not merely hard.

`coequalises` is exactly what excludes it, it is exactly clause (b) of
`X0.lean`'s `exists_deckAction`, and it is TRUE of the Katz–Mazur
construction: two level-`n` structures on one curve differ by a
*locally constant* `GL₂(ℤ/n)`-valued comparison, which equalises the two
composites with `π` piecewise and hence globally.  The section comment
above `Gamma0Atlas` in `X0.lean` records the same fact as the reason the
descent route needs "a strictly stronger field — the torsor property";
that field is this one.

Note `dM_equivariant` is NOT derivable from `coequalises` and vice versa:
the first says `σ^*dM ≅ dM`, the second is the converse direction, and
`Gamma1GITPresentation.toGamma1Atlas` consumes only the first while
`exists_descendClassifyGamma1` consumes only the second.

## FALSITY AUDIT (2026-07-29): `coequalises` was UNSATISFIABLE over a general base, and is now repaired

**The defect.**  `coequalises` was transcribed from `X0.lean`'s
`exists_deckAction` clause (b) with no change.  Over `X0.lean`'s base
`SpecQ` that is harmless, because `Subsingleton (Z ⟶ SpecQ)` holds for
every scheme `Z` (a morphism to `Spec ℚ` is a ring map `ℚ →+* Γ(Z, ⊤)`,
and there is at most one).  Over a general `S` — and `Spec K` for a
number field `K` is general — the missing clause is REAL CONTENT, and
without it the field is not merely too strong: **no inhabitant of
`Gamma1Rigidification N (Spec K)` can satisfy it** for suitable `K`, so
`exists_gamma1Rigidification` was FALSE as stated, and with it
`exists_gamma1DeckAction`, which is what fills the field.

**Why `coequalises` forces `a ≫ strM = b ≫ strM`.**  `S = Spec K` is
affine and so is `Spec A`, and `Spec` is fully faithful on affines, so
`strM = Spec φ` for a unique `φ : K →+* A`.  `strM_invariant` says
`Spec (σ •) ≫ Spec φ = Spec φ`, i.e. `σ • ∘ φ = φ` for every `σ : G`,
i.e. `φ` lands in `A^G`.  Hence `strM = specInvariantsQuotient G A ≫ str'`
with `str' = Spec (φ : K →+* A^G)`, and therefore
`a ≫ π = b ≫ π` IMPLIES `a ≫ strM = b ≫ strM`.  So any pair `a, b`
rigidifying one datum with DIFFERENT structure morphisms to `S` refutes
the old field.

**The witness, and it needs nothing but `cover`.**  Take `N = 5` and an
elliptic curve `E/ℚ` with a rational point `P` of exact order `5` (e.g.
`11a3 = X₁(11)`), let `K = ℚ(E[3])` — a nontrivial Galois extension of
`ℚ`, since it contains `ζ₃` — and let `σ ∈ Gal(K/ℚ)`, `σ ≠ 1`.  Put
`d₁ := (E_K, P_K)`, a `Gamma1Datum 5 (Spec K)`.  Because `E` and `P` are
defined over `ℚ`, the `σ`-conjugate datum is canonically `d₁` again:
`(Spec σ)^* d₁ ≅ d₁`.  Now let `R : Gamma1Rigidification 5 (Spec K)` be
ANY inhabitant and apply `R.cover` twice to the same datum `d₁` with two
different structure morphisms:

* at `g := 𝟙`, giving `p₁ : T₁ ⟶ Spec K` fppf, `d'₁` on `T₁` and
  `m₁ : T₁ ⟶ Spec A` with `m₁ ≫ strM = p₁`;
* at `g := Spec σ`, giving `p₂ : T₂ ⟶ Spec K` fppf, `d'₂` on `T₂` and
  `m₂ : T₂ ⟶ Spec A` with `m₂ ≫ strM = p₂ ≫ Spec σ`.

Set `Z := T₁ ×_{Spec K} T₂` with projections `q₁, q₂`, so
`q₁ ≫ p₁ = q₂ ≫ p₂ =: w`, and set `a := q₁ ≫ m₁`, `b := q₂ ≫ m₂`.  Both
`a` and `b` exhibit the SAME datum `d_Z := w^* d₁` as a base change of
`dM` — for `b` this uses `(Spec σ)^* d₁ ≅ d₁` — so the old `coequalises`
applies and gives `a ≫ π = b ≫ π`, hence `a ≫ strM = b ≫ strM`, i.e.
`w = w ≫ Spec σ`.  But `w` is a composite of two fppf morphisms, hence an
epimorphism, so `Spec σ = 𝟙` and `σ = 1`.  Contradiction.

**The repair, and why it costs nothing.**  The Katz–Mazur torsor
statement is about two level structures on one datum *of `S`-schemes*:
`𝔐([Γ₁(N)], [Γ(n)]) → 𝔐([Γ₁(N)])` is a `GL₂(ℤ/n)`-torsor over `S`, and
"the same point of `𝔐([Γ₁(N)])`" includes the `S`-structure.  So the
field gains the hypothesis `a ≫ strM = b ≫ strM`, which is exactly what
was silently free over `SpecQ`.  Every consumer already holds it:
`exists_descendClassifyGamma1` uses `hcoeq` twice and both times the
equation is available from `hcov`'s `p ≫ g = m ≫ strM` clause (the first
was being discarded as `-`), at the price of the same hypothesis on that
theorem's own second conclusion clause — where all three call sites in
`nonempty_gamma1GITPresentation_of_rigidification` supply it, again from
`R.cover`.  **`Gamma1GITPresentation` is unchanged**, so nothing below
this cluster moves.

**Corroboration from this file itself.**  `Gamma1Atlas.quotient` — the
same "does not separate two rigidifications of one datum" condition, one
layer up — ALREADY carries `a ≫ strM = b ≫ strM`, and so does
`Gamma1Rigidification.cover` carry its own over-`S` clause
`p ≫ g = m ≫ strM` with a docstring saying that clause "is what
`Gamma0Atlas.cover` gets for free from `subsingleton_hom_specQ`".  So the
`Γ₀ → Γ₁` over-`S` audit was performed on every neighbouring field and
missed exactly one; `coequalises` is the only place in the cluster where
the free-over-`ℚ` clause was dropped rather than restored.

*The check that would refute this audit*: exhibit
`R : Gamma1Rigidification N (Spec K)` and `a, b, d₁` as above with
`a ≫ strM ≠ b ≫ strM` and `a ≫ π = b ≫ π` — impossible by the
factorisation paragraph — or show that `(Spec σ)^* d₁ ≇ d₁` for a datum
defined over the prime field, which is false by base-change transitivity. -/

/-- **The Katz–Mazur rigidified moduli scheme for `[Γ₁(N)]`, over an
arbitrary base scheme `S`** — the output of (8.1.1), with the descended
classifying map of (8.1.3) deliberately NOT included.

This is `Gamma1GITPresentation` with `B`, `str`, `classify`,
`classify_natural` and `classify_dM` removed and `coequalises` added; the
removed fields are all PROVEN from these ones in
`nonempty_gamma1GITPresentation_of_rigidification` below, and the added
one is what makes that proof possible at all (see the section comment for
the counterexample).

The `Γ₀` analogue is `RigidifiedModuli` together with the two clauses of
`exists_deckAction`, which `X0.lean` keeps separate because its `A` comes
from a fine moduli scheme via a chosen affine presentation.  Here the
whole package is one structure, since nothing in this file needs the
fine moduli property on its own. -/
structure Gamma1Rigidification (N : ℕ) (S : Scheme.{0}) where
  /-- the coordinate ring of the rigidified moduli scheme `𝔐([Γ₁(N)], [Γ(n)])` -/
  A : Type
  [commRing_A : CommRing A]
  /-- the deck group `GL₂(ℤ/n)` of the rigidification -/
  G : Type
  [group_G : Group G]
  [finite_G : Finite G]
  [action_GA : MulSemiringAction G A]
  /-- the structure morphism of the rigidified moduli scheme -/
  strM : Spec (CommRingCat.of A) ⟶ S
  /-- the universal family it carries -/
  dM : Gamma1Datum N (Spec (CommRingCat.of A))
  /-- **rigidification**: every datum over an `S`-scheme is, after a
  faithfully flat quasi-compact base change **of `S`-schemes**, a base
  change of `dM`.  Verbatim `Gamma1GITPresentation.cover`. -/
  cover : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T),
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T')
      (m : T' ⟶ Spec (CommRingCat.of A)),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      p ≫ g = m ≫ strM ∧
      Nonempty (IsBaseChangeOfGamma1 p d' d) ∧ Nonempty (IsBaseChangeOfGamma1 m d' dM)
  /-- **the deck group acts over the base** -/
  strM_invariant : ∀ σ : G,
    Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)) ≫ strM = strM
  /-- **`G`-equivariance of the universal family**: `σ^*dM ≅ dM` -/
  dM_equivariant : ∀ σ : G, ∃ d₁ : Gamma1Datum N (Spec (CommRingCat.of A)),
    Nonempty (IsBaseChangeOfGamma1 (𝟙 (Spec (CommRingCat.of A))) d₁ dM) ∧
    Nonempty (IsBaseChangeOfGamma1
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ))) d₁ dM)
  /-- **the torsor property**: the quotient map coequalises ANY two
  rigidifications of one datum **over `S`**, not merely `𝟙` and `Spec σ`
  for a global `σ : G`.  Without this field the descent below is FALSE —
  see the section comment.

  `hab` was MISSING until 2026-07-29 and its absence made the field
  unsatisfiable over a general base — see the FALSITY AUDIT in the
  section comment for the witness.  It is free over `Spec ℚ`, which is
  why `X0.lean` does not carry it, and every consumer here already holds
  it. -/
  coequalises : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of A))
    (d₁ : Gamma1Datum N Z), a ≫ strM = b ≫ strM →
    IsBaseChangeOfGamma1 a d₁ dM →
    IsBaseChangeOfGamma1 b d₁ dM →
    a ≫ specInvariantsQuotient G A = b ≫ specInvariantsQuotient G A

/-- **fpqc descent of the classifying map, over an ARBITRARY base**
(PROVEN 2026-07-27) — Katz–Mazur (8.1.3), and the half of
`exists_gamma1GITPresentation` that mentions no level structure, no deck
group construction and no modular curve.

The `Γ₁` analogue of `X0.lean`'s `exists_descendClassify`, stated over an
abstract finite group acting on an abstract commutative ring with the
rigidified cover and the coequalising property as hypotheses.

**The one place it is not a transcription: the base.**  `X0.lean`'s
version takes `_g : T ⟶ SpecQ` and never uses it, because
`Subsingleton (T ⟶ Spec ℚ)` makes `c ≫ str = g` automatic.  Over a
general `S` that clause is real content and is now part of the
conclusion, proved from the `p ≫ g = m ≫ strM` clause of `cover` — which
`Gamma0GITPresentation.cover` does not even carry — together with
`hstr` and cancellation of the fpqc epimorphism.

## How it is proven

`hcov` produces a flat surjective quasi-compact `p : T' ⟶ T`, a datum
`d'` on `T'` which is a base change of `d`, and a rigidification
`m₀ : T' ⟶ Spec A` of `d'`.

* **The descent datum, and it costs no fibre product.**  mathlib's
  `EffectiveEpiStruct` is stated against *every* pair `g₁, g₂ : Z ⟶ T'`
  with `g₁ ≫ p = g₂ ≫ p`, so the kernel pair is never named.  Base-change
  `d'` along `g₁` (`exists_gamma1Datum_baseChange`) to get `d₁` over `Z`;
  composing with `bp` makes `d₁` a base change of `d` along
  `g₁ ≫ p = g₂ ≫ p`, and `IsBaseChangeOfGamma1.cancel` turns that into
  `IsBaseChangeOfGamma1 g₂ d₁ d'`.  So `g₁ ≫ m₀` and `g₂ ≫ m₀` are two
  rigidifications of ONE datum, which is the shape `hcoeq` wants.
* **The descent.**  `AlgebraicGeometry.fpqcTopology` is `Subcanonical`,
  so a flat surjective quasi-compact `p` is an `EffectiveEpi`, and
  `EffectiveEpi.desc` factors the equalised morphism through `p`.
* **Independence of the cover** is the `∀ Z k dZ m` clause: pull the
  cover back to `Z ×_T T'`, whose first projection is a base change of
  `p` hence again an epimorphism, and compare there.

## Faithfulness

`hcoeq` is a hypothesis, so a degenerate `G`-action does not make this
leaf false — it makes `hcoeq` unsatisfiable and the statement vacuously
true at that action.  The counterexample in the section comment above is
precisely a rigidification at which `hcoeq` fails and no `c` exists. -/
theorem exists_descendClassifyGamma1 (N : ℕ) (G : Type) [Group G] [Finite G]
    {A : Type} [CommRing A] [MulSemiringAction G A] {S : Scheme.{0}}
    (strM : Spec (CommRingCat.of A) ⟶ S)
    (str : Spec (CommRingCat.of ↥(FixedPoints.subring A G)) ⟶ S)
    (hstr : specInvariantsQuotient G A ≫ str = strM)
    (dM : Gamma1Datum N (Spec (CommRingCat.of A)))
    (hcov : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T),
      ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T')
        (m : T' ⟶ Spec (CommRingCat.of A)),
        AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
        p ≫ g = m ≫ strM ∧
        Nonempty (IsBaseChangeOfGamma1 p d' d) ∧ Nonempty (IsBaseChangeOfGamma1 m d' dM))
    (hcoeq : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of A))
      (d₁ : Gamma1Datum N Z), a ≫ strM = b ≫ strM →
      IsBaseChangeOfGamma1 a d₁ dM →
      IsBaseChangeOfGamma1 b d₁ dM →
      a ≫ specInvariantsQuotient G A = b ≫ specInvariantsQuotient G A)
    (T : Scheme.{0}) (g : T ⟶ S) (d : Gamma1Datum N T) :
    ∃ c : T ⟶ Spec (CommRingCat.of ↥(FixedPoints.subring A G)),
      c ≫ str = g ∧
      ∀ (Z : Scheme.{0}) (k : Z ⟶ T) (dZ : Gamma1Datum N Z),
        IsBaseChangeOfGamma1 k dZ d →
        ∀ m : Z ⟶ Spec (CommRingCat.of A), m ≫ strM = k ≫ g →
          IsBaseChangeOfGamma1 m dZ dM →
          k ≫ c = m ≫ specInvariantsQuotient G A := by
  classical
  -- the rigidifying cover of `d`, and the rigidification `m₀` it carries
  obtain ⟨T', p, d', m₀, hf, hs, hq, hst, ⟨bp⟩, ⟨bm⟩⟩ := hcov g d
  haveI := hf; haveI := hs; haveI := hq
  -- `m₀ ≫ π` coequalises every pair that `p` coequalises
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ T'), g₁ ≫ p = g₂ ≫ p →
      g₁ ≫ (m₀ ≫ specInvariantsQuotient G A)
        = g₂ ≫ (m₀ ≫ specInvariantsQuotient G A) := by
    intro Z g₁ g₂ he
    obtain ⟨d₁, ⟨b₁⟩⟩ := exists_gamma1Datum_baseChange g₁ d'
    have hb : IsBaseChangeOfGamma1 (g₂ ≫ p) d₁ d := by rw [← he]; exact b₁.comp bp
    -- the two rigidifications are rigidifications OVER `S`; this is the clause
    -- `hcoeq` gained on 2026-07-29, and `hst` is exactly what supplies it
    have hab : (g₁ ≫ m₀) ≫ strM = (g₂ ≫ m₀) ≫ strM := by
      calc (g₁ ≫ m₀) ≫ strM = (g₁ ≫ p) ≫ g := by
            rw [Category.assoc, ← hst, ← Category.assoc]
        _ = (g₂ ≫ p) ≫ g := by rw [he]
        _ = (g₂ ≫ m₀) ≫ strM := by rw [Category.assoc, hst, ← Category.assoc]
    rw [← Category.assoc, ← Category.assoc]
    exact hcoeq (g₁ ≫ m₀) (g₂ ≫ m₀) d₁ hab (b₁.comp bm) ((hb.cancel bp).comp bm)
  refine ⟨EffectiveEpi.desc p (m₀ ≫ specInvariantsQuotient G A) key, ?_, ?_⟩
  · -- the descended map is a morphism over `S`: check it after the epimorphism `p`
    refine (cancel_epi p).mp ?_
    rw [← Category.assoc, EffectiveEpi.fac, Category.assoc, hstr, hst]
  · -- independence of the cover: compare on `Z ×_T T'`
    intro Z k dZ bk m hm bmZ
    have hcond : Limits.pullback.fst k p ≫ k = Limits.pullback.snd k p ≫ p :=
      Limits.pullback.condition
    obtain ⟨dW, ⟨bq⟩⟩ := exists_gamma1Datum_baseChange (Limits.pullback.fst k p) dZ
    have hb : IsBaseChangeOfGamma1 (Limits.pullback.snd k p ≫ p) dW d := by
      rw [← hcond]; exact bq.comp bk
    -- again the over-`S` clause of `hcoeq`, this time from `hm` and `hst`
    have hab : (Limits.pullback.fst k p ≫ m) ≫ strM
        = (Limits.pullback.snd k p ≫ m₀) ≫ strM := by
      calc (Limits.pullback.fst k p ≫ m) ≫ strM
          = (Limits.pullback.fst k p ≫ k) ≫ g := by
            rw [Category.assoc, hm, ← Category.assoc]
        _ = (Limits.pullback.snd k p ≫ p) ≫ g := by rw [hcond]
        _ = (Limits.pullback.snd k p ≫ m₀) ≫ strM := by
            rw [Category.assoc, hst, ← Category.assoc]
    have h1 : (Limits.pullback.fst k p ≫ m) ≫ specInvariantsQuotient G A
        = (Limits.pullback.snd k p ≫ m₀) ≫ specInvariantsQuotient G A :=
      hcoeq _ _ dW hab (bq.comp bmZ) ((hb.cancel bp).comp bm)
    refine (cancel_epi (Limits.pullback.fst k p)).mp ?_
    calc Limits.pullback.fst k p
          ≫ k ≫ EffectiveEpi.desc p (m₀ ≫ specInvariantsQuotient G A) key
        = (Limits.pullback.snd k p ≫ p)
            ≫ EffectiveEpi.desc p (m₀ ≫ specInvariantsQuotient G A) key := by
          rw [← Category.assoc, hcond]
      _ = Limits.pullback.snd k p ≫ (m₀ ≫ specInvariantsQuotient G A) := by
          rw [Category.assoc, EffectiveEpi.fac]
      _ = Limits.pullback.fst k p ≫ m ≫ specInvariantsQuotient G A := by
          rw [← Category.assoc, ← Category.assoc]; exact h1.symm

/-- **A rigidification IS a GIT presentation** (PROVEN 2026-07-27) — the
formalisation half of `exists_gamma1GITPresentation`, with the
Katz–Mazur citation discharged by `R`.

## What was owed, and where each piece is discharged

* **`B` and `Algebra.IsInvariant`**: `B` is `FixedPoints.subring R.A R.G`
  and `algebra_BA` is `RingHom.toAlgebra` of the subring inclusion, so
  `algebraMap B A` is definitionally that inclusion — which is what makes
  `classify_dM` an equation about `specInvariantsQuotient`.
  `Algebra.IsInvariant`, `SMulCommClass` and `injective_algebraMap` are
  one-liners from that choice.
* **`str`, the structure morphism of the coarse space**: this is where
  the `Γ₁` development departs from the `Γ₀` one.  `X0.lean` builds it by
  hand from `Spec.preimage R.strM` and `RingHom.codRestrict`, using
  `subsingleton_hom_specQ` to see that the resulting `ℚ →+* A` is
  `G`-fixed.  Over a general base there is no such ring map to restrict,
  so `str` comes instead from the EXISTENCE half of
  `specInvariants_universal` applied to `R.strM` and `R.strM_invariant`,
  and `hstr` is its factorisation clause.
* **`classify`, `classify_natural`, `classify_dM`**: the descent,
  `exists_descendClassifyGamma1` above.  Naturality is the
  characterisation compared after a rigidifying cover and the cover
  cancelled; `classify_dM` is the characterisation read at the trivial
  cover `𝟙` of `Spec A` rigidified by `𝟙`, which is what
  `IsBaseChangeOfGamma1.refl` exists for.
* **`cover`, `strM_invariant`, `dM_equivariant`**: verbatim from `R`.

Does NOT owe: any Katz–Mazur citation.  Representability, the deck group,
the torsor and the cover are all `R`. -/
theorem nonempty_gamma1GITPresentation_of_rigidification {N : ℕ} {S : Scheme.{0}}
    (R : Gamma1Rigidification N S) : Nonempty (Gamma1GITPresentation N S) := by
  classical
  letI := R.commRing_A
  letI := R.group_G
  letI := R.finite_G
  letI := R.action_GA
  -- the ring of invariants, as a subring of `A`
  letI : Algebra ↥(FixedPoints.subring R.A R.G) R.A :=
    RingHom.toAlgebra (Subring.subtype _)
  haveI : Algebra.IsInvariant ↥(FixedPoints.subring R.A R.G) R.A R.G :=
    ⟨fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  haveI : SMulCommClass R.G ↥(FixedPoints.subring R.A R.G) R.A :=
    ⟨fun σ b a => by
      show σ • ((b : R.A) * a) = (b : R.A) * (σ • a)
      rw [smul_mul', b.2 σ]⟩
  have hinj : Function.Injective (algebraMap ↥(FixedPoints.subring R.A R.G) R.A) :=
    Subtype.val_injective
  -- the structure morphism of the coarse space, from the GIT quotient property
  obtain ⟨str, hstr, -⟩ := specInvariants_universal R.G hinj R.strM R.strM_invariant
  have hstr' : specInvariantsQuotient R.G R.A ≫ str = R.strM := hstr
  -- the descended classifying map, together with its characterisation
  choose c hc1 hc2 using fun (T : Scheme.{0}) (g : T ⟶ S) (d : Gamma1Datum N T) =>
    exists_descendClassifyGamma1 N R.G R.strM str hstr' R.dM
      (fun {_T} g₀ d₀ => R.cover g₀ d₀)
      (fun {_Z} a b d₁ hab h₁ h₂ => R.coequalises a b d₁ hab h₁ h₂) T g d
  refine ⟨{ A := R.A
            B := ↥(FixedPoints.subring R.A R.G)
            G := R.G
            action_GA := R.action_GA
            injective_algebraMap := hinj
            str := str
            strM := R.strM
            classify := fun {T} g d => ⟨c T g d, hc1 T g d⟩
            classify_natural := ?_
            dM := R.dM
            classify_dM := ?_
            cover := fun {_T} g d => R.cover g d
            strM_invariant := R.strM_invariant
            dM_equivariant := R.dM_equivariant }⟩
  · -- naturality: both sides agree after the rigidifying cover of `d'`, and
    -- that cover is an epimorphism.
    intro T' T h g g' hg d' d bch
    refine Subtype.ext ?_
    show c T' g' d' = h ≫ c T g d
    obtain ⟨Z, p, dZ, m, hf, hs, hq, hst, ⟨bp⟩, ⟨bm⟩⟩ := R.cover g' d'
    haveI := hf; haveI := hs; haveI := hq
    -- the over-`S` clause `hc2` gained on 2026-07-29; `R.cover` supplies it
    have hm2 : m ≫ R.strM = (p ≫ h) ≫ g := by rw [Category.assoc, hg, ← hst]
    have h1 := hc2 T' g' d' Z p dZ bp m hst.symm bm
    have h2 := hc2 T g d Z (p ≫ h) dZ (bp.comp bch) m hm2 bm
    refine (cancel_epi p).mp ?_
    rw [h1, ← Category.assoc, h2]
  · -- the classifying map of the universal family is the quotient map: read
    -- the characterisation at the trivial cover of `Spec A`, rigidified by `𝟙`.
    show c _ R.strM R.dM = Spec.map (CommRingCat.ofHom
      (algebraMap ↥(FixedPoints.subring R.A R.G) R.A))
    have h1 := hc2 _ R.strM R.dM _ (𝟙 _) R.dM (IsBaseChangeOfGamma1.refl R.dM) (𝟙 _)
      rfl (IsBaseChangeOfGamma1.refl R.dM)
    rw [Category.id_comp, Category.id_comp] at h1
    exact h1

/-! #### The cut of `exists_gamma1Rigidification`, 2026-07-28

The node below used to be one leaf owing `A`, `G`, `strM`, `dM` and four
Props.  It is now PROVEN, over the cut `X0.lean` takes one step further
down: interpose a **fine** moduli scheme for the RIGIDIFIED problem
`[Γ₁(N)], [Γ(n)]`, and derive the deck group, its equivariance and the
torsor clause from the fine moduli property rather than assuming them.

| what | where | status |
|---|---|---|
| the fine moduli scheme `𝔐([Γ₁(N)], [Γ(n)])`, AFFINE | `Gamma1RigidifiedModuli` / `exists_gamma1RigidifiedModuli` | **PROVEN** 2026-07-30, over the two citation leaves `exists_gamma1RigidifiedModuliScheme` (4.7.2 + 5.1.1 + 6.6.2) and `isAffine_of_gamma1RigidifiedModuliScheme` (the affineness parenthesis of 8.1.1) |
| the level-`n` torsor: every datum acquires a full level structure fpqc-locally | `exists_gamma1FullLevelStructure_cover` | **LEAF** (2.3.1 / 8.1.1) |
| the deck action `GL₂(ℤ/n) ↷ A`, its invariance over `S`, `dM_equivariant` and `coequalises` | `exists_gamma1DeckAction` | **PROVEN** 2026-07-29 (after being REFUTED and restated — see its FALSITY AUDIT) |
| two level structures on ONE datum differ Zariski-locally by a constant matrix | `exists_openCover_twist_of_abelianFullLevelStructure` | **PROVEN** 2026-07-30 over the single geometric leaf `isOpenImmersion_equalizer_of_abelianFullLevelStructure` (the `Γ₁`, arbitrary-base analogue of a PROVEN `Γ₀` theorem, cut the same way its `Γ₀` original was) |
| the equalizer of two `n`-torsion sections is OPEN | `isOpenImmersion_equalizer_of_abelianFullLevelStructure` | **LEAF** (Katz–Mazur 2.3.1: `n` invertible makes `E[n] ⟶ Z` étale) |
| the assembly | `nonempty_gamma1Rigidification_of_rigidifiedModuli` | **PROVEN** |

**Why this is not the junk-witness trap.**  The section comment before
`RigidifiedModuli` in `X0.lean` rejects the "obvious" split — a structure
holding the moduli scheme with `cover` stated as a `∀` over it — because
an arbitrary inhabitant of such a structure need not be the genuine
moduli scheme, and the companion leaf would then be FALSE at the junk
witness.  `Gamma1RigidifiedModuli.universal` is a **fine** moduli
property, so its inhabitant is pinned up to unique isomorphism, and
quantifying over it (which is what `exists_gamma1DeckAction` does) is
safe.  That is the whole reason the citation and the formalisation can be
separated at all.

**Two `Γ₀ → Γ₁` transcription hazards, and both bite here.**

* `RigidifiedModuli.universal` has **no "over the base" clause**, because
  `Subsingleton (T ⟶ Spec ℚ)` makes `m ≫ strM = g` automatic there.  Over
  a general `S` — and `Spec K` is general — it is real content, so
  `Gamma1RigidifiedModuli.universal` carries it as a conjunct.  It is
  exactly what discharges the `p ≫ g = m ≫ strM` clause of
  `Gamma1Rigidification.cover`, which `Gamma0GITPresentation.cover` does
  not even have.
* `Gamma0GITPresentation` has no `strM_invariant` field at all, for the
  same reason.  `Gamma1Rigidification` does, so `exists_gamma1DeckAction`
  carries it as its first clause; it comes from the uniqueness half of
  `universal` applied at `g := strM`, so it costs the prover nothing
  beyond what the deck action already gives.

**COORDINATION NOTE — `AbelianFullLevelStructure` duplicates
`FullLevelStructure` and should not, 2026-07-28.**  `X0.lean`'s
`FullLevelStructure n (d : Gamma0Datum N T)` never inspects `d.cyc`: it
mentions `d` only through `d.f` and `d.ab`.  The structure below is the
same statement over a bare `AbelianSchemeStruct`, written here because
`X0.lean`'s region has other concurrent owners.  **The right repair is in
`X0.lean`**: change `FullLevelStructure`'s parameter from
`d : Gamma0Datum N T` to `abs : AbelianSchemeStruct f`, at which point ONE
definition serves both moduli problems, this one can be deleted, and —
this is the part that matters — the whole twist API
(`FullLevelStructure.twistP`/`twistQ`/`twist`/`twist_one`/`twist_mul`/
`geomBasis_twist`, ~290 lines, all of it already PROVEN) becomes available
to `Γ₁` unchanged.

**UPDATE 2026-07-29: the duplication happened.**  The repair was not made
— `X0.lean` still has other concurrent owners — so the twist API was
TRANSCRIBED here instead, in the block before
`exists_openCover_twist_of_abelianFullLevelStructure`, together with
`exists_abelianFullLevelStructure_of_geomBasis`,
`exists_abelianFullLevelStructure_baseChange` and `twist_baseChange`.
That transcription is what turned `exists_gamma1DeckAction` from a leaf
into a PROVEN theorem over one named geometric leaf, exactly as this note
predicted; but the note's verdict stands, and the debt is now ~450 lines
rather than ~290.  Whoever generalises `FullLevelStructure` should delete
all of it, and should note that nothing UNDER the twist API had to be
duplicated — `RelPoint.comb`, `comb_comb` and `pre_comb` are already
stated over a bare `AbelianSchemeStruct`, which is the evidence that the
generalisation is mechanical. -/

/-- **A full level-`n` structure on an abelian scheme**, stated over a
bare `AbelianSchemeStruct` rather than over a datum — Katz–Mazur's
`[Γ(n)]`, in the fibrewise idiom this development already uses.

**This is `X0.lean`'s `FullLevelStructure` with the `Gamma0Datum`
parameter generalised away, and it is a DUPLICATE that should be
removed** — see the COORDINATION NOTE in the section comment above for
the one-line repair in `X0.lean` that removes it.  Every remark on
`FullLevelStructure` applies verbatim and is not repeated here; the two
that matter are:

* `nsmul_P` and `nsmul_Q` are FIELDS and are **not** consequences of
  `geom_basis`.  `X0.lean` carries the `Spec ℚ(ζ_n)[ε]` counterexample:
  every geometric point kills `ε`, so `(P₀ + εv, Q₀)` satisfies
  `geom_basis` for every `v ∈ Lie(E₀)` while `n • (P₀ + εv) = nεv ≠ 0`.
  Without the fields `GL₂(ℤ/n)` does not act (`ZMod.val` is not
  multiplicative) and the moduli functor is not representable.
* At `n = 0` the condition is unsatisfiable (`Fin 0` is empty while
  `0 • x = 0` always), which is why every consumer below carries
  `3 ≤ n`. -/
structure AbelianFullLevelStructure (n : ℕ) {E T : Scheme.{u}} {f : E ⟶ T}
    (abs : AbelianSchemeStruct f) where
  /-- the first basis section -/
  P : RelPoint f (𝟙 T)
  /-- the second basis section -/
  Q : RelPoint f (𝟙 T)
  /-- **`P` is `n`-torsion over the base** — not a consequence of
  `geom_basis`; see the docstring -/
  nsmul_P : letI := abs.addCommGroup (𝟙 T); n • P = 0
  /-- **`Q` is `n`-torsion over the base** -/
  nsmul_Q : letI := abs.addCommGroup (𝟙 T); n • Q = 0
  /-- at every geometric point `P` and `Q` are a basis of the `n`-torsion -/
  geom_basis : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (t : Spec (CommRingCat.of K) ⟶ T),
      letI := abs.addCommGroup t
      ∀ x : RelPoint f t, n • x = 0 ↔
        ∃! c : Fin n × Fin n,
          x = (c.1 : ℕ) • RelPoint.pre t (Category.comp_id t) P
              + (c.2 : ℕ) • RelPoint.pre t (Category.comp_id t) Q

/-- **The rigidified moduli scheme `𝔐([Γ₁(N)], [Γ(n)])` as an AFFINE FINE
moduli scheme over an arbitrary base** — the `Γ₁` analogue of `X0.lean`'s
`RigidifiedModuli`, and Katz–Mazur (8.1.1)'s `M(𝒫, 𝒮)` at
`𝒫 = [Γ₁(N)]`, `𝒮 = [Γ(n)]`.

The data is an affine `S`-scheme `Spec A`, a universal `Γ₁(N)`-datum `dM`
on it carrying a universal full level-`n` structure `lvlM`, and the fine
moduli property: a datum-with-level-structure over an `S`-scheme is the
base change of `(dM, lvlM)` along a **unique** `S`-morphism.

## Why `universal` carries `m ≫ strM = g` and `RigidifiedModuli` does not

`X0.lean` works over `Spec ℚ`, where `Subsingleton (T ⟶ SpecQ)` makes the
clause automatic — its docstring says so explicitly ("the structure
morphism needs no compatibility field").  Over a general `S` it is real
content, and it is what `Gamma1Rigidification.cover`'s
`p ≫ g = m ≫ strM` clause is discharged from.  Dropping it would leave
that clause unprovable and would also break `strM_invariant`, which is
read off the uniqueness half at `g := strM`.

## Level compatibility is stated on the underlying morphisms

Verbatim `RigidifiedModuli`'s reason: `RelPoint.along bc.map _ L.P` lands
over `𝟙 T ≫ m` while `RelPoint.pre m _ lvlM.P` lands over `m`, and the
two are equal only propositionally, so the points inhabit different
types.  Unfolding both to `.1` removes the transport with no loss.

## Why quantifying over this structure is safe

`universal` is a FINE moduli property, so an inhabitant is pinned up to
unique isomorphism.  See the section comment above. -/
structure Gamma1RigidifiedModuli (N n : ℕ) (S : Scheme.{0}) where
  /-- the coordinate ring of the rigidified moduli scheme -/
  A : Type
  [commRing_A : CommRing A]
  /-- the structure morphism to the base -/
  strM : Spec (CommRingCat.of A) ⟶ S
  /-- the universal `Γ₁(N)`-datum -/
  dM : Gamma1Datum N (Spec (CommRingCat.of A))
  /-- the universal full level-`n` structure on it -/
  lvlM : AbelianFullLevelStructure n dM.ab
  /-- **fine moduli**: a datum-with-level-structure over an `S`-scheme is
  the base change of `(dM, lvlM)` along a UNIQUE `S`-morphism -/
  universal : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T)
      (L : AbelianFullLevelStructure n d.ab),
    ∃! m : T ⟶ Spec (CommRingCat.of A),
      m ≫ strM = g ∧
      ∃ bc : IsBaseChangeOfGamma1 m d dM,
        L.P.1 ≫ bc.map = m ≫ lvlM.P.1 ∧ L.Q.1 ≫ bc.map = m ≫ lvlM.Q.1

/-! **`exists_gamma1RigidifiedModuli` used to sit here.**  It moved down on
2026-07-30, when it was split three ways (see the section comment before
`Gamma1RigidifiedModuliScheme`): the transport half consumes
`exists_abelianFullLevelStructure_baseChange`, which is defined below, so the
whole group had to follow it.  Nothing between the two positions consumed the
node. -/

/-! #### The cut of `exists_gamma1FullLevelStructure_cover`, 2026-07-28

The node used to be one leaf owing the whole level-`n` torsor together
with the transport of a fibrewise basis into an
`AbelianFullLevelStructure`.  It is now PROVEN, over the cut `X0.lean`
takes on the `Γ₀` side: separate the GEOMETRY (a flat surjective
quasi-compact cover over which the `n`-torsion acquires a basis) from the
BOOKKEEPING (turning that basis into a level structure on the
base-changed datum).

| what | where | status |
|---|---|---|
| the level-`n` torsor over a base field | `exists_torsionBasisCover_field` | **LEAF** (Katz–Mazur 2.3.1 / 5.1.1, Silverman *AEC* III.6.4) |
| base change of a `Γ₁(N)`-datum | `nonempty_gamma1Datum_baseChange` | **PROVEN** (2026-07-27) |
| `IsBaseChangeOfGamma1.toRelPoint` and its additivity | this block | **PROVEN** |
| the transport | `nonempty_abelianFullLevelStructure_of_geomBasis` | **PROVEN** |
| the assembly | `exists_gamma1FullLevelStructure_cover` | **PROVEN** |

**THREE CORRECTIONS to the previous docstring of this node, all found by
grepping its claims (2026-07-28).**

* It said `nonempty_gamma1Datum_baseChange` was "already a leaf in this
  file".  It is **PROVEN** — it is a one-line consequence of
  `exists_gamma1Datum_baseChange`, itself PROVEN 2026-07-27 from
  `Gamma1BaseChange.datumBC` / `isBaseChangeBC`.
* It said of the four `Γ₀` declarations that "**none of them mentions
  `Gamma0Datum` except through `d.ab`**".  That is true of
  `exists_torsionBasis_geomPoint` and
  `exists_torsionBasis_cover_of_geomPoint`, and **false** of the other
  two: `exists_gamma0Datum_baseChange` is entirely about `Gamma0Datum`,
  and `nonempty_fullLevelStructure_of_geomBasis` takes an
  `IsBaseChangeOf` between `Gamma0Datum`s and concludes
  `Nonempty (FullLevelStructure n d')`.  So the transport had to be
  transcribed to `IsBaseChangeOfGamma1` / `AbelianFullLevelStructure`
  rather than reused; that transcription is the block below and it is
  line-for-line the `Γ₀` proof.
* It said the node "reduces to them **without new mathematics**".  It
  does not, and this is the substantive correction.  Every geometric
  declaration in the `Γ₀` chain — `exists_torsionBasis_geomPoint`,
  `exists_zmodBasis_torsion_geomPoint`, `exists_torsionBasis_cover_of_`
  `geomPoint`, `exists_isomTorsor_of_geomPoint` — carries a hypothesis
  `g : T ⟶ SpecQ`, i.e. it is stated **only over `ℚ`-schemes**, where
  every `n` is automatically invertible.  This node is over an arbitrary
  field `K` with `char K ∤ n`, so the Silverman *AEC* III.6.4 input it
  needs is the positive-characteristic form.  The mathematics is
  standard, but it is not the released statement, and reducing to the
  `Γ₀` leaves verbatim is **impossible**: the base does not match.
  `exists_torsionBasisCover_field` below is that general-base statement,
  and it is the one new leaf this cut leaves open.

  (Refuting command, if this ever needs rechecking:
  `grep -n 'SpecQ' Fermat/FLT/ModularCurve/X0.lean` at those four
  declarations.  If they acquire a general base, this leaf becomes a
  transcription and should be closed against them.)

**Ownership note.** `exists_zmodBasis_torsion_geomPoint` and
`exists_isomTorsor_of_geomPoint` — the `ℚ` forms of exactly the content
`exists_torsionBasisCover_field` owes — had a live owner on 2026-07-28.
Whoever closes them should be asked for the general-base form at the same
time; the `ℚ` hypothesis is used in both only to know `n` is invertible
on `T`. -/

namespace IsBaseChangeOfGamma1

variable {N : ℕ} {T' T : Scheme.{u}} {p : T' ⟶ T}
  {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}

/-- **A relative point of `d'`, read as a relative point of `d`**
(PROVEN) — compose with the morphism on total spaces.  The base point
moves from `u : U ⟶ T'` to `u ≫ p`.

Verbatim `IsBaseChangeOf.toRelPoint` of `X0.lean`, transcribed because
that one is typed by `Gamma0Datum`; see the CORRECTIONS in the section
comment above. -/
def toRelPoint (bc : IsBaseChangeOfGamma1 p d' d) {U : Scheme.{u}} {u : U ⟶ T'}
    (x : RelPoint d'.f u) : RelPoint d.f (u ≫ p) :=
  RelPoint.along bc.map bc.isPullback.w x

/-- **`toRelPoint` is injective** (PROVEN), because the square is
cartesian: the two points already agree after `d'.f`. -/
theorem toRelPoint_injective (bc : IsBaseChangeOfGamma1 p d' d) {U : Scheme.{u}}
    {u : U ⟶ T'} : Function.Injective (bc.toRelPoint (U := U) (u := u)) := by
  intro x y hxy
  refine Subtype.ext (bc.isPullback.hom_ext ?_ ?_)
  · rw [x.2, y.2]
  · exact congrArg Subtype.val hxy

/-- **`toRelPoint` preserves the zero section** (PROVEN) — this is
`map_zero`, read through the `AddCommGroup` instances on relative
points. -/
theorem toRelPoint_zero (bc : IsBaseChangeOfGamma1 p d' d) {U : Scheme.{u}} (u : U ⟶ T') :
    letI := d'.ab.addCommGroup u
    letI := d.ab.addCommGroup (u ≫ p)
    bc.toRelPoint (0 : RelPoint d'.f u) = 0 :=
  bc.map_zero u

/-- **`toRelPoint` is additive** (PROVEN) — this is `map_add`, read
through the `AddCommGroup` instances on relative points. -/
theorem toRelPoint_add (bc : IsBaseChangeOfGamma1 p d' d) {U : Scheme.{u}} {u : U ⟶ T'}
    (x y : RelPoint d'.f u) :
    letI := d'.ab.addCommGroup u
    letI := d.ab.addCommGroup (u ≫ p)
    bc.toRelPoint (x + y) = bc.toRelPoint x + bc.toRelPoint y :=
  bc.map_add x y

/-- **Hence `toRelPoint` commutes with the `ℕ`-action** (PROVEN), which is
what carries the `n`-torsion condition across the base change. -/
theorem toRelPoint_nsmul (bc : IsBaseChangeOfGamma1 p d' d) {U : Scheme.{u}} {u : U ⟶ T'}
    (k : ℕ) (x : RelPoint d'.f u) :
    letI := d'.ab.addCommGroup u
    letI := d.ab.addCommGroup (u ≫ p)
    bc.toRelPoint (k • x) = k • bc.toRelPoint x := by
  letI := d'.ab.addCommGroup u
  letI := d.ab.addCommGroup (u ≫ p)
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul]; exact bc.toRelPoint_zero u
  | succ k ih => rw [succ_nsmul, succ_nsmul, bc.toRelPoint_add, ih]

/-- **`n`-torsion descends across a cartesian square** (PROVEN).
`toRelPoint` is an injective additive map, so a relative point upstairs
is `n`-torsion as soon as its image downstairs is.  Consumed by
`nonempty_abelianFullLevelStructure_of_geomBasis` to fill
`AbelianFullLevelStructure`'s `nsmul_P` / `nsmul_Q` fields, which — see
that structure's docstring — genuinely cannot be read off
`geom_basis`. -/
theorem nsmul_eq_zero_of_toRelPoint {n : ℕ} (bc : IsBaseChangeOfGamma1 p d' d)
    {U : Scheme.{u}} {u : U ⟶ T'} (X : RelPoint d'.f u)
    (h : letI := d.ab.addCommGroup (u ≫ p); n • bc.toRelPoint X = 0) :
    letI := d'.ab.addCommGroup u
    n • X = 0 := by
  letI := d'.ab.addCommGroup u
  letI := d.ab.addCommGroup (u ≫ p)
  refine bc.toRelPoint_injective ?_
  rw [bc.toRelPoint_nsmul, h, bc.toRelPoint_zero]

end IsBaseChangeOfGamma1

/-- **A fibrewise basis over the cover IS a full level structure on the
base-changed datum** (PROVEN 2026-07-28) — the transport half of the
level-`n` torsor, and the `Γ₁` transcription of `X0.lean`'s
`nonempty_fullLevelStructure_of_geomBasis`.

`P` and `Q` are sections of `d.f` over `p`, i.e. relative points of the
ORIGINAL datum at the base point `p : T' ⟶ T`.  The cartesian square of
`bc` lifts each of them to a section of `d'.f` over `𝟙 T'`
(`IsPullback.lift (𝟙 T') P.1`), which is what `AbelianFullLevelStructure`
asks for, and `IsPullback.lift_snd` says the lift maps back to `P`.  The
`geom_basis` field then transports along `bc.toRelPoint`, using only that
it is INJECTIVE and additive.  No *type* transport occurs anywhere: the
statement is phrased through `RelPoint.pre t rfl` on the `d`-side and
`RelPoint.pre t (comp_id t)` on the `d'`-side, and `toRelPoint` moves the
base point from `t` to `t ≫ p` on the nose.

`hnP` / `hnQ` are what fill the `nsmul_P` / `nsmul_Q` fields; they cannot
be dropped and cannot be derived from `hb` — see
`AbelianFullLevelStructure`'s `Spec ℚ(ζ_n)[ε]` counterexample. -/
theorem nonempty_abelianFullLevelStructure_of_geomBasis {N n : ℕ} {T' T : Scheme.{u}}
    {p : T' ⟶ T} {d : Gamma1Datum N T} {d' : Gamma1Datum N T'}
    (bc : IsBaseChangeOfGamma1 p d' d) (P Q : RelPoint d.f p)
    (hnP : letI := d.ab.addCommGroup p; n • P = 0)
    (hnQ : letI := d.ab.addCommGroup p; n • Q = 0)
    (hb : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T'),
        letI := d.ab.addCommGroup (t ≫ p)
        ∀ x : RelPoint d.f (t ≫ p), n • x = 0 ↔
          ∃! c : Fin n × Fin n,
            x = (c.1 : ℕ) • RelPoint.pre t rfl P + (c.2 : ℕ) • RelPoint.pre t rfl Q) :
    Nonempty (AbelianFullLevelStructure n d'.ab) := by
  refine ⟨{ P := ⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
              bc.isPullback.lift_fst _ _ _⟩
            Q := ⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
              bc.isPullback.lift_fst _ _ _⟩
            nsmul_P := ?_
            nsmul_Q := ?_
            geom_basis := ?_ }⟩
  · refine bc.nsmul_eq_zero_of_toRelPoint _ ?_
    rw [show bc.toRelPoint
          (⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
            bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T'))
        = RelPoint.pre (𝟙 T') (rfl : 𝟙 T' ≫ p = 𝟙 T' ≫ p) P from
      Subtype.ext (by
        show bc.isPullback.lift (𝟙 T') P.1 _ ≫ bc.map = 𝟙 T' ≫ P.1
        rw [bc.isPullback.lift_snd, Category.id_comp])]
    exact RelPoint.nsmul_pre_eq_zero d.ab (𝟙 T') rfl hnP
  · refine bc.nsmul_eq_zero_of_toRelPoint _ ?_
    rw [show bc.toRelPoint
          (⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
            bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T'))
        = RelPoint.pre (𝟙 T') (rfl : 𝟙 T' ≫ p = 𝟙 T' ≫ p) Q from
      Subtype.ext (by
        show bc.isPullback.lift (𝟙 T') Q.1 _ ≫ bc.map = 𝟙 T' ≫ Q.1
        rw [bc.isPullback.lift_snd, Category.id_comp])]
    exact RelPoint.nsmul_pre_eq_zero d.ab (𝟙 T') rfl hnQ
  intro K _ _ t
  letI := d'.ab.addCommGroup t
  letI := d.ab.addCommGroup (t ≫ p)
  have hP : bc.toRelPoint (RelPoint.pre t (Category.comp_id t)
      (⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
        bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T')))
      = RelPoint.pre t (rfl : t ≫ p = t ≫ p) P := by
    refine Subtype.ext ?_
    show (t ≫ bc.isPullback.lift (𝟙 T') P.1 _) ≫ bc.map = t ≫ P.1
    rw [Category.assoc, bc.isPullback.lift_snd]
  have hQ : bc.toRelPoint (RelPoint.pre t (Category.comp_id t)
      (⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
        bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T')))
      = RelPoint.pre t (rfl : t ≫ p = t ≫ p) Q := by
    refine Subtype.ext ?_
    show (t ≫ bc.isPullback.lift (𝟙 T') Q.1 _) ≫ bc.map = t ≫ Q.1
    rw [Category.assoc, bc.isPullback.lift_snd]
  intro x
  have hinj := bc.toRelPoint_injective (U := Spec (CommRingCat.of K)) (u := t)
  rw [← hinj.eq_iff, bc.toRelPoint_nsmul, bc.toRelPoint_zero t]
  rw [hb K t (bc.toRelPoint x)]
  constructor
  · rintro ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · refine hinj ?_
      rw [bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
      exact hc
    · intro c' hc'
      refine huniq c' ?_
      rw [hc', bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
  · rintro ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · rw [hc, bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
    · intro c' hc'
      refine huniq c' (hinj ?_)
      rw [bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
      exact hc'

/-! #### The cut of `exists_torsionBasisCover_field`, 2026-07-30

The leaf below asked for the `Γ₀` chain `exists_torsionBasis_geomPoint` +
`exists_torsionBasis_cover_of_geomPoint` with the base changed from `SpecQ`
to `Spec K`, and its docstring is right that neither applies as stated:
**both carry `g : T ⟶ SpecQ`**, and so does everything under them.

Following that chain down to where the `ℚ`-base is actually *spent* shows
it is spent in exactly TWO places, both of them for the single fact
`(n : K') ≠ 0` at a geometric point:

| `Γ₀` (`X0.lean`) | what it spends `g` on | `Γ₁` analogue here |
|---|---|---|
| `isFinite_flat_nTorsion` | **nothing** — its `_g` is unused | `isFinite_flat_nTorsion_noBase`, PROVEN |
| `isReduced_geomFibre_nTorsion_of_specQBase` | `CharZero K'`, hence `(n : K') ≠ 0` | `isReduced_geomFibre_nTorsion_field`, PROVEN |
| `etale_nTorsion_of_specQBase` | only via the two above | `etale_nTorsion_of_fieldBase`, PROVEN |
| `exists_zmodBasis_torsion_geomPoint` | `CharZero K'`, hence `(n : K') ≠ 0` | `exists_zmodBasis_torsion_geomPoint_field`, PROVEN |
| `exists_torsionBasis_geomPoint` | only via the above | `exists_torsionBasis_geomPoint_field`, PROVEN |
| `exists_isomTorsor_of_etale_nTorsion` | **nothing** — the `Isom`-sheaf | `exists_isomTorsor_of_etale_nTorsion_noBase`, **LEAF** |
| `exists_torsionBasis_cover_of_geomPoint` | only via the above | `exists_torsionBasisCover_field`, PROVEN |

`natCast_ne_zero_geomPoint_of_fieldBase` is the replacement for the
`CharZero` step: `t ≫ g : Spec K' ⟶ Spec K` gives a ring map `K →+* K'`
on global sections, it is injective because `K` is a field, and
`¬ ringChar K ∣ n` is `(n : K) ≠ 0` by `ringChar.spec`.  That is a
STRICTLY weaker input than characteristic zero, which is why the `Γ₀`
chain's `CharZero` route could not be reused verbatim but its skeleton
could.

**WHAT IS LEFT IS EXACTLY ONE THING, AND IT IS ALREADY OWED IN `X0.lean`.**
`exists_isomTorsor_of_etale_nTorsion_noBase` below is
`X0.lean`'s `exists_isomTorsor_of_etale_nTorsion` **with its `g : T ⟶ SpecQ`
deleted** — that hypothesis does nothing there either, as that node's own
docstring says ("it owes nothing about characteristic, ranks, flatness or
finiteness: `hetale` is `Etale (E[n] ⟶ T)`, and finite + étale is everything
the construction uses").  So the base-free form is strictly stronger and
**a proof of it closes the `Γ₀` leaf as a one-liner**; the two should have a
single owner.  It is restated here rather than generalised in place because
`X0.lean` has several concurrent owners and this file cannot be imported by
it.  If that node is ever generalised in `X0.lean`, THIS declaration is the
one to delete. -/

/-- **A geometric point of a `K`-scheme has `n` invertible in its residue
field, when `n` is prime to `char K`** (PROVEN 2026-07-30) — the
replacement, over an arbitrary field base, for the `CharZero` step that
`X0.lean`'s `ℚ`-side chain uses twice.

`t ≫ g : Spec K' ⟶ Spec K` induces `K →+* K'` on global sections through
`Scheme.ΓSpecIso`; a ring map out of a field is injective; and
`¬ ringChar K ∣ n` is `(n : K) ≠ 0` by `ringChar.spec`. -/
theorem natCast_ne_zero_geomPoint_of_fieldBase {T : Scheme.{0}} (n : ℕ) (K : Type) [Field K]
    (hchar : ¬ ringChar K ∣ n)
    (g : T ⟶ Spec (CommRingCat.of K)) (K' : Type) [Field K']
    (t : Spec (CommRingCat.of K') ⟶ T) : (n : K') ≠ 0 := by
  obtain ⟨ψ⟩ : Nonempty (K →+* K') :=
    ⟨((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (t ≫ g).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K')).hom).hom⟩
  have hK : (n : K) ≠ 0 := fun h => hchar ((ringChar.spec K n).mp h)
  intro h
  exact hK (ψ.injective (by rw [map_natCast, h, map_zero]))

/-- **The `n`-torsion at a geometric point of a `K`-scheme is free of rank
two over `ℤ/n`** (PROVEN 2026-07-30) — `X0.lean`'s
`exists_zmodBasis_torsion_geomPoint` with `SpecQ` relaxed to `Spec K`.

Its proof transcribes verbatim except for its first three lines, which
derive `CharZero K'` from the `ℚ`-base; here
`natCast_ne_zero_geomPoint_of_fieldBase` supplies the `(n : K') ≠ 0` those
lines existed to produce.  Everything after that is unchanged:
`exists_weierstrassModel_geomFibreAddEquiv_of_geomPoint` (a `sorry` leaf in
`X0.lean`, but one that carries NO base morphism, which is what makes this
generalisation possible at all) reads the geometric fibre as the points of a
Weierstrass elliptic curve, `WeierstrassCurve.n_torsion_dimension` is the
Silverman *AEC* III.6.4 citation, and `exists_zmodBasis_of_torsionEquiv` is
pure algebra.

`hchar` is load-bearing for TRUTH, exactly as `g` is on the `Γ₀` side: over
`K' = 𝔽̄_p` with `p ∣ n` the `p`-torsion is `ℤ/p` (ordinary) or trivial
(supersingular), so no pair `(y, z)` can be both independent and spanning. -/
theorem exists_zmodBasis_torsion_geomPoint_field (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) (g : T ⟶ Spec (CommRingCat.of K))
    (K' : Type) [Field K'] [IsAlgClosed K'] (t : Spec (CommRingCat.of K') ⟶ T) :
    letI := ab.addCommGroup t
    ∃ y z : RelPoint f t, n • y = 0 ∧ n • z = 0 ∧
      (∀ x : RelPoint f t, n • x = 0 → ∃ a b : ℕ, x = a • y + b • z) ∧
      (∀ a b : ℕ, a • y + b • z = 0 → n ∣ a ∧ n ∣ b) := by
  letI := ab.addCommGroup t
  have hnK' : (n : K') ≠ 0 := natCast_ne_zero_geomPoint_of_fieldBase n K hchar g K' t
  letI : DecidableEq K' := Classical.typeDecidableEq K'
  obtain ⟨W, hW, ⟨φ⟩⟩ := exists_weierstrassModel_geomFibreAddEquiv_of_geomPoint ab hdim K' t
  haveI := hW
  obtain ⟨χ⟩ := W.n_torsion_dimension (n := n) hnK'
  exact exists_zmodBasis_of_torsionEquiv (by omega)
    ((TorsionCounting.torsionByCongr (n : ℤ) φ).trans χ)

/-- **The `n`-torsion at a geometric point of a `K`-scheme has unique
`Fin n`-coordinates** (PROVEN 2026-07-30) — the leaf above read through
`nsmul_eq_zero_iff_existsUnique_finPair`, which is pure algebra; the `Γ₁`
mirror of `exists_torsionBasis_geomPoint`, and like it nothing but the
citation in the shape `FullLevelStructure.geom_basis` asks for. -/
theorem exists_torsionBasis_geomPoint_field (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) (g : T ⟶ Spec (CommRingCat.of K))
    (K' : Type) [Field K'] [IsAlgClosed K'] (t : Spec (CommRingCat.of K') ⟶ T) :
    letI := ab.addCommGroup t
    ∃ y z : RelPoint f t, ∀ x : RelPoint f t, n • x = 0 ↔
      ∃! c : Fin n × Fin n, x = (c.1 : ℕ) • y + (c.2 : ℕ) • z := by
  letI := ab.addCommGroup t
  obtain ⟨y, z, hy, hz, hspan, hindep⟩ :=
    exists_zmodBasis_torsion_geomPoint_field n hn K hchar ab hdim g K' t
  exact ⟨y, z, nsmul_eq_zero_iff_existsUnique_finPair (by omega) hy hz hspan hindep⟩

/-- **`E[n] ⟶ T` is finite and flat, over ANY base** (PROVEN 2026-07-30) —
`X0.lean`'s `isFinite_flat_nTorsion` with the two hypotheses its own
docstring records as unused (`_hdim` and `_g : T ⟶ SpecQ`) deleted rather
than underscored, which is what makes it usable here.  The proof is that
node's, verbatim: `[n]` is proper, locally of finite type and quasi-finite,
hence finite, and flat; and `nTorsionStructure_eq_snd` makes the structure
morphism of `E[n]` a base change of it. -/
theorem isFinite_flat_nTorsion_noBase (n : ℕ) (hn : 3 ≤ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f) :
    IsFinite (Limits.pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f) ∧
      AlgebraicGeometry.Flat (Limits.pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f) := by
  have hn0 : n ≠ 0 := by omega
  haveI : IsProper (ab.mulByNat n) := ab.isProper_mulByNat n
  haveI : LocallyOfFiniteType (ab.mulByNat n) := ab.locallyOfFiniteType_mulByNat n
  haveI : LocallyQuasiFinite (ab.mulByNat n) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_mulByNat ab n hn0)
  haveI : IsFinite (ab.mulByNat n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : AlgebraicGeometry.Flat (ab.mulByNat n) := flat_mulByNat ab n hn0
  rw [nTorsionStructure_eq_snd n ab]
  exact ⟨inferInstance, inferInstance⟩

/-- **Every geometric fibre of `E[n]` is REDUCED over a `K`-base with
`char K ∤ n`** (PROVEN 2026-07-30) — `X0.lean`'s
`isReduced_geomFibre_nTorsion_of_specQBase` with `SpecQ` relaxed to
`Spec K`, and the ONLY place in this chain where `hchar` is spent.

The proof is that node's, verbatim, with its `CharZero K'` step replaced by
`natCast_ne_zero_geomPoint_of_fieldBase`: `[n]` is formally unramified over
the geometric point because `n` is invertible there, base change preserves
that, and finite + formally unramified over a field is reduced.

`hchar` is load-bearing for TRUTH: at `char K = p ∣ n` the scheme `E[p]` is
an infinitesimal group scheme (`μ_p` or `α_p` in the supersingular case),
finite flat of rank `p²` and NOT reduced. -/
theorem isReduced_geomFibre_nTorsion_field (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (g : T ⟶ Spec (CommRingCat.of K)) :
    ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (t : Spec (CommRingCat.of K') ⟶ T),
      IsReduced (Limits.pullback
        (Limits.pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f) t) := by
  intro K' _ _ t
  have hnK' : (n : K') ≠ 0 := natCast_ne_zero_geomPoint_of_fieldBase n K hchar g K' t
  haveI hfin : IsFinite (Limits.pullback.snd (ab.mulByNat n) ab.zeroSection) := by
    rw [← nTorsionStructure_eq_snd n ab]
    exact (isFinite_flat_nTorsion_noBase n hn ab).1
  rw [nTorsionStructure_eq_snd n ab]
  set abK := ab.baseChange t
  have hP := ab.isPullback_ker_baseChange t n
  haveI : IsFinite (Limits.pullback.snd (abK.mulByNat n) abK.zeroSection) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hP hfin
  haveI : FormallyUnramified (abK.mulByNat n) := formallyUnramified_mulByNat K' abK n hnK'
  haveI : FormallyUnramified (Limits.pullback.snd (abK.mulByNat n) abK.zeroSection) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _)
      inferInstance
  haveI : IsReduced (Limits.pullback (abK.mulByNat n) abK.zeroSection) :=
    AlgebraicGeometry.isReduced_of_formallyUnramified_over_field
      (Limits.pullback.snd (abK.mulByNat n) abK.zeroSection)
  exact isReduced_of_isOpenImmersion hP.isoPullback.inv

/-- **`E[n] ⟶ T` is ÉTALE over a `K`-base with `char K ∤ n`** (PROVEN
2026-07-30) — the `Γ₁` mirror of `etale_nTorsion_of_specQBase`, and like it
just `AlgebraicGeometry.etale_of_isReduced_pullback` applied to finite, flat,
locally of finite presentation and reduced geometric fibres.  Three of the
four are free; only the reducedness spends `hchar`. -/
theorem etale_nTorsion_of_fieldBase (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (g : T ⟶ Spec (CommRingCat.of K)) :
    AlgebraicGeometry.Etale (Limits.pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f) := by
  haveI := (isFinite_flat_nTorsion_noBase n hn ab).1
  haveI := (isFinite_flat_nTorsion_noBase n hn ab).2
  haveI := locallyOfFinitePresentation_nTorsion n ab
  exact AlgebraicGeometry.etale_of_isReduced_pullback _
    (isReduced_geomFibre_nTorsion_field n hn K hchar ab g)

/-- **The `Isom`-scheme of the level-`n` torsor, over an ARBITRARY base**
(sorry leaf, opened 2026-07-30) — `X0.lean`'s
`exists_isomTorsor_of_etale_nTorsion` **with its `g : T ⟶ SpecQ` deleted**.

That hypothesis is inert there: the node's own docstring says it "owes
nothing about characteristic, ranks, flatness or finiteness: `hetale` is
`Etale (E[n] ⟶ T)`, and finite + étale is everything the construction uses".
So this statement is strictly stronger, and **anyone who proves it has
proven the `Γ₀` node as a one-liner** (`fun … g hetale => …`).  They should
have one owner.  It is restated here rather than generalised in place only
because `X0.lean` has several concurrent owners and cannot import this file;
if it is ever generalised there, delete this declaration.

## What the prover owes, and it is unchanged from the `Γ₀` node

The `Isom`-sheaf `Isom_T((ℤ/n)²_T, E[n])`: that it is representable by a
finite étale `T`-scheme `T'` (Katz–Mazur 8.1.1), that the tautological
isomorphism over `T'` is a pair of sections `P, Q` of `E[n]` — hence killed
by `n` ON THE NOSE over `T'`, which is the last conjunct — and that `T'` has
a point over exactly those geometric points of `T` at which `E[n]` admits a
basis.

A concrete route that avoids the general representability machinery, and
which is available because `hetale` is a hypothesis rather than a goal:
`E[n] ×_T E[n]` is finite étale over `T` (composition and base change of
finite étale morphisms, both stable), "being a basis" is a locally constant
condition on a finite étale scheme, so the basis locus is a clopen
subscheme, and it is the `T'` wanted.

Note the conclusion asks only for `Flat` and `QuasiCompact` on `p`;
SURJECTIVITY is not asked for, because it is derived by the consumer from
the third conjunct through `surjective_of_exists_lift_geomPoint`
(`X0.lean`, PROVEN, a statement about schemes only).

## Faithfulness

`hetale` is load-bearing: without `n` invertible, `E[n]` is an
infinitesimal group scheme, no basis exists at any geometric point of
characteristic dividing `n`, and no cover helps.  `hn` is load-bearing at
`n = 0` (`Fin 0` is empty while `0 • x = 0` always); only `0 < n` is used.
`hdim` is load-bearing: at relative dimension `d` the `n`-torsion is
`(ℤ/n)^{2d}` and admits no two-element basis for `d ≥ 2`. -/
theorem exists_isomTorsor_of_etale_nTorsion_noBase (n : ℕ) (hn : 3 ≤ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f)
    (hetale : AlgebraicGeometry.Etale
      (Limits.pullback.fst (ab.mulByNat n) ab.zeroSection ≫ f)) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T),
      AlgebraicGeometry.Flat p ∧ QuasiCompact p ∧
      ∃ P Q : RelPoint f p,
        (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T'),
          letI := ab.addCommGroup (t ≫ p)
          ∀ x : RelPoint f (t ≫ p), n • x = 0 ↔
            ∃! c : Fin n × Fin n,
              x = (c.1 : ℕ) • RelPoint.pre t rfl P + (c.2 : ℕ) • RelPoint.pre t rfl Q) ∧
        (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T),
          (letI := ab.addCommGroup t
            ∃ y z : RelPoint f t, ∀ x : RelPoint f t, n • x = 0 ↔
              ∃! c : Fin n × Fin n, x = (c.1 : ℕ) • y + (c.2 : ℕ) • z) →
          ∃ t' : Spec (CommRingCat.of K) ⟶ T', t' ≫ p = t) ∧
        (letI := ab.addCommGroup p; n • P = 0 ∧ n • Q = 0) :=
  sorry

/-- **The level-`n` torsor over an arbitrary base field: after a flat
surjective quasi-compact cover the `n`-torsion of an abelian scheme of
relative dimension one acquires a basis** (**PROVEN 2026-07-30** over the
cut described in the section comment above; a single sorry leaf from
2026-07-28)
— Katz–Mazur 2.3.1 and 5.1.1's last sentence, Silverman *AEC* III.6.4 for
the geometric fibres.

This is the ONE geometric leaf left under
`exists_gamma1FullLevelStructure_cover`, and it is stated for a **bare
abelian scheme**: it mentions neither `Gamma1Datum` nor any moduli
scheme, so it can be dispatched entirely independently of the `Γ₁` layer,
and it would serve the `Γ₀` layer unchanged.

## What it is, and why it is not the released `Γ₀` statement

It is `X0.lean`'s `exists_torsionBasis_cover_of_geomPoint` composed with
`exists_torsionBasis_geomPoint`, with the base changed from `SpecQ` to
`Spec K` for a field `K` with `char K ∤ n`.  **Both of those carry
`g : T ⟶ SpecQ`**, so neither applies here; see the CORRECTIONS in the
section comment above.  The `ℚ` hypothesis is used in them only to know
that `n` is invertible on `T`, which `hchar` supplies directly: `T` is a
`K`-scheme, so every residue field of `T` is a `K`-algebra and has
characteristic `ringChar K`, and `¬ ringChar K ∣ n` is exactly `n ≠ 0`
in `K`.

## The route

`n` invertible on `T` makes `[n] : E ⟶ E` finite étale, so `E[n] ⟶ T` is
finite étale of rank `n²` and its geometric fibres are `(ℤ/n)²`
(Silverman *AEC* III.6.4, in the form valid in every characteristic prime
to `n`).  The sheaf `Isom_T((ℤ/n)²_T, E[n])` is then a `GL₂(ℤ/n)`-torsor,
representable by a finite étale — in particular flat, surjective,
quasi-compact — cover `T' ⟶ T`, and the tautological isomorphism over
`T'` is the required basis.  Surjectivity is separated out on the `Γ₀`
side as the PROVEN `surjective_of_exists_lift_geomPoint`, which applies
here verbatim, being a statement about schemes only.

## Faithfulness

`hchar` is load-bearing for TRUTH: at `char K ∣ n` the group scheme
`E[n]` is not étale, its geometric fibres are strictly smaller than
`(ℤ/n)²`, and the `∃!` clause is unsatisfiable over a nonempty `T` — no
cover helps.  `g` is load-bearing for the same reason: it is what forces
the residue characteristics of `T` to be `ringChar K`.  `hn` is
load-bearing at `n = 0`, where `Fin 0` is empty while `0 • x = 0` always;
only `0 < n` is actually used, and `3 ≤ n` is carried to match the
consumer.  `hdim` is load-bearing: at relative dimension `d` the
`n`-torsion is `(ℤ/n)^{2d}` and admits no two-element basis for
`d ≥ 2`. -/
theorem exists_torsionBasisCover_field (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {E T : Scheme.{0}} {f : E ⟶ T} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) (g : T ⟶ Spec (CommRingCat.of K)) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      ∃ P Q : RelPoint f p,
        (∀ (L : Type) [Field L] [IsAlgClosed L] (t : Spec (CommRingCat.of L) ⟶ T'),
          letI := ab.addCommGroup (t ≫ p)
          ∀ x : RelPoint f (t ≫ p), n • x = 0 ↔
            ∃! c : Fin n × Fin n,
              x = (c.1 : ℕ) • RelPoint.pre t rfl P + (c.2 : ℕ) • RelPoint.pre t rfl Q) ∧
        (letI := ab.addCommGroup p; n • P = 0 ∧ n • Q = 0) := by
  obtain ⟨T', p, hflat, hqc, P, Q, hbasis, hlift, htors⟩ :=
    exists_isomTorsor_of_etale_nTorsion_noBase n hn ab hdim
      (etale_nTorsion_of_fieldBase n hn K hchar ab g)
  exact ⟨T', p, hflat,
    surjective_of_exists_lift_geomPoint p
      (fun L _ _ t =>
        hlift L t (exists_torsionBasis_geomPoint_field n hn K hchar ab hdim g L t)),
    hqc, P, Q, hbasis, htors⟩

/-- **Every `Γ₁(N)`-datum over a `K`-scheme acquires a full level-`n`
structure after an fpqc cover** (**PROVEN 2026-07-28**; formerly a single
`sorry` leaf) — the `Γ₁` analogue of `X0.lean`'s
`exists_fullLevelStructure_cover`, and Katz–Mazur's finite étale
`GL₂(ℤ/n)`-torsor `[Γ(n)]`.

This is a statement about ONE datum: it names no moduli scheme, no deck
group and no rigidification, which is what let it be dispatched
independently of everything else in this block.

## How it is proven

`exists_torsionBasisCover_field` produces the flat surjective
quasi-compact `p : T' ⟶ T` and the two sections `P, Q` of `d.f` over `p`
that are a basis of the `n`-torsion at every geometric point of `T'`;
`nonempty_gamma1Datum_baseChange` (PROVEN) supplies the datum `d'` over
`T'` together with the cartesian square; and
`nonempty_abelianFullLevelStructure_of_geomBasis` turns the basis into an
`AbelianFullLevelStructure` on `d'.ab`.  Exactly the `Γ₀` assembly of
`exists_fullLevelStructure_cover_of_baseChange`, over an arbitrary base
field instead of over `ℚ`.

## Faithfulness

`hchar` is load-bearing for TRUTH, not merely for the intended proof: in
characteristic `p ∣ n` the scheme `E[n]` is not étale, its geometric
fibres are not `(ℤ/n)²`, and `geom_basis` is unsatisfiable — no cover
helps.  `g` is therefore load-bearing too: it is what makes `T` a
`K`-scheme, and without it the statement is false at a base of bad
characteristic.  Both are passed straight through to
`exists_torsionBasisCover_field`, which is where the content now is.
`hn` is load-bearing at `n = 0`, where `AbelianFullLevelStructure 0` is
unsatisfiable. -/
theorem exists_gamma1FullLevelStructure_cover {N : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of K)) (d : Gamma1Datum N T) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T'),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOfGamma1 p d' d) ∧
      Nonempty (AbelianFullLevelStructure n d'.ab) := by
  obtain ⟨T', p, hflat, hsurj, hqc, P, Q, hb, hnP, hnQ⟩ :=
    exists_torsionBasisCover_field n hn K hchar d.ab d.relativeDimensionOne g
  -- `exists_gamma1Datum_baseChange`, not its alias `nonempty_gamma1Datum_baseChange`:
  -- the alias is declared thousands of lines BELOW this point in the file.
  obtain ⟨d', ⟨bc⟩⟩ := exists_gamma1Datum_baseChange p d
  exact ⟨T', p, d', hflat, hsurj, hqc, ⟨bc⟩,
    nonempty_abelianFullLevelStructure_of_geomBasis bc P Q hnP hnQ hb⟩

/-! #### The `GL₂(ℤ/n)`-twist of an `AbelianFullLevelStructure` (2026-07-29)

`X0.lean` carries this API for `FullLevelStructure`, i.e. for a level
structure typed by a `Gamma0Datum`, and `exists_deckAction_of_torsion`
consumes it.  The `Γ₁` deck action needs the same API for
`AbelianFullLevelStructure`, and the COORDINATION NOTE in the section
comment before `Gamma1RigidifiedModuli` records the right long-term
repair: generalise `X0.lean`'s `FullLevelStructure` from
`d : Gamma0Datum N T` to `abs : AbelianSchemeStruct f`, at which point
ONE definition and ONE twist API serve both moduli problems and the block
below can be deleted.  That repair is not made here, for the reason
`AbelianFullLevelStructure` itself was written here rather than there:
`X0.lean` has other concurrent owners and the edit touches a 62k-line
file.  **The block below is therefore a transcription and is marked as
one**; it is line-for-line `X0.lean`'s `FullLevelStructure` namespace with
`d.ab` replaced by `abs` and `d.f` by `f`, and every remark, FALSITY
AUDIT and counterexample there applies verbatim and is not repeated.

Nothing underneath had to be transcribed: `RelPoint.comb`,
`RelPoint.comb_comb`, `RelPoint.pre_comb`, `nsmul_eq_nsmul_of_mod` and
`mod_eq_of_zmod_eq` are already stated over a bare `AbelianSchemeStruct`
in `X0.lean`, so they are used here unchanged.  That is also the check
that the generalisation really is mechanical: the only `Gamma0Datum` in
the `Γ₀` twist API was the one in the type of the structure.
-/

namespace IsBaseChangeOfGamma1

variable {N : ℕ} {T' T : Scheme.{u}} {p : T' ⟶ T}
  {d' : Gamma1Datum N T'} {d : Gamma1Datum N T}

/-- **`toRelPoint` commutes with `comb`** (PROVEN) — it is additive and
`ℕ`-linear, and `comb` is built from those two.  `X0.lean`'s
`IsBaseChangeOf.toRelPoint_comb`, transcribed. -/
theorem toRelPoint_comb {n : ℕ} (bc : IsBaseChangeOfGamma1 p d' d)
    {U : Scheme.{u}} {u : U ⟶ T'} (a b : ZMod n) (X Y : RelPoint d'.f u) :
    bc.toRelPoint (RelPoint.comb d'.ab a b X Y)
      = RelPoint.comb d.ab a b (bc.toRelPoint X) (bc.toRelPoint Y) := by
  letI := d'.ab.addCommGroup u
  letI := d.ab.addCommGroup (u ≫ p)
  show bc.toRelPoint (a.val • X + b.val • Y)
      = a.val • bc.toRelPoint X + b.val • bc.toRelPoint Y
  rw [bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul]

end IsBaseChangeOfGamma1

namespace AbelianFullLevelStructure

variable {n : ℕ} {E T : Scheme.{u}} {f : E ⟶ T} {abs : AbelianSchemeStruct f}

/-- The first section of the `σ`-twist of a full level structure. -/
noncomputable def twistP (σ : GL (Fin 2) (ZMod n)) (L : AbelianFullLevelStructure n abs) :
    RelPoint f (𝟙 T) :=
  RelPoint.comb abs (σ.val 0 0) (σ.val 0 1) L.P L.Q

/-- The second section of the `σ`-twist of a full level structure. -/
noncomputable def twistQ (σ : GL (Fin 2) (ZMod n)) (L : AbelianFullLevelStructure n abs) :
    RelPoint f (𝟙 T) :=
  RelPoint.comb abs (σ.val 1 0) (σ.val 1 1) L.P L.Q

/-- Transcription of `FullLevelStructure.twistP_one`. -/
theorem twistP_one (h1 : 1 < n) (L : AbelianFullLevelStructure n abs) :
    letI := abs.addCommGroup (𝟙 T)
    twistP 1 L = L.P := by
  letI := abs.addCommGroup (𝟙 T)
  show (((1 : GL (Fin 2) (ZMod n)).val 0 0).val • L.P
      + ((1 : GL (Fin 2) (ZMod n)).val 0 1).val • L.Q) = L.P
  rw [Units.val_one]
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide)]
  rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1]
  simp

/-- Transcription of `FullLevelStructure.twistQ_one`. -/
theorem twistQ_one (h1 : 1 < n) (L : AbelianFullLevelStructure n abs) :
    letI := abs.addCommGroup (𝟙 T)
    twistQ 1 L = L.Q := by
  letI := abs.addCommGroup (𝟙 T)
  show (((1 : GL (Fin 2) (ZMod n)).val 1 0).val • L.P
      + ((1 : GL (Fin 2) (ZMod n)).val 1 1).val • L.Q) = L.Q
  rw [Units.val_one]
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide)]
  rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1]
  simp

/-- The twisted sections are again `n`-torsion over the base, so the twist
stays inside the moduli problem the deck group acts on.  Transcription of
`FullLevelStructure.nsmul_twistP_eq_zero`. -/
theorem nsmul_twistP_eq_zero [NeZero n] (L : AbelianFullLevelStructure n abs)
    (hP : letI := abs.addCommGroup (𝟙 T); n • L.P = 0)
    (hQ : letI := abs.addCommGroup (𝟙 T); n • L.Q = 0) (σ : GL (Fin 2) (ZMod n)) :
    letI := abs.addCommGroup (𝟙 T); n • twistP σ L = 0 := by
  letI := abs.addCommGroup (𝟙 T)
  show n • ((σ.val 0 0).val • L.P + (σ.val 0 1).val • L.Q) = 0
  rw [smul_add, smul_comm n, smul_comm n, hP, hQ, smul_zero, smul_zero, add_zero]

/-- Transcription of `FullLevelStructure.nsmul_twistQ_eq_zero`. -/
theorem nsmul_twistQ_eq_zero [NeZero n] (L : AbelianFullLevelStructure n abs)
    (hP : letI := abs.addCommGroup (𝟙 T); n • L.P = 0)
    (hQ : letI := abs.addCommGroup (𝟙 T); n • L.Q = 0) (σ : GL (Fin 2) (ZMod n)) :
    letI := abs.addCommGroup (𝟙 T); n • twistQ σ L = 0 := by
  letI := abs.addCommGroup (𝟙 T)
  show n • ((σ.val 1 0).val • L.P + (σ.val 1 1).val • L.Q) = 0
  rw [smul_add, smul_comm n, smul_comm n, hP, hQ, smul_zero, smul_zero, add_zero]

/-- **The twisted pair is again a fibrewise basis of the `n`-torsion** —
transcription of `FullLevelStructure.geomBasis_twist`, whose FALSITY AUDIT
(the `ℤ/20`, `n = 6` countermodel showing that `hP` / `hQ` cannot be
dropped) applies here word for word and is not repeated.  The proof is
that one verbatim: `RelPoint.pre_comb` puts the twisted sections in the
original basis, `RelPoint.comb_comb` turns a `ZMod n`-combination of the
twisted pair into the combination by the matrix product, and the two `∃!`s
are the same statement reindexed along the bijection of `(ZMod n)²`
induced by the UNIT `σ`. -/
theorem geomBasis_twist (hn : 3 ≤ n) (L : AbelianFullLevelStructure n abs)
    (hP : letI := abs.addCommGroup (𝟙 T); n • L.P = 0)
    (hQ : letI := abs.addCommGroup (𝟙 T); n • L.Q = 0)
    (σ : GL (Fin 2) (ZMod n)) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T),
      letI := abs.addCommGroup t
      ∀ x : RelPoint f t, n • x = 0 ↔
        ∃! ab : Fin n × Fin n,
          x = (ab.1 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistP σ L)
              + (ab.2 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistQ σ L) := by
  intro K _ _ t
  letI := abs.addCommGroup (𝟙 T)
  letI := abs.addCommGroup t
  haveI : NeZero n := ⟨by omega⟩
  set P₀ : RelPoint f t := RelPoint.pre t (Category.comp_id t) L.P
  set Q₀ : RelPoint f t := RelPoint.pre t (Category.comp_id t) L.Q
  -- the two sections stay `n`-torsion at the geometric point
  have hnP : n • P₀ = 0 := by
    have h1 : RelPoint.pre t (Category.comp_id t) (n • L.P) = n • P₀ :=
      abs.pre_nsmul t (Category.comp_id t) n L.P
    rw [hP] at h1
    rw [← h1]
    exact abs.pre_zero t (Category.comp_id t)
  have hnQ : n • Q₀ = 0 := by
    have h1 : RelPoint.pre t (Category.comp_id t) (n • L.Q) = n • Q₀ :=
      abs.pre_nsmul t (Category.comp_id t) n L.Q
    rw [hQ] at h1
    rw [← h1]
    exact abs.pre_zero t (Category.comp_id t)
  -- the twisted sections, read in the original basis
  have hPt : RelPoint.pre t (Category.comp_id t) (twistP σ L)
      = RelPoint.comb abs (σ.val 0 0) (σ.val 0 1) P₀ Q₀ :=
    RelPoint.pre_comb abs t (Category.comp_id t) (σ.val 0 0) (σ.val 0 1) L.P L.Q
  have hQt : RelPoint.pre t (Category.comp_id t) (twistQ σ L)
      = RelPoint.comb abs (σ.val 1 0) (σ.val 1 1) P₀ Q₀ :=
    RelPoint.pre_comb abs t (Category.comp_id t) (σ.val 1 0) (σ.val 1 1) L.P L.Q
  -- a `ZMod n`-combination of the twisted pair is the matrix-product combination
  have key : ∀ u v : ZMod n,
      u.val • RelPoint.pre t (Category.comp_id t) (twistP σ L)
        + v.val • RelPoint.pre t (Category.comp_id t) (twistQ σ L)
      = (u * σ.val 0 0 + v * σ.val 1 0).val • P₀
        + (u * σ.val 0 1 + v * σ.val 1 1).val • Q₀ := by
    intro u v
    rw [hPt, hQt]
    exact RelPoint.comb_comb abs hnP hnQ u v (σ.val 0 0) (σ.val 0 1) (σ.val 1 0) (σ.val 1 1)
  -- `σ` acts bijectively on the coefficient pairs
  let e : Fin n ≃ ZMod n :=
    { toFun := fun a => ((a : ℕ) : ZMod n)
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := fun a => Fin.ext (ZMod.val_cast_of_lt a.isLt)
      right_inv := fun z => ZMod.natCast_rightInverse z }
  let f2 : Fin n × Fin n ≃ (Fin 2 → ZMod n) :=
    (e.prodCongr e).trans (finTwoArrowEquiv (ZMod n)).symm
  let vm : (Fin 2 → ZMod n) ≃ (Fin 2 → ZMod n) :=
    { toFun := fun w => Matrix.vecMul w σ.val
      invFun := fun w => Matrix.vecMul w σ⁻¹.val
      left_inv := fun w => by
        show Matrix.vecMul (Matrix.vecMul w σ.val) σ⁻¹.val = w
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]
      right_inv := fun w => by
        show Matrix.vecMul (Matrix.vecMul w σ⁻¹.val) σ.val = w
        rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.vecMul_one] }
  let Φ : Fin n × Fin n ≃ Fin n × Fin n := f2.trans (vm.trans f2.symm)
  have hΦ1 : ∀ ab : Fin n × Fin n, ((Φ ab).1 : ℕ)
      = (((ab.1 : ℕ) : ZMod n) * σ.val 0 0 + ((ab.2 : ℕ) : ZMod n) * σ.val 1 0).val := by
    intro ab
    simp [Φ, f2, vm, e, Matrix.vecMul, Fin.sum_univ_two, dotProduct]
  have hΦ2 : ∀ ab : Fin n × Fin n, ((Φ ab).2 : ℕ)
      = (((ab.1 : ℕ) : ZMod n) * σ.val 0 1 + ((ab.2 : ℕ) : ZMod n) * σ.val 1 1).val := by
    intro ab
    simp [Φ, f2, vm, e, Matrix.vecMul, Fin.sum_univ_two, dotProduct]
  have key' : ∀ ab : Fin n × Fin n,
      ((Φ ab).1 : ℕ) • P₀ + ((Φ ab).2 : ℕ) • Q₀
        = (ab.1 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistP σ L)
          + (ab.2 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistQ σ L) := by
    intro ab
    have h := key ((ab.1 : ℕ) : ZMod n) ((ab.2 : ℕ) : ZMod n)
    rw [ZMod.val_cast_of_lt ab.1.isLt, ZMod.val_cast_of_lt ab.2.isLt] at h
    rw [hΦ1, hΦ2, ← h]
  intro x
  rw [L.geom_basis K t x]
  calc (∃! cd : Fin n × Fin n, x = (cd.1 : ℕ) • P₀ + (cd.2 : ℕ) • Q₀)
      ↔ (∃! ab : Fin n × Fin n, x = ((Φ ab).1 : ℕ) • P₀ + ((Φ ab).2 : ℕ) • Q₀) :=
        (Equiv.existsUnique_congr_right (q := fun cd : Fin n × Fin n =>
          x = (cd.1 : ℕ) • P₀ + (cd.2 : ℕ) • Q₀) Φ).symm
    _ ↔ (∃! ab : Fin n × Fin n, x = (ab.1 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistP σ L)
          + (ab.2 : ℕ) • RelPoint.pre t (Category.comp_id t) (twistQ σ L)) := by
        simp only [key']

/-- **The `GL₂(ℤ/n)`-twist of a full level structure.**  Transcription of
`FullLevelStructure.twist`; the `n`-torsion hypotheses `geomBasis_twist`
consumes are the FIELDS `L.nsmul_P` / `L.nsmul_Q`, discharged here. -/
noncomputable def twist (hn : 3 ≤ n) (L : AbelianFullLevelStructure n abs)
    (σ : GL (Fin 2) (ZMod n)) : AbelianFullLevelStructure n abs where
  P := twistP σ L
  Q := twistQ σ L
  nsmul_P :=
    haveI : NeZero n := ⟨by omega⟩
    nsmul_twistP_eq_zero L L.nsmul_P L.nsmul_Q σ
  nsmul_Q :=
    haveI : NeZero n := ⟨by omega⟩
    nsmul_twistQ_eq_zero L L.nsmul_P L.nsmul_Q σ
  geom_basis := geomBasis_twist hn L L.nsmul_P L.nsmul_Q σ

/-- `nsmul_P`, `nsmul_Q` and `geom_basis` are all `Prop`s, so a full level
structure is determined by its two sections. -/
theorem ext' {L₁ L₂ : AbelianFullLevelStructure n abs} (hP : L₁.P = L₂.P) (hQ : L₁.Q = L₂.Q) :
    L₁ = L₂ := by
  cases L₁; cases L₂; subst hP; subst hQ; rfl

/-- Transcription of `FullLevelStructure.twist_one`. -/
theorem twist_one (hn : 3 ≤ n) (L : AbelianFullLevelStructure n abs) : twist hn L 1 = L :=
  ext' (twistP_one (by omega) L) (twistQ_one (by omega) L)

/-- **The twist is an action** — and this is FALSE without the `n`-torsion
hypotheses, since `ZMod.val` is not multiplicative; they are supplied by
`L` itself.  Transcription of `FullLevelStructure.twist_mul`. -/
theorem twist_mul (hn : 3 ≤ n) (L : AbelianFullLevelStructure n abs)
    (σ τ : GL (Fin 2) (ZMod n)) :
    twist hn (twist hn L τ) σ = twist hn L (σ * τ) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ext' ?_ ?_
  · show RelPoint.comb abs (σ.val 0 0) (σ.val 0 1)
        (RelPoint.comb abs (τ.val 0 0) (τ.val 0 1) L.P L.Q)
        (RelPoint.comb abs (τ.val 1 0) (τ.val 1 1) L.P L.Q)
      = RelPoint.comb abs ((σ * τ).val 0 0) ((σ * τ).val 0 1) L.P L.Q
    rw [RelPoint.comb_comb abs L.nsmul_P L.nsmul_Q]
    congr 1 <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · show RelPoint.comb abs (σ.val 1 0) (σ.val 1 1)
        (RelPoint.comb abs (τ.val 0 0) (τ.val 0 1) L.P L.Q)
        (RelPoint.comb abs (τ.val 1 0) (τ.val 1 1) L.P L.Q)
      = RelPoint.comb abs ((σ * τ).val 1 0) ((σ * τ).val 1 1) L.P L.Q
    rw [RelPoint.comb_comb abs L.nsmul_P L.nsmul_Q]
    congr 1 <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

end AbelianFullLevelStructure

/-! #### The moduli problem WITH level structure is a functor, `Γ₁` form

Transcription of `X0.lean`'s block of the same name.  The PINNING is the
point: `nonempty_abelianFullLevelStructure_of_geomBasis` above already
transports a fibrewise basis across a cartesian square, but it returns
`Nonempty`, so the produced structure is not identified with anything and
cannot be fed to the UNIQUENESS half of
`Gamma1RigidifiedModuli.universal`.  The two theorems below are the same
construction stated with the defining property
`L'.P.1 ≫ bc.map = P.1` — literally the shape of `universal`'s
classifying clause.  The `Nonempty` form is left in place because
`exists_gamma1FullLevelStructure_cover` consumes it.
-/

/-- **A fibrewise basis over the cover IS a full level structure on the
base-changed datum, and the structure is PINNED** (PROVEN 2026-07-29) —
`nonempty_abelianFullLevelStructure_of_geomBasis` with the defining
property retained.  Transcription of `X0.lean`'s
`exists_fullLevelStructure_of_geomBasis`; the sections are
`IsPullback.lift (𝟙 T') P.1`, so `IsPullback.lift_snd` gives
`L'.P.1 ≫ bc.map = P.1` immediately. -/
theorem exists_abelianFullLevelStructure_of_geomBasis {N n : ℕ} {T' T : Scheme.{u}}
    {p : T' ⟶ T} {d : Gamma1Datum N T} {d' : Gamma1Datum N T'}
    (bc : IsBaseChangeOfGamma1 p d' d) (P Q : RelPoint d.f p)
    (hnP : letI := d.ab.addCommGroup p; n • P = 0)
    (hnQ : letI := d.ab.addCommGroup p; n • Q = 0)
    (hb : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T'),
        letI := d.ab.addCommGroup (t ≫ p)
        ∀ x : RelPoint d.f (t ≫ p), n • x = 0 ↔
          ∃! c : Fin n × Fin n,
            x = (c.1 : ℕ) • RelPoint.pre t rfl P + (c.2 : ℕ) • RelPoint.pre t rfl Q) :
    ∃ L' : AbelianFullLevelStructure n d'.ab,
      L'.P.1 ≫ bc.map = P.1 ∧ L'.Q.1 ≫ bc.map = Q.1 := by
  refine ⟨{ P := ⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
              bc.isPullback.lift_fst _ _ _⟩
            Q := ⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
              bc.isPullback.lift_fst _ _ _⟩
            nsmul_P := ?_
            nsmul_Q := ?_
            geom_basis := ?_ },
    bc.isPullback.lift_snd _ _ _, bc.isPullback.lift_snd _ _ _⟩
  · refine bc.nsmul_eq_zero_of_toRelPoint _ ?_
    rw [show bc.toRelPoint
          (⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
            bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T'))
        = RelPoint.pre (𝟙 T') (rfl : 𝟙 T' ≫ p = 𝟙 T' ≫ p) P from
      Subtype.ext (by
        show bc.isPullback.lift (𝟙 T') P.1 _ ≫ bc.map = 𝟙 T' ≫ P.1
        rw [bc.isPullback.lift_snd, Category.id_comp])]
    exact RelPoint.nsmul_pre_eq_zero d.ab (𝟙 T') rfl hnP
  · refine bc.nsmul_eq_zero_of_toRelPoint _ ?_
    rw [show bc.toRelPoint
          (⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
            bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T'))
        = RelPoint.pre (𝟙 T') (rfl : 𝟙 T' ≫ p = 𝟙 T' ≫ p) Q from
      Subtype.ext (by
        show bc.isPullback.lift (𝟙 T') Q.1 _ ≫ bc.map = 𝟙 T' ≫ Q.1
        rw [bc.isPullback.lift_snd, Category.id_comp])]
    exact RelPoint.nsmul_pre_eq_zero d.ab (𝟙 T') rfl hnQ
  intro K _ _ t
  letI := d'.ab.addCommGroup t
  letI := d.ab.addCommGroup (t ≫ p)
  have hP : bc.toRelPoint (RelPoint.pre t (Category.comp_id t)
      (⟨bc.isPullback.lift (𝟙 T') P.1 (by rw [Category.id_comp, P.2]),
        bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T')))
      = RelPoint.pre t (rfl : t ≫ p = t ≫ p) P := by
    refine Subtype.ext ?_
    show (t ≫ bc.isPullback.lift (𝟙 T') P.1 _) ≫ bc.map = t ≫ P.1
    rw [Category.assoc, bc.isPullback.lift_snd]
  have hQ : bc.toRelPoint (RelPoint.pre t (Category.comp_id t)
      (⟨bc.isPullback.lift (𝟙 T') Q.1 (by rw [Category.id_comp, Q.2]),
        bc.isPullback.lift_fst _ _ _⟩ : RelPoint d'.f (𝟙 T')))
      = RelPoint.pre t (rfl : t ≫ p = t ≫ p) Q := by
    refine Subtype.ext ?_
    show (t ≫ bc.isPullback.lift (𝟙 T') Q.1 _) ≫ bc.map = t ≫ Q.1
    rw [Category.assoc, bc.isPullback.lift_snd]
  intro x
  have hinj := bc.toRelPoint_injective (U := Spec (CommRingCat.of K)) (u := t)
  rw [← hinj.eq_iff, bc.toRelPoint_nsmul, bc.toRelPoint_zero t]
  rw [hb K t (bc.toRelPoint x)]
  constructor
  · rintro ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · refine hinj ?_
      rw [bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
      exact hc
    · intro c' hc'
      refine huniq c' ?_
      rw [hc', bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
  · rintro ⟨c, hc, huniq⟩
    refine ⟨c, ?_, ?_⟩
    · rw [hc, bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
    · intro c' hc'
      refine huniq c' (hinj ?_)
      rw [bc.toRelPoint_add, bc.toRelPoint_nsmul, bc.toRelPoint_nsmul, hP, hQ]
      exact hc'

/-- **A full level structure pulls back along a base change, PINNED**
(PROVEN 2026-07-29) — transcription of `X0.lean`'s
`exists_fullLevelStructure_baseChange`.  The two `n`-torsion fields
descend by `RelPoint.nsmul_pre_eq_zero`, and `geom_basis` is
`L.geom_basis` read at the geometric point `t ≫ p`; the only friction is
that `pre t _ (pre p _ L.P)` and `pre (t ≫ p) _ L.P` are equal by
`Category.assoc` rather than definitionally. -/
theorem exists_abelianFullLevelStructure_baseChange {N n : ℕ} {T' T : Scheme.{u}} {p : T' ⟶ T}
    {d : Gamma1Datum N T} {d' : Gamma1Datum N T'} (bc : IsBaseChangeOfGamma1 p d' d)
    (L : AbelianFullLevelStructure n d.ab) :
    ∃ L' : AbelianFullLevelStructure n d'.ab,
      L'.P.1 ≫ bc.map = p ≫ L.P.1 ∧ L'.Q.1 ≫ bc.map = p ≫ L.Q.1 := by
  refine exists_abelianFullLevelStructure_of_geomBasis bc
    (RelPoint.pre p (Category.comp_id p) L.P) (RelPoint.pre p (Category.comp_id p) L.Q)
    (RelPoint.nsmul_pre_eq_zero d.ab p (Category.comp_id p) L.nsmul_P)
    (RelPoint.nsmul_pre_eq_zero d.ab p (Category.comp_id p) L.nsmul_Q) ?_
  intro K _ _ t
  letI := d.ab.addCommGroup (t ≫ p)
  have e1 : RelPoint.pre t (rfl : t ≫ p = t ≫ p) (RelPoint.pre p (Category.comp_id p) L.P)
      = RelPoint.pre (t ≫ p) (Category.comp_id (t ≫ p)) L.P :=
    Subtype.ext (Category.assoc t p L.P.1).symm
  have e2 : RelPoint.pre t (rfl : t ≫ p = t ≫ p) (RelPoint.pre p (Category.comp_id p) L.Q)
      = RelPoint.pre (t ≫ p) (Category.comp_id (t ≫ p)) L.Q :=
    Subtype.ext (Category.assoc t p L.Q.1).symm
  intro x
  rw [e1, e2]
  exact L.geom_basis K (t ≫ p) x

/-- **The rigidified moduli scheme as a SCHEME, with affineness NOT
asserted** — `Gamma1RigidifiedModuli` verbatim except that the moduli
scheme is a bare `M : Scheme` rather than `Spec (CommRingCat.of A)`, and
the `Γ₁` transcription of `X0.lean`'s `RigidifiedModuliScheme`.

Every remark on `Gamma1RigidifiedModuli` applies unchanged — in
particular that `universal` is a **fine** moduli property, so an
inhabitant is pinned up to unique isomorphism and quantifying over this
structure is not the junk-witness trap.  That is what makes
`isAffine_of_gamma1RigidifiedModuliScheme` below legitimate as a `∀`. -/
structure Gamma1RigidifiedModuliScheme (N n : ℕ) (S : Scheme.{0}) where
  /-- the rigidified moduli scheme -/
  M : Scheme.{0}
  /-- its structure morphism to the base -/
  strM : M ⟶ S
  /-- the universal `Γ₁(N)`-datum -/
  dM : Gamma1Datum N M
  /-- the universal full level-`n` structure on it -/
  lvlM : AbelianFullLevelStructure n dM.ab
  /-- **fine moduli**: a datum-with-level-structure over an `S`-scheme is
  the base change of `(dM, lvlM)` along a UNIQUE `S`-morphism -/
  universal : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T)
      (L : AbelianFullLevelStructure n d.ab),
    ∃! m : T ⟶ M,
      m ≫ strM = g ∧
      ∃ bc : IsBaseChangeOfGamma1 m d dM,
        L.P.1 ≫ bc.map = m ≫ lvlM.P.1 ∧ L.Q.1 ≫ bc.map = m ≫ lvlM.Q.1

/-! #### The three-way split of `exists_gamma1RigidifiedModuli`, 2026-07-30

The node below used to carry, in one `sorry`, all five Katz–Mazur
citations its docstring records TOGETHER with the transport of an affine
presentation into a `Gamma1RigidifiedModuli`.  It is now split exactly
along the line `X0.lean` draws for the identical `Γ₀` node
(`exists_rigidifiedModuli`, ASSEMBLED 2026-07-27 over
`exists_rigidifiedModuliScheme` / `isAffine_of_rigidifiedModuliScheme` /
`nonempty_rigidifiedModuli_of_isAffine`):

| what | where | status |
|---|---|---|
| representability, affineness not mentioned | `exists_gamma1RigidifiedModuliScheme` | **LEAF** (4.7.1/4.7.2, 5.1.1, 6.6.2) |
| affineness | `isAffine_of_gamma1RigidifiedModuliScheme` | **LEAF** (the parenthesis of 8.1.1) |
| `M ≅ Spec A` transport | `nonempty_gamma1RigidifiedModuli_of_iso` | **PROVEN** |
| `IsAffine` transport | `nonempty_gamma1RigidifiedModuli_of_isAffine` | **PROVEN** |
| the assembly | `exists_gamma1RigidifiedModuli` | **PROVEN** |

**The accounting, stated honestly: this is `1 -> 2` open leaves, not
`1 -> 1`.**  What it buys is that the residues are now pure citations with
no Lean work left in either of them, and the ~120 lines of transport — the
part a formaliser can actually discharge, and the only part of this node
that was not a literature appeal — are done.  The same trade was taken on
the `Γ₀` side and for the same reason.

**Where the `Γ₁` transport is SHORTER than the `Γ₀` one.**  X0's
`nonempty_rigidifiedModuli_of_iso` builds the transported
`FullLevelStructure` by hand: `alongInv` on each of `P` and `Q`, then
`nsmul_P`/`nsmul_Q` through `nsmul_eq_zero_of_toRelPoint`, then
`geom_basis` through an `existsUnique_congr` across `alongEquiv`.  Here
`exists_abelianFullLevelStructure_baseChange` (PROVEN 2026-07-29) already
delivers that structure PINNED, so `alongInv` and `alongEquiv` are never
needed and only `along_injective` is transcribed.  Conversely the `Γ₁`
version owes two things the `Γ₀` version does not: the `map_sec` field of
`IsBaseChangeOfGamma1` (where `IsBaseChangeOf` has `liesIn_iff`), and the
`m ≫ strM = g` conjunct that `Gamma1RigidifiedModuli.universal` carries
because this development works over an arbitrary base `S` rather than over
`Spec ℚ`.  Both are three rewrites. -/

/-- **Katz–Mazur representability of the rigidified `Γ₁` moduli problem**
(sorry leaf, cut 2026-07-30 out of `exists_gamma1RigidifiedModuli` below)
— the first of the two citation halves, and it says NOTHING about
affineness.

## What the prover of this node owes

That the moduli problem "`Γ₁(N)`-datum over a `K`-scheme together with a
full level-`n` structure" is representable by a scheme.  The citations are
those quoted on `exists_gamma1RigidifiedModuli` below — (4.7.2) with
(4.7.1) behind it for `[Γ(n)]`, (5.1.1) for `[Γ₁(N)]`, combined by
(6.6.2) — MINUS the affineness parenthesis of (8.1.1), which is the next
leaf.  The `∃!` of `universal` is what "representable" means.

## Faithfulness

Verbatim the analysis on `exists_gamma1RigidifiedModuli`, whose
hypotheses these are: `hn` and `hcharn` are load-bearing for TRUTH (at
`n ≤ 2` the rigidified problem still has `-1`; at `char K ∣ n` the group
scheme `E[n]` is not étale and `AbelianFullLevelStructure n dM.ab` is
unsatisfiable over a nonempty base), `hcharN` is what makes `[Γ₁(N)]`
étale rather than merely finite flat, and `_hN` is not load-bearing and is
carried only to match the consumer. -/
theorem exists_gamma1RigidifiedModuliScheme (N : ℕ) (_hN : 4 ≤ N) (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hcharN : ¬ ringChar K ∣ N) (hcharn : ¬ ringChar K ∣ n) :
    Nonempty (Gamma1RigidifiedModuliScheme N n (Spec (CommRingCat.of K))) :=
  sorry

/-- **Katz–Mazur affineness: the rigidified `Γ₁` moduli scheme is affine**
(sorry leaf, cut 2026-07-30 out of `exists_gamma1RigidifiedModuli` below)
— the second citation half, the parenthesis of (8.1.1) and nothing else.

## What the prover of this node owes

The clause of (8.1.1) that reads, of `𝔐(𝒫, 𝒮)` with `𝒮 = [Γ(n)]`,
`𝒫 = [Γ₁(N)]` and `n ≥ 3` invertible on the base:

> It "exists" because `𝔐(𝒫, 𝒮)` is itself affine.

Concretely: `𝔐(𝒮) = Y(n)_K` is affine by (4.7.2), `[Γ₁(N)]` is finite
over `(Ell)` by (5.1.1), so `𝔐(𝒫, 𝒮) ⟶ 𝔐(𝒮)` is finite hence affine by
(6.6.2), and a scheme affine over an affine scheme is affine.  That last
step is NOT a citation and is available in the pin, so what is genuinely
cited is only "`𝔐(𝒮)` is affine" and "`𝔐(𝒫, 𝒮) ⟶ 𝔐(𝒮)` is finite".

## Why the `∀` is legitimate, and not the junk-witness trap

`Gamma1RigidifiedModuliScheme.universal` is a **fine** moduli property, so
any two inhabitants are related by a unique isomorphism (apply each one's
`universal` to the other's universal family, then to its own to see the
composites are identities).  `IsAffine` is invariant under isomorphism of
schemes.  So "the Katz–Mazur `𝔐(𝒫, 𝒮)` is affine" and "every inhabitant
of `Gamma1RigidifiedModuliScheme N n (Spec K)` has affine `M`" are the same
statement, exactly as on the `Γ₀` side. -/
theorem isAffine_of_gamma1RigidifiedModuliScheme (N : ℕ) (_hN : 4 ≤ N) (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hcharN : ¬ ringChar K ∣ N) (hcharn : ¬ ringChar K ∣ n)
    (R : Gamma1RigidifiedModuliScheme N n (Spec (CommRingCat.of K))) : IsAffine R.M :=
  sorry

/-- **From a fine moduli scheme with a chosen affine presentation to
`Gamma1RigidifiedModuli`** (PROVEN 2026-07-30) — the pure FORMALISATION
third of `exists_gamma1RigidifiedModuli`, with **no Katz–Mazur citation
left in it**, and the reason the two citation leaves above may forget
about affine presentations entirely.

It is stated for a chosen isomorphism `φ` rather than for the bare
`IsAffine` so that the ring `A` is a plain `Type` and no `CommRingCat`
carrier juggling enters the transport itself;
`nonempty_gamma1RigidifiedModuli_of_isAffine` below specialises it.

## How it is proven

`dM' := Gamma1BaseChange.datumBC φ.hom R.dM` is the datum on `Spec A`,
with `dbc` its base-change relation to `R.dM`; the level structure is
`exists_abelianFullLevelStructure_baseChange dbc R.lvlM`, already PROVEN
and already PINNED, which is where this is shorter than the `Γ₀`
transport (see the section comment above).

The universal property is the substantial half.  Given `T, d, L` it takes
the unique `m₀ : T ⟶ R.M` from `R.universal` and returns `m₀ ≫ φ.inv`; the
base-change datum over `Spec A` is obtained by *cancelling* `dbc` out of
`bc₀`, with `k := dbc.isPullback.lift (d.f ≫ m₀ ≫ φ.inv) bc₀.map _` and
cartesianness by `IsPullback.of_bot`.  Uniqueness runs the other way,
composing the given `bc₁` with `dbc` through `IsBaseChangeOfGamma1.comp`
and feeding the result to `R.universal`'s uniqueness clause.

**The one real obstacle, and how it is dealt with**, inherited verbatim
from the `Γ₀` transport: the base points do not match definitionally.
`RelPoint.along dbc.map` sends a point over `g ≫ (m₀ ≫ φ.inv)` to one over
`(g ≫ m₀ ≫ φ.inv) ≫ φ.hom`, while `RelPoint.along bc₀.map` lands over
`g ≫ m₀`; the two agree propositionally and the relative points therefore
inhabit *different types*, so no `rw` bridges them.  Every step is instead
stated on the **underlying morphisms**, where the base index does not
appear, and the residual identifications are absorbed by
`AbelianSchemeStruct.zero_val_congr` and `add_val_congr`. -/
theorem nonempty_gamma1RigidifiedModuli_of_iso {N n : ℕ} {S : Scheme.{0}}
    (R : Gamma1RigidifiedModuliScheme N n S) {A : Type} [CommRing A]
    (φ : Spec (CommRingCat.of A) ≅ R.M) :
    Nonempty (Gamma1RigidifiedModuli N n S) := by
  classical
  -- the transported datum, and its base-change relation to the universal one
  let dM' : Gamma1Datum N (Spec (CommRingCat.of A)) := Gamma1BaseChange.datumBC φ.hom R.dM
  let dbc : IsBaseChangeOfGamma1 φ.hom dM' R.dM := Gamma1BaseChange.isBaseChangeBC φ.hom R.dM
  -- the transported level structure, PINNED — this is the whole of what the `Γ₀`
  -- transport has to build by hand
  obtain ⟨lvl, hP', hQ'⟩ := exists_abelianFullLevelStructure_baseChange dbc R.lvlM
  refine ⟨{ A := A, strM := φ.hom ≫ R.strM, dM := dM', lvlM := lvl, universal := ?_ }⟩
  intro T g d L
  obtain ⟨m₀, ⟨hstr₀, bc₀, e₁, e₂⟩, huniq⟩ := R.universal g d L
  have hmφ : (m₀ ≫ φ.inv) ≫ φ.hom = m₀ := by simp
  refine ⟨m₀ ≫ φ.inv, ⟨?_, ?_⟩, ?_⟩
  · -- the structure morphism is respected
    rw [Category.assoc, ← Category.assoc φ.inv φ.hom R.strM, φ.inv_hom_id, Category.id_comp]
    exact hstr₀
  · -- existence: cancel `dbc` out of `bc₀`
    have hw : (d.f ≫ m₀ ≫ φ.inv) ≫ φ.hom = bc₀.map ≫ R.dM.f := by
      rw [Category.assoc, hmφ]; exact bc₀.isPullback.w
    let k : d.E ⟶ dM'.E := dbc.isPullback.lift (d.f ≫ m₀ ≫ φ.inv) bc₀.map hw
    have hk₁ : k ≫ dM'.f = d.f ≫ m₀ ≫ φ.inv := dbc.isPullback.lift_fst _ _ _
    have hk₂ : k ≫ dbc.map = bc₀.map := dbc.isPullback.lift_snd _ _ _
    have hsq : IsPullback d.f k (m₀ ≫ φ.inv) dM'.f := by
      refine IsPullback.of_bot ?_ hk₁.symm dbc.isPullback
      rw [hk₂, hmφ]; exact bc₀.isPullback
    let bc : IsBaseChangeOfGamma1 (m₀ ≫ φ.inv) d dM' :=
      { map := k
        isPullback := hsq
        map_zero := by
          intro U u
          refine dbc.along_injective ?_
          have z₁ : (d.ab.zero u).1 ≫ bc₀.map = (R.dM.ab.zero (u ≫ m₀)).1 :=
            congrArg Subtype.val (bc₀.map_zero u)
          have z₂ : (dM'.ab.zero (u ≫ m₀ ≫ φ.inv)).1 ≫ dbc.map
              = (R.dM.ab.zero ((u ≫ m₀ ≫ φ.inv) ≫ φ.hom)).1 :=
            congrArg Subtype.val (dbc.map_zero (u ≫ m₀ ≫ φ.inv))
          show ((d.ab.zero u).1 ≫ k) ≫ dbc.map
              = (dM'.ab.zero (u ≫ m₀ ≫ φ.inv)).1 ≫ dbc.map
          rw [Category.assoc, hk₂, z₁, z₂]
          exact AbelianSchemeStruct.zero_val_congr R.dM.ab
            (by rw [Category.assoc, hmφ])
        map_add := by
          intro U u x y
          refine dbc.along_injective ?_
          have hx : x.1 ≫ bc₀.map = (x.1 ≫ k) ≫ dbc.map := by rw [Category.assoc, hk₂]
          have hy : y.1 ≫ bc₀.map = (y.1 ≫ k) ≫ dbc.map := by rw [Category.assoc, hk₂]
          have z₁ : (d.ab.add x y).1 ≫ bc₀.map
              = (R.dM.ab.add (RelPoint.along bc₀.map bc₀.isPullback.w x)
                  (RelPoint.along bc₀.map bc₀.isPullback.w y)).1 :=
            congrArg Subtype.val (bc₀.map_add x y)
          have z₂ : (dM'.ab.add (RelPoint.along k hsq.w x) (RelPoint.along k hsq.w y)).1
                ≫ dbc.map
              = (R.dM.ab.add
                  (RelPoint.along dbc.map dbc.isPullback.w (RelPoint.along k hsq.w x))
                  (RelPoint.along dbc.map dbc.isPullback.w (RelPoint.along k hsq.w y))).1 :=
            congrArg Subtype.val (dbc.map_add (RelPoint.along k hsq.w x)
              (RelPoint.along k hsq.w y))
          show ((d.ab.add x y).1 ≫ k) ≫ dbc.map
              = (dM'.ab.add (RelPoint.along k hsq.w x) (RelPoint.along k hsq.w y)).1 ≫ dbc.map
          rw [Category.assoc, hk₂, z₁, z₂]
          exact AbelianSchemeStruct.add_val_congr R.dM.ab (by rw [Category.assoc, hmφ]) _ _ _ _
            hx hy
        map_sec := by
          refine dbc.isPullback.hom_ext ?_ ?_
          · show (d.pt.sec ≫ k) ≫ dM'.f = ((m₀ ≫ φ.inv) ≫ dM'.pt.sec) ≫ dM'.f
            rw [Category.assoc, hk₁, ← Category.assoc, d.pt.sec_comp, Category.id_comp,
              Category.assoc, dM'.pt.sec_comp, Category.comp_id]
          · show (d.pt.sec ≫ k) ≫ dbc.map = ((m₀ ≫ φ.inv) ≫ dM'.pt.sec) ≫ dbc.map
            rw [Category.assoc, hk₂, bc₀.map_sec, Category.assoc, dbc.map_sec,
              ← Category.assoc, hmφ] }
    refine ⟨bc, ?_, ?_⟩
    · refine dbc.isPullback.hom_ext ?_ ?_
      · show (L.P.1 ≫ k) ≫ dM'.f = ((m₀ ≫ φ.inv) ≫ lvl.P.1) ≫ dM'.f
        rw [Category.assoc, hk₁, ← Category.assoc, L.P.2, Category.id_comp,
          Category.assoc, lvl.P.2, Category.comp_id]
      · show (L.P.1 ≫ k) ≫ dbc.map = ((m₀ ≫ φ.inv) ≫ lvl.P.1) ≫ dbc.map
        rw [Category.assoc, hk₂, e₁, Category.assoc, hP', ← Category.assoc, hmφ]
    · refine dbc.isPullback.hom_ext ?_ ?_
      · show (L.Q.1 ≫ k) ≫ dM'.f = ((m₀ ≫ φ.inv) ≫ lvl.Q.1) ≫ dM'.f
        rw [Category.assoc, hk₁, ← Category.assoc, L.Q.2, Category.id_comp,
          Category.assoc, lvl.Q.2, Category.comp_id]
      · show (L.Q.1 ≫ k) ≫ dbc.map = ((m₀ ≫ φ.inv) ≫ lvl.Q.1) ≫ dbc.map
        rw [Category.assoc, hk₂, e₂, Category.assoc, hQ', ← Category.assoc, hmφ]
  · -- uniqueness: compose with `dbc` and use uniqueness upstairs
    rintro m₁ ⟨hstr₁, bc₁, f₁, f₂⟩
    have := huniq (m₁ ≫ φ.hom) ⟨?_, bc₁.comp dbc, ?_, ?_⟩
    · rw [← this, Category.assoc, φ.hom_inv_id, Category.comp_id]
    · rw [Category.assoc]; exact hstr₁
    · show L.P.1 ≫ bc₁.map ≫ dbc.map = (m₁ ≫ φ.hom) ≫ R.lvlM.P.1
      rw [← Category.assoc, f₁, Category.assoc, hP', ← Category.assoc]
    · show L.Q.1 ≫ bc₁.map ≫ dbc.map = (m₁ ≫ φ.hom) ≫ R.lvlM.Q.1
      rw [← Category.assoc, f₂, Category.assoc, hQ', ← Category.assoc]

/-- **From an affine fine moduli scheme to `Gamma1RigidifiedModuli`**
(PROVEN 2026-07-30) — `nonempty_gamma1RigidifiedModuli_of_iso` at the
isomorphism `Scheme.isoSpec.symm`, with the coordinate ring taken to be
the carrier of `Γ(R.M, ⊤)`.  Splitting the two keeps the
`CommRingCat`-carrier step (`A : Type` versus `A : CommRingCat`) out of
the transport proof, where it would have interacted with the base-point
transports for no reason.

## Faithfulness

No hypothesis is decorative: `hR` is what supplies the isomorphism, and
without it there is no ring `A` at all.  Neither `N` nor `n` is
constrained, and neither needs to be — the statement holds for every `N`
and `n` for which an inhabitant of `Gamma1RigidifiedModuliScheme` exists,
which is the honest generality; the arithmetic hypotheses live on the two
citation leaves, where they are load-bearing. -/
theorem nonempty_gamma1RigidifiedModuli_of_isAffine {N n : ℕ} {S : Scheme.{0}}
    (R : Gamma1RigidifiedModuliScheme N n S) (hR : IsAffine R.M) :
    Nonempty (Gamma1RigidifiedModuli N n S) :=
  letI := hR
  nonempty_gamma1RigidifiedModuli_of_iso R (A := (Γ(R.M, ⊤) : CommRingCat).carrier)
    R.M.isoSpec.symm

/-- **The rigidified moduli scheme of `[Γ₁(N)], [Γ(n)]` over a field in
which `N` and `n` are invertible exists, and is AFFINE** (**ASSEMBLED
2026-07-30** over the three named nodes above; opened as a single sorry
leaf 2026-07-28) — Katz–Mazur, and NOTHING else.  This is the one
citation half of `exists_gamma1Rigidification`.

The citations below are unchanged and are now split between
`exists_gamma1RigidifiedModuliScheme` (4.7.1/4.7.2, 5.1.1, 6.6.2) and
`isAffine_of_gamma1RigidifiedModuliScheme` (the parenthesis of 8.1.1);
the third node, `nonempty_gamma1RigidifiedModuli_of_isAffine`, carries no
citation at all.  See the section comment above for the accounting.

## The citations, quoted so nobody has to re-derive which says what

* **(4.7.1)** "Any relatively representable moduli problem `𝒫` which is
  affine and etale over `(Ell)`, and rigid, is representable by a smooth
  affine curve over `ℤ`."
* **(4.7.2)** "For `N ≥ 3`, the naive level `N` moduli problem of 4.6 is
  representable, by a smooth affine curve `Y(N)` over `ℤ[1/N]`."  Applied
  at `n`, this represents `[Γ(n)]` by an affine `Y(n)`, and over `K` with
  `char K ∤ n` the base change `Y(n)_K` is available.
* **(5.1.1, First Main Theorem)** "Each of the four moduli problems
  `[Γ(N)]`, `[Γ₁(N)]`, `[bal.Γ₁(N)]`, and `[Γ₀(N)]` is relatively
  representable over `(Ell)`.  Each is finite and flat over `(Ell)` of
  constant rank `≥ 1`… Each tensored with `ℤ[1/N]` is finite etale over
  `(Ell/ℤ[1/N])`."  This is the `[Γ₁(N)]` input, and it is the ONE place
  the `Γ₁` citation differs from the `Γ₀` one (which uses 6.6.1/6.6.2).
* **(6.6.2)**, in the form that combines them: a representable moduli
  problem `𝒮` étale over `(Ell)` and a relatively representable `𝒫` give
  `M(𝒫, 𝒮)` finite and flat over `M(𝒮)`.  Take `𝒮 = [Γ(n)]`, étale over
  `(Ell/K)` by the last sentence of 5.1.1, and `𝒫 = [Γ₁(N)]`.
* **(8.1.1)** "…It 'exists' because `M(𝒫, 𝒮)` is itself affine."  The
  emphasised clause is the affineness, and `M(𝒫, 𝒮) ⟶ M(𝒮) = Y(n)_K` is
  finite over an affine scheme, hence affine.

## What it does NOT owe

The deck group, the invariants, the coarse space, descent, and the
level-`n` torsor.  Those are `exists_gamma1DeckAction`,
`exists_gamma1FullLevelStructure_cover` and the two PROVEN theorems
above.

## Faithfulness

`hcharn` is load-bearing for TRUTH: at `char K ∣ n` the group scheme
`E[n]` is not étale, `AbelianFullLevelStructure n dM.ab` is unsatisfiable
over a nonempty base, and no inhabitant with `A ≠ 0` exists.  `hn` is
load-bearing too: at `n ≤ 2` the rigidified problem still has the
automorphism `-1`, so it is not representable.  `hcharN` is what makes
`[Γ₁(N)]` étale rather than merely finite flat (5.1.1's last sentence).
`_hN` is **not** load-bearing — the rigidity that representability needs
is supplied by `[Γ(n)]` with `n ≥ 3`, not by `N ≥ 4` — and is carried only
to match the consumer's signature. -/
theorem exists_gamma1RigidifiedModuli (N : ℕ) (_hN : 4 ≤ N) (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hcharN : ¬ ringChar K ∣ N) (hcharn : ¬ ringChar K ∣ n) :
    Nonempty (Gamma1RigidifiedModuli N n (Spec (CommRingCat.of K))) :=
  (exists_gamma1RigidifiedModuliScheme N _hN n hn K hcharN hcharn).elim fun R =>
    nonempty_gamma1RigidifiedModuli_of_isAffine R
      (isAffine_of_gamma1RigidifiedModuliScheme N _hN n hn K hcharN hcharn R)

namespace AbelianFullLevelStructure

/-- **The matrix twist commutes with base change** (PROVEN 2026-07-29) —
transcription of `FullLevelStructure.twist_baseChange`.  No `n`-torsion
hypothesis is needed: this composes ONE twist with a base change, never
two twists with each other, which is the only place `ZMod.val`'s failure
to be multiplicative bites. -/
theorem twist_baseChange {N n : ℕ} (hn : 3 ≤ n) {T' T : Scheme.{u}} {p : T' ⟶ T}
    {d' : Gamma1Datum N T'} {d : Gamma1Datum N T} (bc : IsBaseChangeOfGamma1 p d' d)
    {L' : AbelianFullLevelStructure n d'.ab} {L : AbelianFullLevelStructure n d.ab}
    (hP : L'.P.1 ≫ bc.map = p ≫ L.P.1) (hQ : L'.Q.1 ≫ bc.map = p ≫ L.Q.1)
    (σ : GL (Fin 2) (ZMod n)) :
    (twist hn L' σ).P.1 ≫ bc.map = p ≫ (twist hn L σ).P.1 ∧
      (twist hn L' σ).Q.1 ≫ bc.map = p ≫ (twist hn L σ).Q.1 := by
  have hbP : bc.toRelPoint L'.P
      = RelPoint.pre (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p)) L.P :=
    Subtype.ext (by
      show L'.P.1 ≫ bc.map = (𝟙 T' ≫ p) ≫ L.P.1
      rw [hP, Category.id_comp])
  have hbQ : bc.toRelPoint L'.Q
      = RelPoint.pre (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p)) L.Q :=
    Subtype.ext (by
      show L'.Q.1 ≫ bc.map = (𝟙 T' ≫ p) ≫ L.Q.1
      rw [hQ, Category.id_comp])
  constructor
  · have h1 : bc.toRelPoint (twist hn L' σ).P
        = RelPoint.pre (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p)) (twist hn L σ).P := by
      show bc.toRelPoint (RelPoint.comb d'.ab (σ.val 0 0) (σ.val 0 1) L'.P L'.Q) = _
      rw [bc.toRelPoint_comb, hbP, hbQ,
        ← RelPoint.pre_comb d.ab (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p))
          (σ.val 0 0) (σ.val 0 1) L.P L.Q]
      rfl
    have h2 := congrArg Subtype.val h1
    simp only [Category.id_comp] at h2
    exact h2
  · have h1 : bc.toRelPoint (twist hn L' σ).Q
        = RelPoint.pre (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p)) (twist hn L σ).Q := by
      show bc.toRelPoint (RelPoint.comb d'.ab (σ.val 1 0) (σ.val 1 1) L'.P L'.Q) = _
      rw [bc.toRelPoint_comb, hbP, hbQ,
        ← RelPoint.pre_comb d.ab (𝟙 T' ≫ p) (Category.comp_id (𝟙 T' ≫ p))
          (σ.val 1 0) (σ.val 1 1) L.P L.Q]
      rfl
    have h2 := congrArg Subtype.val h1
    simp only [Category.id_comp] at h2
    exact h2

end AbelianFullLevelStructure

/-! ### The comparison locus of two full level structures

**Transcription of `X0.lean`'s `combPiece` block (2026-07-30), with
`Gamma0Datum` replaced by a BARE `AbelianSchemeStruct`** — which is
strictly more general than the original, since `AbelianFullLevelStructure`
is already stated over an `AbelianSchemeStruct` rather than over a datum,
and would serve the `Γ₀` side unchanged once `X0.lean`'s
`FullLevelStructure` is generalised the same way.

It exists to cut `exists_openCover_twist_of_abelianFullLevelStructure`
below along exactly the line its own docstring drew: *"Only step 2 is
geometry."*  Steps 1, 3, 4 and 5 are now written and green here, and step
2 is the single named leaf
`isOpenImmersion_equalizer_of_abelianFullLevelStructure`.

**THE ACCOUNTING, STATED HONESTLY: this is 1 → 1 OPEN LEAF, not 1 → 0.**
What it buys is that the residue is now a single self-contained assertion
about one abelian scheme — *the equalizer of two `n`-torsion sections is
open* — with all the moduli-theoretic and matrix bookkeeping discharged,
and that it is the SAME assertion `X0.lean` already carries as
`isOpenImmersion_equalizer_of_nsmul_eq_zero`, modulo the hypothesis that
supplies invertibility of `n`.  The `Γ₀` side took this identical trade on
2026-07-28.
-/

section CombPiece

variable {n : ℕ} {Z E : Scheme.{0}} {f : E ⟶ Z} {abs : AbelianSchemeStruct f}

/-- The locus in `Z` where BOTH `L₂.P = M₀ · L₁` and `L₂.Q = M₁ · L₁`
hold: the fibre product over `Z` of the two equalizers.  Transcription of
`X0.lean`'s `combPiece`. -/
noncomputable def abelianCombPiece (L₁ L₂ : AbelianFullLevelStructure n abs)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n)) : Scheme.{0} :=
  Limits.pullback
    (Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1)
    (Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1)

/-- The inclusion of the piece into `Z`. -/
noncomputable def abelianCombPieceι (L₁ L₂ : AbelianFullLevelStructure n abs)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n)) : abelianCombPiece L₁ L₂ M ⟶ Z :=
  Limits.pullback.fst
      (Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1)
      (Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1) ≫
    Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1

/-- On the piece, `L₂.P` IS the first row of `M` applied to `L₁` (PROVEN):
the piece factors through the first equalizer by `pullback.fst`. -/
theorem abelianCombPieceι_comp_P (L₁ L₂ : AbelianFullLevelStructure n abs)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n)) :
    abelianCombPieceι L₁ L₂ M ≫ L₂.P.1
      = abelianCombPieceι L₁ L₂ M ≫ (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1 :=
  comp_eq_of_factors_equalizer _ _
    (Limits.pullback.fst
      (Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1)
      (Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1)) rfl

/-- On the piece, `L₂.Q` IS the second row of `M` applied to `L₁` (PROVEN):
the piece factors through the second equalizer by `pullback.snd`, which is
`Limits.pullback.condition`. -/
theorem abelianCombPieceι_comp_Q (L₁ L₂ : AbelianFullLevelStructure n abs)
    (M : Matrix (Fin 2) (Fin 2) (ZMod n)) :
    abelianCombPieceι L₁ L₂ M ≫ L₂.Q.1
      = abelianCombPieceι L₁ L₂ M ≫ (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1 :=
  comp_eq_of_factors_equalizer _ _
    (Limits.pullback.snd
      (Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1)
      (Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1))
    Limits.pullback.condition.symm

end CombPiece

/-- **THE ONE OPEN LEAF under
`exists_openCover_twist_of_abelianFullLevelStructure`** (sorry leaf, cut
2026-07-30): *the equalizer of two `n`-torsion sections of an elliptic
scheme over an ARBITRARY base carrying a full level-`n` structure is OPEN
in the base.*

This is `X0.lean`'s `isOpenImmersion_equalizer_of_nsmul_eq_zero` with its
`g : Z ⟶ SpecQ` replaced by `L`, and it is the ONLY thing that changes
between the two.  Everything that leaf's docstring records as owed — the
five-step route through `E[n] := pullback (ab.mulByNat n) ab.zeroSection`,
`liesIn_torsionι_iff` as the model for the functor-of-points step,
`FormallyUnramified.isOpenImmersion_diagonal` for the diagonal, and
`section_eq_of_formallyUnramified` as the worked precedent in this
development — applies here verbatim and is not repeated.  Read it there.

## Why `L` in place of `g : Z ⟶ SpecQ`, and why the leaf is still TRUE

The `ℚ`-structure is consumed at exactly one point of that route: step 3,
where `n` invertible on `Z` makes `[n] : E ⟶ E` étale and hence `E[n] ⟶ Z`
unramified.  This leaf's consumer runs over an arbitrary base `S` — `Z` is
an arbitrary `Spec R.A`-scheme — so it cannot have a `g`, and it does not
need one: **`L` already pins `n` invertible on `Z`.**  The count, which is
the FALSITY AUDIT of the parent theorem below in full:

* let `z : Z` be any point and `t : Spec (κ(z)^alg) ⟶ Z` the geometric
  point over it.  `L.nsmul_P` and `L.nsmul_Q` make
  `(a, b) ↦ a·P + b·Q : Fin n × Fin n → RelPoint f t` land in the
  `n`-torsion, and `L.geom_basis` says every `n`-torsion point has EXACTLY
  ONE preimage.  So `#E_z[n](κ(z)^alg) = n²`.
* `hdim` makes that fibre an elliptic curve.  Over an algebraically closed
  field of characteristic `p`, writing `n = p^a·m` with `p ∤ m`, one has
  `E[n] ≅ E[p^a] × E[m]` with `E[m] ≅ (ℤ/m)²` and `E[p^a]` either `ℤ/p^a`
  or `0`.  So `#E[n] ∈ {m²·p^a, m²}`, and both are `< n² = m²·p^{2a}` as
  soon as `a ≥ 1`.
* Hence no point of `Z` has residue characteristic dividing `n`, i.e. `n`
  is a unit in every local ring of `Z`, i.e. `n ∈ Γ(Z, ⊤)ˣ` — which is
  exactly what `g` was supplying, and strictly weaker than it.

So `hdim` is **load-bearing for TRUTH here** in a way it is not in the
`Γ₀` leaf (where its own docstring correctly records it as optional,
because `g` supplies invertibility outright): without it the fibres need
not be elliptic curves and the count that recovers invertibility of `n`
collapses.  `L` is load-bearing for the same reason.

`hn` is load-bearing at `n = 0`, where the hypotheses `0 • x = 0` and
`0 • y = 0` are vacuous, `x` and `y` are arbitrary sections, and the
equalizer of two sections of an elliptic surface over `𝔸¹` is a point —
closed and not open.  Only `n ≠ 0` is used; `3 ≤ n` is inherited from the
parent.

**A prover may equally well close this by proving `n ∈ Γ(Z, ⊤)ˣ` from `L`
and `hdim` as a separate step and then running the `Γ₀` route** — that is
the intended decomposition if the count above is wanted as a named lemma.
It is deliberately NOT cut that way here, because doing so would make this
node 1 → 2 open leaves rather than 1 → 1.

## WHAT IS ALREADY IN CONE, and exactly where the remaining gap sits

Recorded 2026-07-30 while making the cut, because the `Γ₀` leaf's own route
list predates it and a prover reading only that list will re-derive this.
The route's step 3 — *`E[n] ⟶ Z` is formally unramified* — is **one base
change away from a PROVEN theorem**, not from nothing:

* `formallyUnramified_mulByNat` — no `AbelianSchemeStruct` namespace, it is
  applied as `formallyUnramified_mulByNat K ab n hn`
  (`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`, PROVEN 2026-07-27):
  `[n] : A ⟶ A` is `FormallyUnramified` whenever `(n : K) ≠ 0`.
* `E[n] := pullback (ab.mulByNat n) ab.zeroSection` has `pullback.snd` the
  base change of `[n]` along `ab.zeroSection : Z ⟶ E`, and
  `FormallyUnramified` is stable under base change, so `E[n] ⟶ Z` inherits
  it directly.

**The gap is that `formallyUnramified_mulByNat` is stated over a FIELD
base** — `fK : X ⟶ Spec (CommRingCat.of K)`, `[Field K]` — while `Z` here
is an arbitrary scheme.  Its field hypothesis enters in exactly two places
and both look like `IsUnit`, not like `Field`:

1. `eq_zero_of_nsmul_eq_zero_of_squareZero` inverts `(n : K)` and uses
   nothing else about `K` (`hz`, the three-line `calc` at the end);
2. `nonempty_module_infKernel_of_squareZero` — itself the open leaf under
   both — produces a `Module K` structure on the infinitesimal kernel.

So the natural generalisation is `[CommRing R]` with `IsUnit (n : R)` in
place of `[Field K]` with `(n : K) ≠ 0`, `FormallyUnramified` being
affine-local on the base.  **This is a route sketch and has NOT been
compiler-checked**; it is written down because it names the two exact
declarations to look at, which is a cheap check and a large saving if it
holds.  If it does hold, closing this leaf reduces to the count above, and
`X0.lean`'s `isOpenImmersion_equalizer_of_nsmul_eq_zero` closes with it. -/
theorem isOpenImmersion_equalizer_of_abelianFullLevelStructure (n : ℕ) (_hn : 3 ≤ n)
    {Z E : Scheme.{0}} {f : E ⟶ Z} (abs : AbelianSchemeStruct f)
    (_hdim : SmoothOfRelativeDimension 1 f) (_L : AbelianFullLevelStructure n abs)
    (x y : RelPoint f (𝟙 Z))
    (_hx : letI := abs.addCommGroup (𝟙 Z); n • x = 0)
    (_hy : letI := abs.addCommGroup (𝟙 Z); n • y = 0) :
    IsOpenImmersion (Limits.pullback.fst x.1 y.1) :=
  sorry

/-- **The piece is an OPEN subscheme of `Z`** (PROVEN from the leaf): each
of the two equalizers is open by
`isOpenImmersion_equalizer_of_abelianFullLevelStructure`, open immersions
are stable under base change, and they compose. -/
theorem isOpenImmersion_abelianCombPieceι {n : ℕ} (hn : 3 ≤ n) {Z E : Scheme.{0}} {f : E ⟶ Z}
    {abs : AbelianSchemeStruct f} (hdim : SmoothOfRelativeDimension 1 f)
    (L₁ L₂ : AbelianFullLevelStructure n abs) (M : Matrix (Fin 2) (Fin 2) (ZMod n)) :
    IsOpenImmersion (abelianCombPieceι L₁ L₂ M) := by
  haveI := isOpenImmersion_equalizer_of_abelianFullLevelStructure n hn abs hdim L₁
    L₂.P (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q) L₂.nsmul_P
    (nsmul_comb_eq_zero abs _ _ L₁.nsmul_P L₁.nsmul_Q)
  haveI := isOpenImmersion_equalizer_of_abelianFullLevelStructure n hn abs hdim L₁
    L₂.Q (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q) L₂.nsmul_Q
    (nsmul_comb_eq_zero abs _ _ L₁.nsmul_P L₁.nsmul_Q)
  show IsOpenImmersion (Limits.pullback.fst _ _ ≫
    Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1)
  infer_instance

/-- **Two full level structures on one abelian scheme differ Zariski-locally
by a constant MATRIX** (PROVEN 2026-07-30 over the leaf above) — the parent
statement with `GL₂(ℤ/n)` weakened to `M₂(ℤ/n)`, which is precisely the part
that does not need `L₂.geom_basis`.  Transcription of `X0.lean`'s
`exists_openCover_comb_of_fullLevelStructure`.

The cover is indexed by the `n⁴` matrices themselves, with the piece for
`M` the locus `abelianCombPiece L₁ L₂ M`.  Each piece is open
(`isOpenImmersion_abelianCombPieceι`, over the one leaf), and they COVER:
at a point `z` of `Z`, take the geometric point `Spec (κ(z)^alg) ⟶ Z`,
read `L₂.P` and `L₂.Q` in the basis `L₁` there (`L₁.geom_basis`, a field of
`AbelianFullLevelStructure`), and the resulting `Fin n`-coordinates
assemble into a matrix whose piece contains `z` — the lift being
`pullback.lift` applied twice, once for each equalizer.

Note where invertibility is NOT available: a piece may be EMPTY, and on an
empty piece the matrix is unconstrained.  That is why the `GL₂` form of the
statement is proven separately, by discharging the empty pieces through
initiality rather than by strengthening this one. -/
theorem exists_openCover_comb_of_abelianFullLevelStructure (n : ℕ) (hn : 3 ≤ n)
    {Z E : Scheme.{0}} {f : E ⟶ Z} (abs : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f) (L₁ L₂ : AbelianFullLevelStructure n abs) :
    ∃ 𝒰 : Scheme.OpenCover.{0} Z, ∀ i : 𝒰.I₀,
      ∃ M : Matrix (Fin 2) (Fin 2) (ZMod n),
        𝒰.f i ≫ L₂.P.1 = 𝒰.f i ≫ (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1 ∧
        𝒰.f i ≫ L₂.Q.1 = 𝒰.f i ≫ (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1 := by
  classical
  refine ⟨Scheme.Cover.mkOfCovers (Matrix (Fin 2) (Fin 2) (ZMod n))
    (fun M => abelianCombPiece L₁ L₂ M) (fun M => abelianCombPieceι L₁ L₂ M) ?_
    (fun M => isOpenImmersion_abelianCombPieceι hn hdim L₁ L₂ M),
    fun i => ⟨i, abelianCombPieceι_comp_P L₁ L₂ i, abelianCombPieceι_comp_Q L₁ L₂ i⟩⟩
  intro z
  letI := abs.addCommGroup (𝟙 Z)
  let Kz := AlgebraicClosure (Z.residueField z)
  let t : Spec (CommRingCat.of Kz) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Kz)) ≫
      Z.fromSpecResidueField z
  letI := abs.addCommGroup t
  have htP : n • RelPoint.pre t (Category.comp_id t) L₂.P = 0 :=
    RelPoint.nsmul_pre_eq_zero abs t (Category.comp_id t) L₂.nsmul_P
  have htQ : n • RelPoint.pre t (Category.comp_id t) L₂.Q = 0 :=
    RelPoint.nsmul_pre_eq_zero abs t (Category.comp_id t) L₂.nsmul_Q
  obtain ⟨a, ha, -⟩ := (L₁.geom_basis Kz t _).mp htP
  obtain ⟨b, hb, -⟩ := (L₁.geom_basis Kz t _).mp htQ
  refine ⟨![![((a.1 : ℕ) : ZMod n), ((a.2 : ℕ) : ZMod n)],
      ![((b.1 : ℕ) : ZMod n), ((b.2 : ℕ) : ZMod n)]], ?_⟩
  set M : Matrix (Fin 2) (Fin 2) (ZMod n) :=
    ![![((a.1 : ℕ) : ZMod n), ((a.2 : ℕ) : ZMod n)],
      ![((b.1 : ℕ) : ZMod n), ((b.2 : ℕ) : ZMod n)]] with hM
  have hM00 : (M 0 0).val = (a.1 : ℕ) := ZMod.val_cast_of_lt a.1.isLt
  have hM01 : (M 0 1).val = (a.2 : ℕ) := ZMod.val_cast_of_lt a.2.isLt
  have hM10 : (M 1 0).val = (b.1 : ℕ) := ZMod.val_cast_of_lt b.1.isLt
  have hM11 : (M 1 1).val = (b.2 : ℕ) := ZMod.val_cast_of_lt b.2.isLt
  have keyP : t ≫ L₂.P.1 = t ≫ (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1 := by
    refine congrArg Subtype.val (?_ : RelPoint.pre t (Category.comp_id t) L₂.P
      = RelPoint.pre t (Category.comp_id t) (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q))
    rw [RelPoint.pre_comb abs t (Category.comp_id t) (M 0 0) (M 0 1) L₁.P L₁.Q]
    show _ = (M 0 0).val • _ + (M 0 1).val • _
    rw [hM00, hM01]
    exact ha
  have keyQ : t ≫ L₂.Q.1 = t ≫ (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1 := by
    refine congrArg Subtype.val (?_ : RelPoint.pre t (Category.comp_id t) L₂.Q
      = RelPoint.pre t (Category.comp_id t) (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q))
    rw [RelPoint.pre_comb abs t (Category.comp_id t) (M 1 0) (M 1 1) L₁.P L₁.Q]
    show _ = (M 1 0).val • _ + (M 1 1).val • _
    rw [hM10, hM11]
    exact hb
  have hup : Limits.pullback.lift t t keyP ≫
      Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1 = t :=
    Limits.pullback.lift_fst _ _ _
  have huq : Limits.pullback.lift t t keyQ ≫
      Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1 = t :=
    Limits.pullback.lift_fst _ _ _
  have hcond : Limits.pullback.lift t t keyP ≫
      Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1
      = Limits.pullback.lift t t keyQ ≫
        Limits.pullback.fst L₂.Q.1 (RelPoint.comb abs (M 1 0) (M 1 1) L₁.P L₁.Q).1 := by
    rw [hup, huq]
  have hucomp : Limits.pullback.lift (Limits.pullback.lift t t keyP)
      (Limits.pullback.lift t t keyQ) hcond ≫ abelianCombPieceι L₁ L₂ M = t := by
    show Limits.pullback.lift (Limits.pullback.lift t t keyP)
        (Limits.pullback.lift t t keyQ) hcond ≫ Limits.pullback.fst _ _ ≫
      Limits.pullback.fst L₂.P.1 (RelPoint.comb abs (M 0 0) (M 0 1) L₁.P L₁.Q).1 = t
    rw [← Category.assoc, Limits.pullback.lift_fst, hup]
  refine ⟨Limits.pullback.lift (Limits.pullback.lift t t keyP)
    (Limits.pullback.lift t t keyQ) hcond (IsLocalRing.closedPoint Kz), ?_⟩
  have h2 : (Limits.pullback.lift (Limits.pullback.lift t t keyP)
        (Limits.pullback.lift t t keyQ) hcond ≫ abelianCombPieceι L₁ L₂ M)
        (IsLocalRing.closedPoint Kz)
      = t (IsLocalRing.closedPoint Kz) := by rw [hucomp]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h2
  exact h2.trans (Scheme.fromSpecResidueField_apply z _)

/-- **Two full level-`n` structures on ONE `Γ₁(N)`-datum differ
Zariski-locally by a CONSTANT matrix** (**PROVEN 2026-07-30** over
`exists_openCover_comb_of_abelianFullLevelStructure` and the single
geometric leaf `isOpenImmersion_equalizer_of_abelianFullLevelStructure`;
opened as a bare sorry leaf 2026-07-29) — the whole geometric content
under `exists_gamma1DeckAction`, and the only thing that node still owes.

This is the `Γ₁`, arbitrary-base analogue of `X0.lean`'s
`exists_openCover_twist_of_fullLevelStructure`, which is **PROVEN**.  The
route transcribes; its five steps are written out in the section comment
before that theorem and are not repeated here.  What is worth repeating
is the shape of the answer: the locus in `Z` where `L₂` equals a fixed
`M ∈ M₂(ℤ/n)`-combination of `L₁` is a fibre product of two equalizers,
each such locus is OPEN, the `n⁴` of them COVER `Z` (read `L₂` in the
basis `L₁` at a geometric point, which is free from `L₁.geom_basis`), on a
NONEMPTY piece the matrix is invertible because `L₂.geom_basis` says two
bases of `(ℤ/n)²` differ by a unit, and an EMPTY piece is initial so
`σ = 1` serves.  Only step 2 is geometry.

**All of that is now written** (2026-07-30), in the `CombPiece` section and
the two theorems above; step 2 alone survives, as
`isOpenImmersion_equalizer_of_abelianFullLevelStructure`.  The count in the
FALSITY AUDIT below is what that leaf carries `L` for instead of a
`ℚ`-structure, so it is reproduced in that leaf's docstring as well — it
justifies both statements and is deliberately written out twice rather
than cross-referenced, since either could be read alone.

## FAITHFULNESS: why there is NO `g : Z ⟶ SpecQ`, and why that is still TRUE

`exists_openCover_twist_of_fullLevelStructure` carries `g : Z ⟶ SpecQ`
and its docstring calls it load-bearing: over a base of residue
characteristic `p ∣ n` the kernel `E[n]` is not étale, the comparison is
not locally constant, and the statement fails.  **This leaf cannot inherit
that hypothesis** — its consumer `exists_openCover_gamma1DeckTranslation`
runs over an arbitrary `S`, with `Z` an arbitrary `Spec R.A`-scheme — and
it does not need it, because `L₁` ALREADY pins `n` invertible on `Z`:

* let `z : Z` be any point and `t : Spec (κ(z)^alg) ⟶ Z` the geometric
  point over it.  `L₁.nsmul_P` and `L₁.nsmul_Q` make
  `(a, b) ↦ a·P + b·Q : Fin n × Fin n → RelPoint d.f t` land in the
  `n`-torsion, and `L₁.geom_basis` says every `n`-torsion point has
  EXACTLY ONE preimage.  So the geometric fibre satisfies
  `#E_z[n](κ(z)^alg) = n²`.
* `d.relativeDimensionOne` makes that fibre an elliptic curve.  Over an
  algebraically closed field of characteristic `p`, writing `n = p^a·m`
  with `p ∤ m`, one has `E[n] ≅ E[p^a] × E[m]` with `E[m] ≅ (ℤ/m)²` and
  `E[p^a]` either `ℤ/p^a` or `0`.  So `#E[n] ∈ {m²·p^a, m²}`, and both are
  `< n² = m²·p^{2a}` as soon as `a ≥ 1`.
* Hence no point of `Z` has residue characteristic dividing `n`, i.e.
  `n ∉ 𝔪_z` for every `z`, i.e. `n` is a unit in every local ring of `Z`,
  i.e. `n ∈ Γ(Z, ⊤)ˣ` — which is exactly what `g : Z ⟶ SpecQ` was
  supplying, and strictly weaker than it.

`d.relativeDimensionOne` is therefore load-bearing for TRUTH and is the
reason this leaf is stated over a `Gamma1Datum` rather than over a bare
`AbelianSchemeStruct`: without it the fibres need not be elliptic curves
and the counting argument that recovers invertibility of `n` collapses.
`hn` is load-bearing at `n = 0` exactly as on
`AbelianFullLevelStructure` (there `Fin 0` is empty while `0 • x = 0`
always), and is used here only through `twist`.

**Reported, not edited** (`X0.lean` has other concurrent owners): the same
argument shows that `exists_openCover_twist_of_fullLevelStructure`'s
`g : Z ⟶ SpecQ` is *not* load-bearing for the TRUTH of that statement
either — `L₁` pins `n` invertible there by the identical count — so its
faithfulness paragraph overstates the case.  It remains load-bearing for
the *route*, since step 2 is proved from a `ℚ`-scheme hypothesis.

## Non-vacuity, in both directions

`𝒰` is an open COVER, so its pieces are jointly surjective and the
equations really do determine `L₂` from `L₁` and the locally constant
`σ`.  The one-piece cover `𝟙 Z` is permitted and would say
`L₂ = twist hn L₁ σ` globally — the false statement the locality exists to
avoid, and the trap `X0.lean` records.  Conversely the conclusion is not
satisfiable by junk: `σ` is quantified INSIDE the cover, so a witness must
produce an actual matrix on each piece. -/
theorem exists_openCover_twist_of_abelianFullLevelStructure (N n : ℕ) (hn : 3 ≤ n)
    {Z : Scheme.{0}} (d : Gamma1Datum N Z)
    (L₁ L₂ : AbelianFullLevelStructure n d.ab) :
    ∃ 𝒰 : Scheme.OpenCover.{0} Z, ∀ i : 𝒰.I₀, ∃ σ : gamma0DeckGroup n,
      𝒰.f i ≫ L₂.P.1 = 𝒰.f i ≫ (AbelianFullLevelStructure.twist hn L₁ σ).P.1 ∧
      𝒰.f i ≫ L₂.Q.1 = 𝒰.f i ≫ (AbelianFullLevelStructure.twist hn L₁ σ).Q.1 := by
  obtain ⟨𝒰, h𝒰⟩ := exists_openCover_comb_of_abelianFullLevelStructure n hn d.ab
    d.relativeDimensionOne L₁ L₂
  refine ⟨𝒰, fun i => ?_⟩
  obtain ⟨M, hMP, hMQ⟩ := h𝒰 i
  rcases isEmpty_or_nonempty ↥(𝒰.X i) with hemp | hne
  · haveI := hemp
    exact ⟨1, (isInitialOfIsEmpty (X := 𝒰.X i)).hom_ext _ _,
      (isInitialOfIsEmpty (X := 𝒰.X i)).hom_ext _ _⟩
  · obtain ⟨pt⟩ := hne
    let Kw := AlgebraicClosure ((𝒰.X i).residueField pt)
    let t : Spec (CommRingCat.of Kw) ⟶ Z :=
      (Spec.map (CommRingCat.ofHom (algebraMap ((𝒰.X i).residueField pt) Kw)) ≫
        (𝒰.X i).fromSpecResidueField pt) ≫ 𝒰.f i
    letI := d.ab.addCommGroup t
    have hfac : ∀ {x y : RelPoint d.f (𝟙 Z)}, 𝒰.f i ≫ x.1 = 𝒰.f i ≫ y.1 →
        RelPoint.pre t (Category.comp_id t) x = RelPoint.pre t (Category.comp_id t) y := by
      intro x y h
      refine Subtype.ext ?_
      show t ≫ x.1 = t ≫ y.1
      show ((Spec.map (CommRingCat.ofHom (algebraMap ((𝒰.X i).residueField pt) Kw)) ≫
        (𝒰.X i).fromSpecResidueField pt) ≫ 𝒰.f i) ≫ x.1 = _
      rw [Category.assoc, h, ← Category.assoc]
    have hP' : RelPoint.pre t (Category.comp_id t) L₂.P
        = (M 0 0).val • RelPoint.pre t (Category.comp_id t) L₁.P
          + (M 0 1).val • RelPoint.pre t (Category.comp_id t) L₁.Q := by
      rw [hfac hMP, RelPoint.pre_comb d.ab t (Category.comp_id t) (M 0 0) (M 0 1) L₁.P L₁.Q]
      rfl
    have hQ' : RelPoint.pre t (Category.comp_id t) L₂.Q
        = (M 1 0).val • RelPoint.pre t (Category.comp_id t) L₁.P
          + (M 1 1).val • RelPoint.pre t (Category.comp_id t) L₁.Q := by
      rw [hfac hMQ, RelPoint.pre_comb d.ab t (Category.comp_id t) (M 1 0) (M 1 1) L₁.P L₁.Q]
      rfl
    have hM : IsUnit M :=
      isUnit_of_geomBasis_comb hn
        (RelPoint.nsmul_pre_eq_zero d.ab t (Category.comp_id t) L₁.nsmul_P)
        (RelPoint.nsmul_pre_eq_zero d.ab t (Category.comp_id t) L₁.nsmul_Q)
        (L₁.geom_basis Kw t) (L₂.geom_basis Kw t) M hP' hQ'
    have hval : (hM.unit : Matrix (Fin 2) (Fin 2) (ZMod n)) = M := hM.unit_spec
    refine ⟨hM.unit, ?_, ?_⟩
    · show 𝒰.f i ≫ L₂.P.1 = 𝒰.f i ≫ (RelPoint.comb d.ab
        ((hM.unit : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 0)
        ((hM.unit : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 1) L₁.P L₁.Q).1
      rw [hval]; exact hMP
    · show 𝒰.f i ≫ L₂.Q.1 = 𝒰.f i ≫ (RelPoint.comb d.ab
        ((hM.unit : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 0)
        ((hM.unit : Matrix (Fin 2) (Fin 2) (ZMod n)) 1 1) L₁.P L₁.Q).1
      rw [hval]; exact hMQ

/-- **Two rigidifications of one datum OVER `S` differ Zariski-locally by
a deck transformation** (PROVEN 2026-07-29) — the `Γ₁` transcription of
`X0.lean`'s `exists_openCover_deckTranslation`, and the geometric half of
`exists_gamma1DeckAction`.

It hands back the comparison morphism `m` TOGETHER with the property that
pins it — that `m` classifies the `σ`-twist of `R.lvlM` over `S` — which
is what lets the consumer identify `m` with `mm σ` by the uniqueness half
of `R.universal`, and is why this is not the junk-witness trap.

**Two things are new against the `Γ₀` original, both from the general
base.**  The hypothesis `hab : a ≫ R.strM = b ≫ R.strM` is what lets the
two rigidifications be compared by `R.universal` at the single structure
morphism `𝒰.f i ≫ a ≫ R.strM` — over `SpecQ` it is automatic, and its
absence is exactly the released falsity recorded in
`exists_gamma1DeckAction`'s FALSITY AUDIT.  And `m` now carries
`m ≫ R.strM = R.strM`, the extra conjunct of
`Gamma1RigidifiedModuli.universal`, which is also what `strM_invariant` is
read off. -/
theorem exists_openCover_gamma1DeckTranslation (N n : ℕ) (hn : 3 ≤ n) {S : Scheme.{0}}
    (R : Gamma1RigidifiedModuli N n S) :
    letI := R.commRing_A
    ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of R.A)) (d₁ : Gamma1Datum N Z),
      a ≫ R.strM = b ≫ R.strM →
      IsBaseChangeOfGamma1 a d₁ R.dM → IsBaseChangeOfGamma1 b d₁ R.dM →
      ∃ 𝒰 : Scheme.OpenCover.{0} Z, ∀ i : 𝒰.I₀, ∃ (σ : gamma0DeckGroup n)
        (m : Spec (CommRingCat.of R.A) ⟶ Spec (CommRingCat.of R.A)),
        (m ≫ R.strM = R.strM ∧ ∃ bc : IsBaseChangeOfGamma1 m R.dM R.dM,
          (AbelianFullLevelStructure.twist hn R.lvlM σ).P.1 ≫ bc.map = m ≫ R.lvlM.P.1 ∧
          (AbelianFullLevelStructure.twist hn R.lvlM σ).Q.1 ≫ bc.map = m ≫ R.lvlM.Q.1) ∧
        𝒰.f i ≫ b = 𝒰.f i ≫ a ≫ m := by
  letI := R.commRing_A
  intro Z a b d₁ hab ha hb
  -- step 1: the two pulled-back level structures on the ONE datum `d₁`
  obtain ⟨La, haP, haQ⟩ := exists_abelianFullLevelStructure_baseChange ha R.lvlM
  obtain ⟨Lb, hbP, hbQ⟩ := exists_abelianFullLevelStructure_baseChange hb R.lvlM
  -- steps 2–3: the geometry, and the only open leaf under this node
  obtain ⟨𝒰, h𝒰⟩ :=
    exists_openCover_twist_of_abelianFullLevelStructure N n hn d₁ La Lb
  refine ⟨𝒰, fun i => ?_⟩
  obtain ⟨σ, hσP, hσQ⟩ := h𝒰 i
  -- the comparison morphism, pinned by `R.universal` at the `σ`-twist
  obtain ⟨m, ⟨hmstr, bcm, hmP, hmQ⟩, -⟩ :=
    R.universal R.strM R.dM (AbelianFullLevelStructure.twist hn R.lvlM σ)
  refine ⟨σ, m, ⟨hmstr, bcm, hmP, hmQ⟩, ?_⟩
  -- step 4: restrict the datum and `Lb` to the piece, and use UNIQUENESS
  obtain ⟨dU, ⟨bcU⟩⟩ := exists_gamma1Datum_baseChange (𝒰.f i) d₁
  obtain ⟨LU, hUP, hUQ⟩ := exists_abelianFullLevelStructure_baseChange bcU Lb
  obtain ⟨w, -, hwu⟩ := R.universal (𝒰.f i ≫ a ≫ R.strM) dU LU
  obtain ⟨htP, htQ⟩ := AbelianFullLevelStructure.twist_baseChange hn ha haP haQ σ
  have h1 : 𝒰.f i ≫ b = w := by
    refine hwu _ ⟨?_, bcU.comp hb, ?_, ?_⟩
    · rw [Category.assoc, ← hab]
    · show LU.P.1 ≫ bcU.map ≫ hb.map = (𝒰.f i ≫ b) ≫ R.lvlM.P.1
      rw [← Category.assoc, hUP, Category.assoc, hbP, Category.assoc]
    · show LU.Q.1 ≫ bcU.map ≫ hb.map = (𝒰.f i ≫ b) ≫ R.lvlM.Q.1
      rw [← Category.assoc, hUQ, Category.assoc, hbQ, Category.assoc]
  have h2 : (𝒰.f i ≫ a) ≫ m = w := by
    refine hwu _ ⟨?_, (bcU.comp ha).comp bcm, ?_, ?_⟩
    · rw [Category.assoc, hmstr, Category.assoc]
    · show LU.P.1 ≫ (bcU.map ≫ ha.map) ≫ bcm.map = ((𝒰.f i ≫ a) ≫ m) ≫ R.lvlM.P.1
      calc LU.P.1 ≫ (bcU.map ≫ ha.map) ≫ bcm.map
          = ((LU.P.1 ≫ bcU.map) ≫ ha.map) ≫ bcm.map := by simp only [Category.assoc]
        _ = ((𝒰.f i ≫ Lb.P.1) ≫ ha.map) ≫ bcm.map := by rw [hUP]
        _ = ((𝒰.f i ≫ (AbelianFullLevelStructure.twist hn La σ).P.1) ≫ ha.map) ≫ bcm.map := by
              rw [hσP]
        _ = (𝒰.f i ≫ (AbelianFullLevelStructure.twist hn La σ).P.1 ≫ ha.map) ≫ bcm.map := by
              simp only [Category.assoc]
        _ = (𝒰.f i ≫ a ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).P.1) ≫ bcm.map := by
              rw [htP]
        _ = (𝒰.f i ≫ a) ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).P.1 ≫ bcm.map := by
              simp only [Category.assoc]
        _ = (𝒰.f i ≫ a) ≫ m ≫ R.lvlM.P.1 := by rw [hmP]
        _ = ((𝒰.f i ≫ a) ≫ m) ≫ R.lvlM.P.1 := by simp only [Category.assoc]
    · show LU.Q.1 ≫ (bcU.map ≫ ha.map) ≫ bcm.map = ((𝒰.f i ≫ a) ≫ m) ≫ R.lvlM.Q.1
      calc LU.Q.1 ≫ (bcU.map ≫ ha.map) ≫ bcm.map
          = ((LU.Q.1 ≫ bcU.map) ≫ ha.map) ≫ bcm.map := by simp only [Category.assoc]
        _ = ((𝒰.f i ≫ Lb.Q.1) ≫ ha.map) ≫ bcm.map := by rw [hUQ]
        _ = ((𝒰.f i ≫ (AbelianFullLevelStructure.twist hn La σ).Q.1) ≫ ha.map) ≫ bcm.map := by
              rw [hσQ]
        _ = (𝒰.f i ≫ (AbelianFullLevelStructure.twist hn La σ).Q.1 ≫ ha.map) ≫ bcm.map := by
              simp only [Category.assoc]
        _ = (𝒰.f i ≫ a ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).Q.1) ≫ bcm.map := by
              rw [htQ]
        _ = (𝒰.f i ≫ a) ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).Q.1 ≫ bcm.map := by
              simp only [Category.assoc]
        _ = (𝒰.f i ≫ a) ≫ m ≫ R.lvlM.Q.1 := by rw [hmQ]
        _ = ((𝒰.f i ≫ a) ≫ m) ≫ R.lvlM.Q.1 := by simp only [Category.assoc]
  rw [h1, ← Category.assoc, h2]

/-- **The deck group acts on the rigidified coordinate ring, over the
base, equivariantly, and its quotient map coequalises rigidifications**
(opened 2026-07-28; REFUTED, RESTATED and **PROVEN** 2026-07-29) — the
formalisation half of `exists_gamma1Rigidification`.  **It carries no
citation**: everything it asserts is a consequence of `R.universal`, and
the Katz–Mazur input is `R` itself.

## STATUS 2026-07-29: PROVEN, over ONE named geometric leaf

The transcription described below was carried out.  Everything this node
owed is discharged: clause (a) `strM_invariant` from the `m ≫ strM = g`
conjunct of `R.universal` read at `g := R.strM`; clause (b)
`dM_equivariant` from `R.universal`'s witness at `σ⁻¹`; clause (c) the
coequalising clause from `exists_openCover_gamma1DeckTranslation`
(PROVEN above), `comp_eq_of_openCover_translation` and
`specInvariantsQuotient_toRingHom_comp`.

**What remains open under this node is exactly ONE leaf**:
`exists_openCover_twist_of_abelianFullLevelStructure`, above — two full
level-`n` structures on ONE `Γ₁(N)`-datum differ Zariski-locally by a
CONSTANT matrix.  It is the `Γ₁`, arbitrary-base analogue of `X0.lean`'s
`exists_openCover_twist_of_fullLevelStructure`, which is PROVEN, and its
docstring carries the faithfulness argument for dropping `g : Z ⟶ SpecQ`.

The twist API the transcription needed
(`AbelianFullLevelStructure.twistP` … `twist_mul`, plus
`exists_abelianFullLevelStructure_of_geomBasis`,
`exists_abelianFullLevelStructure_baseChange` and `twist_baseChange`) is
transcribed from `X0.lean` in the block above, under the COORDINATION
NOTE's protest: the right repair is still to generalise `X0.lean`'s
`FullLevelStructure` to a bare `AbelianSchemeStruct`, at which point that
block can be deleted.

## The transcription, as it was planned (kept for the record)

**CORRECTION 2026-07-28.**  The previous version of this paragraph said
that `X0.lean`'s `exists_deckAction_of_torsion` "proves the corresponding
`Γ₀` statement in full **except for the coequalising clause, which it
leaves as a sorried `have` inside the proof**".  That is **STALE and
false**.  `exists_deckAction_of_torsion` is sorry-free, coequalising
clause included: the `have hcoeq` inside it is fully proven, from
`exists_openCover_deckTranslation` (which was itself opened 2026-07-27
and PROVEN 2026-07-28) together with `comp_eq_of_openCover_translation`
and `specInvariantsQuotient_toRingHom_comp`.  There is no anonymous
`sorry` anywhere in it — the nearest `sorry` above it in `X0.lean` is
`exists_openCover_twist_of_fullLevelStructure`'s and the nearest below is
thousands of lines away.

**What that changes.**  The coequalising clause is NOT unattacked
territory: there is a complete, released `Γ₀` proof to transcribe, and
what is still open under the `Γ₀` node is the single NAMED leaf
`exists_openCover_twist_of_fullLevelStructure` — *two full level
structures on ONE datum differ Zariski-locally by a CONSTANT matrix*.  So
the honest shape of this leaf is: a long but mechanical transcription,
bottoming out in a `Γ₁` analogue of that one named leaf.  Whoever takes
it should read `exists_openCover_twist_of_fullLevelStructure`'s docstring
first — it records why the locality is Zariski rather than merely fppf,
and that the one thing this project lacks for it is the `n`-torsion
subgroup scheme as an OBJECT (the same object `exists_isomTorsor_of_geomPoint`
owes, and it should be built once for both).

**One `Γ₀ → Γ₁` mismatch to watch when transcribing it.**
`exists_openCover_twist_of_fullLevelStructure` carries `g : Z ⟶ SpecQ`.
This leaf is over an ARBITRARY base scheme `S` with no characteristic
hypothesis, so its `Γ₁` analogue cannot inherit that hypothesis.  The
invertibility of `n` is nonetheless available, and not by assumption:
`R.lvlM.geom_basis` says that at every geometric point of `Spec R.A` the
`n`-torsion is in bijection with `Fin n × Fin n`, i.e. has exactly `n²`
points, which is false at a residue characteristic dividing `n`.  So `R`
itself pins `n` invertible on `Spec R.A`, and everything in the
conclusion lives over `Spec R.A`.  **The leaf is faithful as stated**;
the pin is carried by the hypothesis rather than by the signature, which
is worth knowing before anyone "repairs" it by adding a characteristic
assumption on `S`.

The argument transcribes verbatim, because it touches the level structure
only through the twist API:

* for `σ : GL₂(ℤ/n)`, `FullLevelStructure.twist` twists `lvlM` by the
  matrix and `R.universal` classifies the twist by a UNIQUE endomorphism
  `mm σ` of `Spec A`;
* `mm 1 = 𝟙` and `mm (σ * τ) = mm τ ≫ mm σ` from `twist_one` /
  `twist_mul` and the uniqueness half, so `σ ↦ mm σ` is a monoid
  ANTIhomomorphism into endomorphisms, hence into automorphisms;
* the ring action by full faithfulness of `Spec` on affines
  (`Spec.preimage`, `Spec.map_preimage`, `Spec.map_injective`), as
  `σ ↦ Spec.preimage (mm σ⁻¹)`;
* `dM_equivariant` is then immediate with `d₁ := R.dM` and the base
  change `R.universal` produced at `σ⁻¹`.

**Two things are new on the `Γ₁` side.**  First, `strM_invariant`, which
`Gamma0GITPresentation` does not have because morphisms to `Spec ℚ` are
unique: here it is the `m ≫ strM = g` conjunct of `R.universal` read at
`g := R.strM`, so `mm σ ≫ R.strM = R.strM` for every `σ`, and
`Spec.map (ofHom (toRingHom σ)) = mm σ⁻¹`.  Second — and this is the only
real obstruction — the twist API is stated for `FullLevelStructure`, i.e.
for a `Gamma0Datum`.  **See the COORDINATION NOTE in the section comment
above**: generalising `FullLevelStructure` to a bare
`AbelianSchemeStruct` in `X0.lean` makes ~290 lines of already-proven
twist machinery apply here unchanged, and reduces this leaf to its third
clause.

## The coequalising clause is where the content is

Two rigidifications `a, b : Z ⟶ Spec A` of ONE datum `d₁` differ by a
section of the `GL₂(ℤ/n)`-torsor of full level structures, which lies in
`GL₂(ℤ/n)` only fppf-LOCALLY.  Because `R.universal` is a FINE moduli
property, the comparison is **locally constant**: a finite clopen
decomposition of `Z` on each piece of which the two classifying maps
differ by composition with a single global `Spec σ`, and
`Spec σ ≫ π = π` because `π` is `Spec` of the inclusion of the
invariants.  So `a ≫ π = b ≫ π` piecewise and hence globally.  **Use the
piecewise argument** — a search for a single global `σ` cannot succeed,
and that is the trap this leaf exists to record.

## Faithfulness: the three clauses must stay in ONE leaf

Clause (b) alone does not pin the action: `σ ↦ id` satisfies it with
`d₁ := R.dM`, and under that action `A^G = A`, `π = 𝟙`, and clause (c) is
false.  A leaf carrying only (a) and (b), consumed by a second leaf
quantifying over the resulting `MulSemiringAction`, would therefore be
the junk-witness trap.  Conversely `R` itself is pinned, because
`universal` is a fine moduli property — so quantifying over `R` is
safe.

## FALSITY AUDIT (2026-07-29): clause (c) was FALSE without `hab`

As released this leaf was **false**, and provably so: clause (c) had no
`a ≫ R.strM = b ≫ R.strM` hypothesis, and clauses (a)+(c) together imply
it.  Indeed with `S = Spec K` affine, clause (a) forces `R.strM` to
factor through `specInvariantsQuotient` (both schemes are affine and
`Spec` is fully faithful there, so `R.strM = Spec φ` and (a) says
`σ • ∘ φ = φ`, i.e. `φ` lands in `A^G`), whence
`a ≫ π = b ≫ π → a ≫ R.strM = b ≫ R.strM`.  The witness is written out
in full in the FALSITY AUDIT in the section comment before
`Gamma1Rigidification`: `N = 5`, `E/ℚ` with a rational point of exact
order `5`, `K = ℚ(E[3])`, `σ ∈ Gal(K/ℚ)` nontrivial, and the two
rigidifications of the ONE datum `(E_K, P_K)` obtained from `R.cover` at
`g := 𝟙` and at `g := Spec σ`; they differ over `S` precisely by `σ`,
which the old clause (c) forbids.  The same witness refutes the released
field `Gamma1Rigidification.coequalises`, and both are repaired the same
way.

`hab` is therefore load-bearing for TRUTH.  It is not load-bearing on
the `Γ₀` side, which is why `X0.lean`'s `exists_deckAction_of_torsion`
does not carry it: there `S = SpecQ` and `Subsingleton (Z ⟶ SpecQ)`
gives it for free.  It costs the consumer nothing —
`exists_descendClassifyGamma1` derives it at both of its uses from
`hcov`'s `p ≫ g = m ≫ strM` clause. -/
theorem exists_gamma1DeckAction (N n : ℕ) (hn : 3 ≤ n) {S : Scheme.{0}}
    (R : Gamma1RigidifiedModuli N n S) :
    letI := R.commRing_A
    ∃ act : MulSemiringAction (gamma0DeckGroup n) R.A,
      letI := act
      (∀ σ : gamma0DeckGroup n,
          Spec.map (CommRingCat.ofHom
            (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ)) ≫ R.strM = R.strM) ∧
      (∀ σ : gamma0DeckGroup n, ∃ d₁ : Gamma1Datum N (Spec (CommRingCat.of R.A)),
          Nonempty (IsBaseChangeOfGamma1 (𝟙 (Spec (CommRingCat.of R.A))) d₁ R.dM) ∧
          Nonempty (IsBaseChangeOfGamma1
            (Spec.map (CommRingCat.ofHom
              (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ))) d₁ R.dM)) ∧
      ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of R.A)) (d₁ : Gamma1Datum N Z),
        a ≫ R.strM = b ≫ R.strM →
        IsBaseChangeOfGamma1 a d₁ R.dM → IsBaseChangeOfGamma1 b d₁ R.dM →
        a ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A
          = b ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A := by
  classical
  letI := R.commRing_A
  haveI : NeZero n := ⟨by omega⟩
  -- the classifying map of the `σ`-twisted universal level structure
  have huniv : ∀ σ : gamma0DeckGroup n,
      ∃! m : Spec (CommRingCat.of R.A) ⟶ Spec (CommRingCat.of R.A),
        m ≫ R.strM = R.strM ∧
        ∃ bc : IsBaseChangeOfGamma1 m R.dM R.dM,
          (AbelianFullLevelStructure.twist hn R.lvlM σ).P.1 ≫ bc.map = m ≫ R.lvlM.P.1 ∧
          (AbelianFullLevelStructure.twist hn R.lvlM σ).Q.1 ≫ bc.map = m ≫ R.lvlM.Q.1 :=
    fun σ => R.universal R.strM R.dM (AbelianFullLevelStructure.twist hn R.lvlM σ)
  choose mm hmm hmmu using huniv
  have hmstr : ∀ σ : gamma0DeckGroup n, mm σ ≫ R.strM = R.strM := fun σ => (hmm σ).1
  choose bcm e1 e2 using fun σ : gamma0DeckGroup n => (hmm σ).2
  -- `σ ↦ mm σ` is an antihomomorphism into the automorphisms of `Spec A`
  have hone : mm 1 = 𝟙 (Spec (CommRingCat.of R.A)) := by
    refine (hmmu 1 _ ⟨Category.id_comp _, IsBaseChangeOfGamma1.refl R.dM, ?_, ?_⟩).symm <;>
      · rw [AbelianFullLevelStructure.twist_one]
        simp [IsBaseChangeOfGamma1.refl]
  have hmul : ∀ σ τ : gamma0DeckGroup n, mm (σ * τ) = mm τ ≫ mm σ := by
    intro σ τ
    have hTP : (bcm τ).toRelPoint ((AbelianFullLevelStructure.twist hn R.lvlM τ).P)
        = RelPoint.pre (mm τ) (by simp) R.lvlM.P := Subtype.ext (e1 τ)
    have hTQ : (bcm τ).toRelPoint ((AbelianFullLevelStructure.twist hn R.lvlM τ).Q)
        = RelPoint.pre (mm τ) (by simp) R.lvlM.Q := Subtype.ext (e2 τ)
    have hstepP : (AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).P.1 ≫ (bcm τ).map
        = mm τ ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).P.1 := by
      refine congrArg Subtype.val (?_ :
        (bcm τ).toRelPoint ((AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).P)
          = RelPoint.pre (mm τ) (by simp)
              ((AbelianFullLevelStructure.twist hn R.lvlM σ).P))
      rw [← AbelianFullLevelStructure.twist_mul hn R.lvlM σ τ]
      show (bcm τ).toRelPoint (RelPoint.comb R.dM.ab (σ.val 0 0) (σ.val 0 1)
          (AbelianFullLevelStructure.twist hn R.lvlM τ).P
          (AbelianFullLevelStructure.twist hn R.lvlM τ).Q)
        = RelPoint.pre (mm τ) (by simp)
            (RelPoint.comb R.dM.ab (σ.val 0 0) (σ.val 0 1) R.lvlM.P R.lvlM.Q)
      rw [(bcm τ).toRelPoint_comb, RelPoint.pre_comb, hTP, hTQ]
    have hstepQ : (AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).Q.1 ≫ (bcm τ).map
        = mm τ ≫ (AbelianFullLevelStructure.twist hn R.lvlM σ).Q.1 := by
      refine congrArg Subtype.val (?_ :
        (bcm τ).toRelPoint ((AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).Q)
          = RelPoint.pre (mm τ) (by simp)
              ((AbelianFullLevelStructure.twist hn R.lvlM σ).Q))
      rw [← AbelianFullLevelStructure.twist_mul hn R.lvlM σ τ]
      show (bcm τ).toRelPoint (RelPoint.comb R.dM.ab (σ.val 1 0) (σ.val 1 1)
          (AbelianFullLevelStructure.twist hn R.lvlM τ).P
          (AbelianFullLevelStructure.twist hn R.lvlM τ).Q)
        = RelPoint.pre (mm τ) (by simp)
            (RelPoint.comb R.dM.ab (σ.val 1 0) (σ.val 1 1) R.lvlM.P R.lvlM.Q)
      rw [(bcm τ).toRelPoint_comb, RelPoint.pre_comb, hTP, hTQ]
    refine (hmmu (σ * τ) (mm τ ≫ mm σ) ⟨?_, (bcm τ).comp (bcm σ), ?_, ?_⟩).symm
    · rw [Category.assoc, hmstr σ, hmstr τ]
    · show (AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).P.1 ≫ (bcm τ).map ≫ (bcm σ).map
          = (mm τ ≫ mm σ) ≫ R.lvlM.P.1
      rw [← Category.assoc, hstepP, Category.assoc, e1 σ, Category.assoc]
    · show (AbelianFullLevelStructure.twist hn R.lvlM (σ * τ)).Q.1 ≫ (bcm τ).map ≫ (bcm σ).map
          = (mm τ ≫ mm σ) ≫ R.lvlM.Q.1
      rw [← Category.assoc, hstepQ, Category.assoc, e2 σ, Category.assoc]
  -- transport to ring homomorphisms through full faithfulness of `Spec` on affines
  have hw : ∀ (σ τ : gamma0DeckGroup n) (x : R.A),
      (Spec.preimage (mm τ)).hom ((Spec.preimage (mm σ)).hom x)
        = (Spec.preimage (mm (σ * τ))).hom x := by
    intro σ τ x
    have h : Spec.preimage (mm (σ * τ)) = Spec.preimage (mm σ) ≫ Spec.preimage (mm τ) := by
      refine Spec.map_injective ?_
      rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hmul]
    rw [h]; rfl
  have hw1 : ∀ x : R.A, (Spec.preimage (mm (1 : gamma0DeckGroup n))).hom x = x := by
    intro x
    have h : Spec.preimage (mm (1 : gamma0DeckGroup n)) = 𝟙 (CommRingCat.of R.A) := by
      refine Spec.map_injective ?_
      rw [Spec.map_preimage, Spec.map_id, hone]
    rw [h]; rfl
  -- the deck action itself
  let ρ : gamma0DeckGroup n →* RingAut R.A :=
    { toFun := fun σ =>
        { toFun := (Spec.preimage (mm σ⁻¹)).hom
          invFun := (Spec.preimage (mm σ)).hom
          left_inv := fun x => by rw [hw σ⁻¹ σ x, inv_mul_cancel, hw1]
          right_inv := fun x => by rw [hw σ σ⁻¹ x, mul_inv_cancel, hw1]
          map_mul' := map_mul _
          map_add' := map_add _ }
      map_one' := by
        ext x
        show (Spec.preimage (mm (1 : gamma0DeckGroup n)⁻¹)).hom x = x
        rw [inv_one, hw1]
      map_mul' := fun σ τ => by
        ext x
        show (Spec.preimage (mm (σ * τ)⁻¹)).hom x
            = (Spec.preimage (mm σ⁻¹)).hom ((Spec.preimage (mm τ⁻¹)).hom x)
        rw [hw τ⁻¹ σ⁻¹ x, ← mul_inv_rev] }
  letI act : MulSemiringAction (gamma0DeckGroup n) R.A := MulSemiringAction.compHom R.A ρ
  have hmap : ∀ σ : gamma0DeckGroup n, Spec.map (CommRingCat.ofHom
      (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ)) = mm σ⁻¹ := by
    intro σ
    have h : CommRingCat.ofHom (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ)
        = Spec.preimage (mm σ⁻¹) := by
      ext x; rfl
    rw [h, Spec.map_preimage]
  -- **`strM_invariant`**, new on the `Γ₁` side: it is the `m ≫ strM = g`
  -- conjunct of `R.universal` read at `g := R.strM`, which `Gamma0GITPresentation`
  -- does not have because morphisms to `Spec ℚ` are unique
  have hstrinv : ∀ σ : gamma0DeckGroup n, Spec.map (CommRingCat.ofHom
      (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ)) ≫ R.strM = R.strM := by
    intro σ
    rw [hmap σ]
    exact hmstr σ⁻¹
  -- **the coequalising clause**: the geometry is
  -- `exists_openCover_gamma1DeckTranslation`, the gluing is
  -- `comp_eq_of_openCover_translation` and `Spec σ ≫ π = π` is
  -- `specInvariantsQuotient_toRingHom_comp`; uniqueness in `R.universal`
  -- (`hmmu`) is what turns the pinned `m` into `mm σ`
  have hcoeq : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of R.A))
      (d₁ : Gamma1Datum N Z), a ≫ R.strM = b ≫ R.strM →
      IsBaseChangeOfGamma1 a d₁ R.dM → IsBaseChangeOfGamma1 b d₁ R.dM →
      a ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A
        = b ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A := by
    intro Z a b d₁ hab ha hb
    obtain ⟨𝒰, h𝒰⟩ := exists_openCover_gamma1DeckTranslation N n hn R a b d₁ hab ha hb
    refine comp_eq_of_openCover_translation a b _ 𝒰 fun i => ?_
    obtain ⟨σ, m, hcls, hi⟩ := h𝒰 i
    refine ⟨m, ?_, hi⟩
    rw [hmmu σ m hcls]
    have h1 : Spec.map (CommRingCat.ofHom
        (MulSemiringAction.toRingHom (gamma0DeckGroup n) R.A σ⁻¹)) = mm σ := by
      rw [hmap σ⁻¹, inv_inv]
    rw [← h1]
    exact specInvariantsQuotient_toRingHom_comp _ _ _
  refine ⟨act, hstrinv, fun σ => ⟨R.dM, ⟨IsBaseChangeOfGamma1.refl R.dM⟩, ⟨?_⟩⟩,
    fun {Z} a b d₁ hab ha hb => hcoeq a b d₁ hab ha hb⟩
  rw [hmap σ]
  exact bcm σ⁻¹

/-- **A rigidified fine moduli scheme plus the level-`n` torsor IS a
`Gamma1Rigidification`** (PROVEN 2026-07-28) — the assembly, with no
citation in it at all.

Three of the four Props come straight from `exists_gamma1DeckAction`.
The fourth, `cover`, is where the two halves meet: `hcov` produces a flat
surjective quasi-compact `p : T' ⟶ T`, a datum `d'` on `T'` which is a
base change of `d`, and a full level-`n` structure `L` on `d'`; then
`R.universal (p ≫ g) d' L` classifies `(d', L)` by an `m : T' ⟶ Spec A`
whose defining clauses are exactly the two remaining conjuncts of
`Gamma1Rigidification.cover` — `m ≫ strM = p ≫ g` and
`IsBaseChangeOfGamma1 m d' dM`.

Note that `hcov` is stated with the level structure rather than with a
classifying map, which is what keeps it independent of `R`: the
rigidifying cover is a property of ONE datum and the fine moduli scheme
converts it into a cover in the sense of `Gamma1Rigidification`.

`hcov`'s binder `_g` is underscored because the CONCLUSION of `hcov` does
not mention it — but it is **load-bearing for the truth of the supplier**
`exists_gamma1FullLevelStructure_cover`, since it is what makes `T` an
`S`-scheme and hence forces the residue characteristics of `T` to be
those of `S`.  Weakening `hcov` by dropping it would make it false at a
base of characteristic dividing `n`; it is used here at `p ≫ g`. -/
theorem nonempty_gamma1Rigidification_of_rigidifiedModuli (N n : ℕ) (hn : 3 ≤ n)
    {S : Scheme.{0}} (R : Gamma1RigidifiedModuli N n S)
    (hcov : ∀ {T : Scheme.{0}} (_g : T ⟶ S) (d : Gamma1Datum N T),
      ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T'),
        AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
        Nonempty (IsBaseChangeOfGamma1 p d' d) ∧
        Nonempty (AbelianFullLevelStructure n d'.ab)) :
    Nonempty (Gamma1Rigidification N S) := by
  classical
  letI := R.commRing_A
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨act, hstrinv, hequiv, hcoeq⟩ := exists_gamma1DeckAction N n hn R
  letI := act
  refine ⟨{ A := R.A
            G := gamma0DeckGroup n
            action_GA := act
            strM := R.strM
            dM := R.dM
            cover := ?_
            strM_invariant := hstrinv
            dM_equivariant := hequiv
            coequalises := fun {Z} a b d₁ hab ha hb => hcoeq a b d₁ hab ha hb }⟩
  intro T g d
  obtain ⟨T', p, d', hf, hs, hq, ⟨bp⟩, ⟨L⟩⟩ := hcov g d
  obtain ⟨m, ⟨hmg, bcm, -⟩, -⟩ := R.universal (p ≫ g) d' L
  exact ⟨T', p, d', m, hf, hs, hq, hmg.symm, ⟨bp⟩, ⟨bcm⟩⟩

/-- **The Katz–Mazur rigidified moduli scheme of `[Γ₁(N)]` over a field in
which `N` is invertible exists** (PROVEN 2026-07-28 from the three leaves
above; it was itself a leaf, Katz–Mazur (8.1.1), until then).

TRUE and classical.  For `N ≥ 4` the moduli problem `[Γ₁(N)]` is rigid
(Katz–Mazur 4.7.0: a pair `(E, P)` with `P` of order `≥ 4` has no
nontrivial automorphism), so over a base where `N` is invertible it is
representable; adjoining a full level-`n` structure for an auxiliary
`n ≥ 3` prime to `char K` makes `[Γ₁(N)], [Γ(n)]` representable by an
AFFINE scheme `Spec A` (8.1.1), with `G = GL₂(ℤ/n)` acting through the
level-`n` structure.

## The auxiliary level, and why `n ∈ {3, 4}` suffices

The only constraints on `n` are `3 ≤ n` (rigidity of `[Γ(n)]`; at `n ≤ 2`
the automorphism `-1` survives) and `char K ∤ n` (étaleness of `E[n]`).
`ringChar K` is `0` or a prime, and `ringChar K ≠ 1` because a field is
nontrivial, so `n := 3` works unless `ringChar K = 3`, where `n := 4`
does.  Note `n` need NOT be prime to `N`: the two level structures are
imposed independently and nothing below compares them.

`_hchar` is what makes `[Γ₁(N)]` representable at all: at
`char K = p ∣ N` a point of exact order `N` acquires an infinitesimal
part, `Spec A` is not smooth, and the whole tower fails.  `hN` is
rigidity — it is passed on to `exists_gamma1RigidifiedModuli`, whose
docstring records that it is not load-bearing there. -/
theorem exists_gamma1Rigidification (N : ℕ) (hN : 4 ≤ N) (K : Type) [Field K]
    (hchar : ¬ ringChar K ∣ N) :
    Nonempty (Gamma1Rigidification N (Spec (CommRingCat.of K))) := by
  classical
  -- an auxiliary level `n ∈ {3, 4}` with `3 ≤ n` and `n` invertible in `K`
  obtain ⟨n, hn, hcn⟩ : ∃ n : ℕ, 3 ≤ n ∧ ¬ ringChar K ∣ n := by
    have h1 : ringChar K ≠ 1 := by
      haveI := ringChar.charP K
      exact CharP.char_ne_one K (ringChar K)
    by_cases h3 : ringChar K = 3
    · exact ⟨4, by norm_num, by rw [h3]; decide⟩
    · refine ⟨3, le_refl 3, fun hd => ?_⟩
      rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
      · exact h1 h
      · exact h3 h
  obtain ⟨R⟩ := exists_gamma1RigidifiedModuli N hN n hn K hchar hcn
  exact nonempty_gamma1Rigidification_of_rigidifiedModuli N n hn R
    (fun {_T} g d => exists_gamma1FullLevelStructure_cover n hn K hcn g d)

/-- **The Katz–Mazur GIT presentation of `Y_1(N)` over a field in which
`N` is invertible exists** (PROVEN 2026-07-27 from the two halves it was
split into — Katz–Mazur (8.1.1) is `exists_gamma1Rigidification`, and
(8.1.3) is `exists_descendClassifyGamma1` plus
`nonempty_gamma1GITPresentation_of_rigidification`, both proven).

The citation this declaration used to carry now lives on
`exists_gamma1Rigidification`, which is what it reduced to. -/
theorem exists_gamma1GITPresentation (N : ℕ) (hN : 4 ≤ N) (K : Type) [Field K]
    (hchar : ¬ ringChar K ∣ N) :
    Nonempty (Gamma1GITPresentation N (Spec (CommRingCat.of K))) :=
  (exists_gamma1Rigidification N hN K hchar).elim fun R =>
    nonempty_gamma1GITPresentation_of_rigidification R

/-! #### The geometry, stated for the PRESENTATION rather than per-atlas

`X0.lean` states its three geometric leaves for an ARBITRARY
`Gamma0Atlas`, and justifies that with `gamma0Atlas_isIso`: any two
atlases have isomorphic coarse spaces, so the per-atlas and
per-model forms are equivalent.  The three below are instead stated for
an arbitrary `Gamma1GITPresentation`, which is the strictly WEAKER —
hence easier — form, since `Gamma1GITPresentation.toGamma1Atlas` maps
presentations to atlases.

Two reasons, and the second is mechanical.  Mathematically, "exhibit one
model and read the properties off it" is exactly what
`exists_isCoarseModuliY1_isSmoothCurve` needs, and the model it exhibits
IS the one the presentation gives; the per-atlas form buys generality
that nothing consumes.  Mechanically, the per-atlas form needs
`gamma1Atlas_isIso`, hence `IsCoarseModuliY1.exists_inverse`, which is
declared some six hundred lines BELOW this point in the file — and
hoisting it would be a relocation in a region with several concurrent
owners, for no gain here.  A successor who wants the per-atlas form has
`IsCoarseModuliY1.exists_inverse` available at its own site and can add
it there.

Note `isAffine` needs no leaf at all in this form: the presentation's
coarse space is literally `Spec (CommRingCat.of P.B)`, so
`AlgebraicGeometry.isAffine_Spec` supplies it — and it is what discharges
`QuasiCompact` and `IsSeparated` at
`exists_isCoarseModuliY1_isSmoothCurve`, so two of that node's five
conclusions cost the tree nothing at all.

**And that affineness is what makes the whole block DESCEND TO RINGS**
(2026-07-27).  Since the coarse space is `Spec B` and — by
`Gamma1GITPresentation.algebraB` and
`Gamma1GITPresentation.specMap_algebraMap` — its structure morphism is
`Spec` of the `K`-algebra structure map of `B`, each of the three
geometric statements is equivalent to a statement about the `K`-algebra
`B`, and each equivalence is a THEOREM here rather than a leaf:

| scheme statement (PROVEN) | the ring-level leaf it rests on | the bridge |
|---|---|---|
| `isDomain_of_gamma1GITPresentation` | `geometricComponents_of_gamma1GITPresentation` | `Scheme.ΓSpecIso` + `isDomain_of_minimalPrimes_transitive` |
| `smoothOfRelativeDimension_of_gamma1GITPresentation` | `locallyStandardSmooth_of_gamma1GITPresentation` | `HasRingHomProperty.Spec_iff` |
| `geometricallyConnected_of_gamma1GITPresentation` | `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation` (2026-07-30; `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation` and then `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` are PROVEN over it) | `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` + `pullbackSpecIso`, then (2026-07-28) `isDomain_tensorProduct_of_injective` |

So a prover sent at any of the three open leaves below works in
commutative algebra over `K` and never touches a scheme.  This is the
same descent the `Γ₀` side performs by hand at
`isDomain_of_gamma0GITPresentation`, carried through for all three
properties instead of one. -/

/-- **The `K`-algebra structure on `B` carried by the structure morphism**
(PROVEN 2026-07-27).

`Gamma1GITPresentation` does not carry an `Algebra K P.B` field — its
base is an arbitrary scheme `S`, and only when `S = Spec K` does one
exist.  It is however DETERMINED, because `Spec` is fully faithful on
affines: `Spec.map_surjective` produces the unique `φ : K ⟶ B` with
`Spec.map φ = P.str`, and this definition names its `toAlgebra`.

All three geometric statements below are stated through it, which is
what turns them from statements about a scheme morphism into statements
about the `K`-algebra `B = A^G`. -/
@[reducible] noncomputable def Gamma1GITPresentation.algebraB {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; Algebra K P.B :=
  letI := P.commRing_B
  (Spec.map_surjective P.str).choose.hom.toAlgebra

/-- **`P.str` IS `Spec` of the structure map of `Gamma1GITPresentation.algebraB`**
(PROVEN 2026-07-27) — the defining property, by `choose_spec`. -/
theorem Gamma1GITPresentation.specMap_algebraMap {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB;
    Spec.map (CommRingCat.ofHom (algebraMap K P.B)) = P.str := by
  letI := P.commRing_B
  letI := P.algebraB
  show Spec.map (CommRingCat.ofHom (Spec.map_surjective P.str).choose.hom) = P.str
  rw [CommRingCat.ofHom_hom]
  exact (Spec.map_surjective P.str).choose_spec

/-- **A subring of a reduced ring is a DOMAIN as soon as SOME family of ring
endomorphisms fixing it permutes the minimal primes transitively** (PROVEN
2026-07-30, pure commutative algebra — no group, no moduli problem, no base
field, mathlib-facing).

The generalisation of `isDomain_of_minimalPrimes_transitive` below, which is
now proved from it in three lines.  The point of the generalisation is that
the group-action form is unusable after base change: the endomorphisms of
`A ⊗[K] L` induced by `σ ∈ G` are perfectly good ring maps fixing `B ⊗[K] L`,
but assembling them into a `MulSemiringAction G (A ⊗[K] L)` instance is pure
bookkeeping (functoriality of `Algebra.TensorProduct.map`, `one_smul`,
`mul_smul`) that the proof never uses.  A bare FAMILY is all the argument
needs, and it is what
`isPrime_nilradical_tensorProduct_of_gamma1GITPresentation` consumes.

Inspecting the proof: `Finite ι` is not needed, `ι` may even be empty (then
`htrans` forces `minimalPrimes A` to have at most one element, which is the
conclusion), and the `f i` are not required to be injective, bijective, or
closed under composition.  Only three things are used — `hfix`, `htrans`, and
`IsReduced A`.

The proof: `A` reduced means `⋂ {p | p ∈ minimalPrimes A} = 0`
(`Ideal.sInf_minimalPrimes` at `⊥`, then `nilradical_eq_zero`).  Given
`x y = 0` in `B` with `x ≠ 0`, pick a minimal prime `p` missing the image `a`
of `x`; then the image `b` of `y` lies in `p`.  Images of `B` are fixed by
every `f i` (`hfix`), so for any minimal `q` and any `i` with
`comap (f i) p = q` we get `b ∈ q`.  Transitivity makes that every `q`, so
`b = 0` and `y = 0` by injectivity. -/
theorem isDomain_of_minimalPrimes_transitive_family
    {ι : Type} {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
    (f : ι → (A →+* A))
    (hfix : ∀ (i : ι) (b : B), f i (algebraMap B A b) = algebraMap B A b)
    (hinj : Function.Injective (algebraMap B A)) [Nontrivial A] [IsReduced A]
    (htrans : ∀ p ∈ minimalPrimes A, ∀ q ∈ minimalPrimes A,
      ∃ i : ι, Ideal.comap (f i) p = q) :
    IsDomain B := by
  have hbot : ∀ a : A, (∀ p ∈ minimalPrimes A, a ∈ p) → a = 0 := by
    intro a ha
    have h1 : a ∈ sInf (minimalPrimes A) := Ideal.mem_sInf.mpr fun {p} hp => ha p hp
    rw [show minimalPrimes A = (⊥ : Ideal A).minimalPrimes from rfl,
      Ideal.sInf_minimalPrimes] at h1
    have h2 : a ∈ nilradical A := h1
    rw [nilradical_eq_zero] at h2
    simpa using h2
  haveI : Nontrivial B := by
    refine ⟨0, 1, fun h => zero_ne_one (α := A) ?_⟩
    rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), h]
  haveI : NoZeroDivisors B := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    refine Or.inr ?_
    have hab : algebraMap B A x * algebraMap B A y = 0 := by
      rw [← map_mul, hxy, map_zero]
    have hane : algebraMap B A x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    obtain ⟨p, hp, hap⟩ : ∃ p ∈ minimalPrimes A, algebraMap B A x ∉ p := by
      by_contra hcon
      exact hane (hbot _ (by simpa using hcon))
    haveI : p.IsPrime := hp.isPrime
    have hbp : algebraMap B A y ∈ p :=
      ((Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp (hab ▸ Ideal.zero_mem p)).resolve_left hap
    refine hinj ?_
    rw [map_zero]
    refine hbot _ fun q hq => ?_
    obtain ⟨i, hi⟩ := htrans p hp q hq
    rw [← hi, Ideal.mem_comap, hfix i y]
    exact hbp
  exact NoZeroDivisors.to_isDomain B

/-- **A ring of invariants is a DOMAIN as soon as the group permutes the
minimal primes transitively** (PROVEN 2026-07-27, pure commutative
algebra — no moduli problem, no base field, mathlib-facing; reproved
2026-07-30 as the `ι := G` case of
`isDomain_of_minimalPrimes_transitive_family` above, with the proof text
retained there).

This is the general form of "`Y_1(N)` is irreducible even though
`𝔐([Γ₁(N)], [Γ(n)])` is not", and it is exactly what makes the `Γ₁`
side over a general `K` different from the `Γ₀` side over `ℚ`, where
`Function.Injective.isDomain` applied to `IsDomain A` suffices.

The proof: `A` reduced means `⋂ {p | p ∈ minimalPrimes A} = 0`
(`Ideal.sInf_minimalPrimes` at `⊥`, then `nilradical_eq_zero`).  Given
`x y = 0` in `B` with `x ≠ 0`, pick a minimal prime `p` missing the image
`a` of `x`; then the image `b` of `y` lies in `p`.  Images of `B` are
`G`-fixed (`smul_algebraMap`, which is where `SMulCommClass G B A` is
consumed), so for any minimal `q` and any `σ` with
`comap σ p = q` we get `b ∈ q`.  Transitivity makes that every `q`, so
`b = 0` and `y = 0` by injectivity.

Note `Algebra.IsInvariant B A G` is NOT needed: only that the image of
`B` is contained in `A^G`, which `SMulCommClass` already gives.  The
hypothesis `Nontrivial A` is what supplies `Nontrivial B`. -/
theorem isDomain_of_minimalPrimes_transitive
    {B A : Type} [CommRing B] [CommRing A] [Algebra B A]
    (G : Type) [Group G] [MulSemiringAction G A] [SMulCommClass G B A]
    (hinj : Function.Injective (algebraMap B A)) [Nontrivial A] [IsReduced A]
    (htrans : ∀ p ∈ minimalPrimes A, ∀ q ∈ minimalPrimes A,
      ∃ σ : G, Ideal.comap (MulSemiringAction.toRingHom G A σ) p = q) :
    IsDomain B :=
  isDomain_of_minimalPrimes_transitive_family
    (fun σ : G => MulSemiringAction.toRingHom G A σ)
    (fun _ _ => by simp [MulSemiringAction.toRingHom]) hinj htrans

/-! #### The cut of `exists_gamma1Datum_fieldExtension`, 2026-07-28

The node used to be one leaf mixing two entirely different kinds of
content: the ARITHMETIC of torsion on an elliptic curve, and the
SCHEME-THEORETIC bridge from a Weierstrass curve to an abelian scheme
with a section.  It is now PROVEN over that split.

| what | where | status |
|---|---|---|
| a Weierstrass curve over an algebraically closed field with a point of exact order `N` | `exists_weierstrassCurve_pointOfExactOrder` | **PROVEN** 2026-07-30 (Silverman *AEC* III.6.4 was already in cone as `WeierstrassCurve.n_torsion_dimension`) |
| a Weierstrass point of order `N` over ANY field gives a `Γ₁(N)`-datum | `nonempty_gamma1Datum_of_weierstrassPoint` | **LEAF** (base-generalisation of a PROVEN `ℚ` theorem) |
| the assembly, at `L := AlgebraicClosure K` | `exists_gamma1Datum_fieldExtension` | **PROVEN** |

**Why the split is worth making.**  The second leaf is *exactly*
`nonempty_gamma1Datum_of_ratPoint` (far below in this file, **PROVEN**
2026-07-27) with `ℚ` replaced by an arbitrary field.  Its whole
obstruction is that `EllipticScheme.lean` — all ~9000 lines of it,
including `exists_ellipticScheme_of_projModel`, `projGroupLaw` and
`smoothOfRelativeDimension_projToSpec` — is stated at the concrete base
`ℚ`.  That is a base-generalisation task with a known shape and no new
mathematics, and it is *reusable*: every other leaf in this development
that needs an elliptic scheme over a field other than `ℚ` wants the same
thing.  Keeping it fused with the torsion arithmetic hid that.

**A REFINEMENT to the old docstring's "concretely one may also take the
Tate normal form" (2026-07-28).**  That is a route for the FIRST leaf
only, and it is not obviously the cheaper one: the Tate normal form
`y² + (1 − c)xy − by = x³ − bx²` with the point `(0,0)` has `(0,0)` of
order exactly `N` only on the level-`N` locus, i.e. after solving the
division-polynomial condition — which is the function field of `Y_1(N)`
and therefore circular for anyone trying to use this leaf to prove
`Y_1(N)` is nonempty.  Over an algebraically closed field the direct
route (`E[N] ≅ (ℤ/N)²`, then any element of exact order `N`) needs no
such locus and is the one the leaf below is stated for. -/

/-- **Every field carries an elliptic curve** (PROVEN 2026-07-30) — the
existence half of `exists_weierstrassCurve_pointOfExactOrder` below, and
the place where its characteristic-`2` and `-3` corner cases live.

There is **no single integral Weierstrass equation that works in every
characteristic**: `Δ = ±1` is impossible over `ℤ` (no elliptic curve over
`ℚ` has everywhere-good reduction), so the docstring below's suggested
witness `⟨1, 0, 0, 0, 1⟩` — of discriminant `-433` — dies in
characteristic `433`.  Two witnesses are needed, and TWO suffice because
their bad characteristics are different primes:

* `y² + y = x³`, i.e. `⟨0, 0, 1, 0, 0⟩`, has `Δ = -27`, a unit unless
  `char = 3`;
* `y² = x³ + x`, i.e. `⟨0, 0, 0, 1, 0⟩`, has `Δ = -64 = -2⁶`, a unit
  unless `char = 2`.

The case split below is on `(2 : L) = 0`, which is all that is needed:
in characteristic `2` the first curve has `Δ = -27 = -1`. -/
theorem exists_isElliptic_of_field (L : Type) [Field L] :
    ∃ E : WeierstrassCurve L, E.IsElliptic := by
  by_cases h2 : (2 : L) = 0
  · refine ⟨⟨0, 0, 1, 0, 0⟩, ⟨?_⟩⟩
    rw [isUnit_iff_ne_zero]
    have hΔ : (WeierstrassCurve.mk (0 : L) 0 1 0 0).Δ = -27 := by
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [hΔ]
    have h27 : (27 : L) = 1 := by
      have h : (27 : L) = 1 + 13 * 2 := by norm_num
      rw [h, h2]; ring
    rw [h27]
    exact neg_ne_zero.mpr one_ne_zero
  · refine ⟨⟨0, 0, 0, 1, 0⟩, ⟨?_⟩⟩
    rw [isUnit_iff_ne_zero]
    have hΔ : (WeierstrassCurve.mk (0 : L) 0 0 1 0).Δ = -(2 ^ 6) := by
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hΔ]
    exact neg_ne_zero.mpr (pow_ne_zero _ h2)

/-- **Over an algebraically closed field of characteristic prime to `N`,
some elliptic curve carries a point of exact order `N`** (**PROVEN
2026-07-30**; a sorry leaf from 2026-07-28) — Silverman *AEC* III.6.4, and
pure elliptic-curve arithmetic: no schemes, no moduli, no `Γ₁`.

## The route

`E[N] ≅ (ℤ/N)²` for every elliptic curve `E` over an algebraically closed
field `L` with `char L ∤ N` (III.6.4).  Any generator of a `ℤ/N` factor
then has exact order `N`.  The only other thing owed is that SOME
elliptic curve exists over `L` at all, which is where the
characteristic-2 and -3 corner cases live: the short form
`y² = x³ + a₄x + a₆` is singular in characteristic `2`, so the witness
must be given in the general five-coefficient form.  That half is
`exists_isElliptic_of_field` immediately above — and note the correction
recorded there: the old suggestion "`⟨1, 0, 0, 0, 1⟩`, of discriminant a
unit in every characteristic" is FALSE (its discriminant is `-433`), and
in fact no single integral equation works, so two witnesses are used.

## How it is proven

`exists_isElliptic_of_field` supplies `E`; `hchar` is turned into
`(N : L) ≠ 0` by `ringChar.spec`; `WeierstrassCurve.n_torsion_dimension`
(`EllipticCurve/Torsion.lean`, the III.6.4 citation, stated for
`IsSepClosed` which `IsAlgClosed` supplies) gives
`E.nTorsion N ≃+ ZMod N × ZMod N`; the preimage of `(1, 0)` has order
`lcm N 1 = N` by `Prod.addOrderOf` and `ZMod.addOrderOf_one`, and
`addOrderOf_injective` carries that order back along the equivalence and
then along `Submodule.subtype`.  Note this works verbatim at `N = 0` too
(`ZMod 0 = ℤ` and `addOrderOf (1 : ℤ) = 0`), though the hypothesis is
unsatisfiable there.

## Faithfulness

`hchar` is load-bearing for TRUTH: at `char L = p ∣ N` the group scheme
`E[N]` is not étale, `E[p^k](L)` is `ℤ/p^k` for ordinary `E` and trivial
for supersingular `E`, and for `N = p` with `E` supersingular there is no
point of exact order `N` over ANY extension.  `IsAlgClosed L` is
load-bearing: over `ℚ` the statement is FALSE for every `N ≥ 13` and for
`N = 11` by Mazur's theorem, which is the whole subject of this module.

Note there is **no `4 ≤ N`**: it is not needed here.  At `N = 0` the
hypothesis `¬ ringChar L ∣ 0` is unsatisfiable (`c ∣ 0` always), so the
statement is vacuously true there, and at `1 ≤ N ≤ 3` it is true and
easy.  Rigidity — the reason the consumers carry `4 ≤ N` — is about
automorphisms of the pair, not about existence. -/
theorem exists_weierstrassCurve_pointOfExactOrder (N : ℕ)
    (L : Type) [Field L] [DecidableEq L] [IsAlgClosed L] (hchar : ¬ ringChar L ∣ N) :
    ∃ (E : WeierstrassCurve L) (hE : E.IsElliptic),
      letI := hE
      ∃ P : E.toAffine.Point, addOrderOf P = N := by
  have hNL : (N : L) ≠ 0 := fun h => hchar ((ringChar.spec L N).mp h)
  obtain ⟨E, hE⟩ := exists_isElliptic_of_field L
  refine ⟨E, hE, ?_⟩
  letI := hE
  obtain ⟨φ⟩ := E.n_torsion_dimension (n := N) hNL
  set v : E.nTorsion N := φ.symm ((1 : ZMod N), (0 : ZMod N)) with hv
  have hvord : addOrderOf v = N := by
    have h1 : addOrderOf (φ v) = addOrderOf v :=
      addOrderOf_injective φ.toAddMonoidHom φ.injective v
    rw [hv, AddEquiv.apply_symm_apply] at h1
    rw [← h1, Prod.addOrderOf]
    simp [ZMod.addOrderOf_one]
  refine ⟨v.1, ?_⟩
  exact (addOrderOf_injective
    ((Submodule.subtype (Submodule.torsionBy ℤ E.toAffine.Point (N : ℤ))).toAddMonoidHom)
    (Submodule.injective_subtype _) v).trans hvord

/-- **A point of exact order `N` on an elliptic curve over an arbitrary
field `L` gives a `Γ₁(N)`-structure over `Spec L`** (sorry leaf, opened
2026-07-28) — the base-generalisation of `nonempty_gamma1Datum_of_ratPoint`,
which is the SAME statement at `L := ℚ` and is **PROVEN** far below in
this file.

## What is owed, and what is not

Read `nonempty_gamma1Datum_of_ratPoint`'s docstring: it lists the three
steps in dependency order, and all three generalise.

1. `exists_ellipticScheme_of_weierstrass` — the bridge from a Weierstrass
   curve to an abelian scheme of relative dimension one with a
   Galois-equivariant `≃+` on geometric points.  **This is the whole
   obstruction**: it and everything under it in `EllipticScheme.lean`
   (`exists_ellipticScheme_of_projModel`, `projGroupLaw`,
   `smoothOfRelativeDimension_projToSpec`,
   `exists_projGeomFibreAddEquiv`) are stated at the concrete base `ℚ`.
   Nothing in their content is `ℚ`-specific — `WeierstrassCurve.Projective`
   `.proj` and `projToSpec` are already defined over a general base — so
   this is a base-generalisation, not new mathematics.
2. Galois descent of the point to a SECTION, `exists_section_of_galoisInvariant`,
   with `Γ_ℚ` replaced by `Γ_L`.  An `L`-rational point is fixed by
   `Γ_L`, and for a scheme separated over `L` the `L`-points are the
   Galois-fixed `L̄`-points.  **When `L` is algebraically closed — which
   is the only case the consumer below needs — this step is trivial**,
   since `Γ_L` is trivial; so a prover who wants only the consumer may
   add `[IsAlgClosed L]` and skip it.  It is stated without that
   hypothesis because the general form is what the rest of the
   development will want.
3. Order transport: `Point.map` along `L → L̄` is injective, so
   `addOrderOf` is unchanged; the `≃+` of step 1 preserves it by
   `AddEquiv.addOrderOf_eq`. `RelPoint.ofSection`'s order at an arbitrary
   geometric point `t : Spec K' ⟶ Spec L` is the order of the image of
   `P` in `E(K')`, and `L → K'` is injective (`L` is a field), so it is
   again `N`.  This is what `PointOfExactOrder.geom_order` asks and it is
   PROVEN verbatim at `ℚ`.

## RECONNAISSANCE on steps 2 and 3, 2026-07-30 (read before starting)

Step 1 really is the whole *mathematical* obstruction, but steps 2 and 3
are not free either, and the split between "already base-generic" and
"still `ℚ`-hardcoded" is not where the list above suggests.  Checked
against the sources:

* **Step 2 is already available over any PERFECT base.**
  `exists_specSection_of_specGal_invariant` (further down this file,
  PROVEN) is stated for `{F : Type} [Field F] [PerfectField F]` — not for
  `ℚ` — and `specAlgClos` / `specGal` (`Modularity/AbelianScheme.lean`)
  are stated for an arbitrary field.  So the descent half needs no work
  at all when `L` is perfect.  What is `ℚ`-hardcoded is
  `exists_section_of_galoisInvariant`, the thin wrapper immediately above
  `nonempty_gamma1Datum_of_ratPoint`; re-instantiating it is bookkeeping.

* **Step 3 hides a second `ℚ`-specific node.**  The `geom_order` field is
  discharged by `exists_pointOfExactOrder_of_geomPt`, which calls
  `exists_injective_pre_geomBase` (`X0.lean`, PROVEN) — and *that* one is
  genuinely `ℚ`-shaped: its proof runs through `subsingleton_hom_specQ`
  and `nonempty_ringHom_of_hom_specQ`, i.e. through the INITIALITY of `ℚ`
  among rings, to produce the embedding `L̄ ↪ K'` over the base.  Over a
  general `L` that embedding still exists — `t : Spec K' ⟶ Spec L` makes
  `K'` an `L`-algebra and `K'` is algebraically closed, so
  `exists_ringHom_algebraicClosure` applies — but the *commuting* clause
  is no longer a `Subsingleton.elim` and has to be proven.  Budget a
  second declaration for it.

* **AND THE ROUTE AS WRITTEN DOES NOT REACH THIS LEAF'S STATEMENT.**
  There is no `[PerfectField L]` here, and step 2 cannot be dropped to
  cover the imperfect case: `Field.absoluteGaloisGroup L` is
  `AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L`, whose fixed field inside
  `L̄` is the purely inseparable closure of `L`, strictly larger than `L`
  — which is exactly why `exists_specSection_of_specGal_invariant` asks
  for `PerfectField`.  So a `Γ_L`-invariant geometric point of an
  imperfect-base scheme need not descend, and no repair of step 2 alone
  will do.

  **The leaf is nonetheless TRUE as stated**, because the descent is not
  actually needed: `P` is `L`-rational to begin with, so the section is
  there before any geometric point is formed, and only `geom_order` — a
  statement about images — has to travel upwards.  A successor therefore
  has a genuine choice to make when stating step 1's `L`-analogue: state
  the bridge so that it produces the section from the `L`-point directly
  (no descent, works for imperfect `L`), or state it in the `ℚ`-side's
  geometric-fibre-only form and add `[PerfectField L]` here.  The first is
  the faithful one; the second silently weakens this leaf.

## Faithfulness

No characteristic hypothesis is needed or wanted: `hP` already asserts
that a point of exact order `N` EXISTS, which is strictly stronger than
anything a characteristic assumption would buy, and the conclusion only
transports it.  `[IsElliptic]` is load-bearing — a singular Weierstrass
curve is not an abelian scheme.  At `N = 0` the statement is true and not
vacuous, for the reason `nonempty_gamma1Datum_of_ratPoint`'s docstring
records: `PointOfExactOrder` carries no finiteness field, so
`addOrderOf = 0` asks for a section of infinite order and a curve of
positive rank supplies one. -/
theorem nonempty_gamma1Datum_of_weierstrassPoint {N : ℕ} (L : Type) [Field L]
    [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic] (P : E.toAffine.Point)
    (hP : addOrderOf P = N) :
    Nonempty (Gamma1Datum N (Spec (CommRingCat.of L))) :=
  sorry

/-- **`[Γ₁(N)]` is nonempty over SOME field extension of `K`**
(**PROVEN 2026-07-28** over the two leaves above; formerly a single
`sorry` leaf, cut out of `geometricComponents_of_gamma1GITPresentation`)
— an elliptic curve carrying a point of exact order `N`, over some
extension field of `K`.

TRUE and elementary, and much weaker than anything about modular curves:
`L := AlgebraicClosure K` already works, and that is what the proof takes.
The only bookkeeping is that `ringChar (AlgebraicClosure K) = ringChar K`,
which is `charP_of_injective_algebraMap` along the (automatically
injective) `algebraMap K (AlgebraicClosure K)` read through
`ringChar.eq`.

This is deliberately the WEAKEST form that its consumer
`nontrivial_A_of_gamma1GITPresentation` needs: no algebraic closedness in
the CONCLUSION, no rationality over `K` itself — and rationality over `K`
would be FALSE, since `Y_1(N)(K)` can be empty
(`isEmpty_gamma1Datum_finiteField` is the extreme case, and the whole
point of this module is that `Y_1(25)(ℚ)` contains no non-cuspidal
point).

Note the ORDER of quantifiers: `L` may depend on `K` and `N`.  Nothing
downstream sees `L`; it is consumed immediately by `classify` and
discarded.

**`hchar` is REQUIRED and is now USED** (it was `_hchar` while this was a
leaf): at `char K ∣ N` the group scheme `E[N]` is not étale and a section
of exact order `N` need not exist at all (at `N = p = char K` and `E`
supersingular there is none over any extension).  `_hN : 4 ≤ N` is
genuinely NOT load-bearing — see `exists_weierstrassCurve_pointOfExactOrder`
— and is kept, underscored, only to match every call site.

## NON-VACUITY NOTE for `exists_gamma1RigidifiedModuli` (2026-07-28)

This leaf, together with `exists_gamma1FullLevelStructure_cover`, is what
stops `Gamma1RigidifiedModuli N n (Spec K)` from being satisfiable by the
ZERO ring.  `Spec 0` is the empty scheme, over which
`AbelianFullLevelStructure`'s `geom_basis` and `PointOfExactOrder`'s
`geom_order` are both vacuous (there is no morphism `Spec K' ⟶ ∅`), so
`A := 0` would discharge every field of that structure EXCEPT `universal`
— and `universal` is killed exactly by exhibiting one
datum-with-level-structure over one NONEMPTY `K`-scheme, which is this
leaf followed by the cover.  So the faithfulness paragraph of
`exists_gamma1RigidifiedModuli` is right that a nonzero `A` is forced,
but the reason is not `hcharn` on its own: it is `hcharn` **plus the
truth of these two leaves**.  Anyone tempted to discharge that leaf with
a degenerate witness should read this paragraph first. -/
theorem exists_gamma1Datum_fieldExtension (N : ℕ) (_hN : 4 ≤ N)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ N) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Nonempty (Gamma1Datum N (Spec (CommRingCat.of L))) := by
  classical
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, ?_⟩
  -- ONE `DecidableEq` instance, shared by the two leaves: mathlib's group law on
  -- `WeierstrassCurve.Affine.Point` is defined by a case split on equality of
  -- `x`-coordinates and so carries `[DecidableEq]` on the base field.  Over `ℚ`
  -- (`nonempty_gamma1Datum_of_ratPoint`) it is found automatically; over an
  -- abstract field it is not, and the two leaves must be handed the SAME one or
  -- their `addOrderOf`s are different terms.
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  have hcharL : ¬ ringChar (AlgebraicClosure K) ∣ N := by
    haveI : CharP (AlgebraicClosure K) (ringChar K) :=
      charP_of_injective_algebraMap
        (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
    rwa [ringChar.eq (AlgebraicClosure K) (ringChar K)]
  obtain ⟨E, hE, hPt⟩ :=
    exists_weierstrassCurve_pointOfExactOrder N (AlgebraicClosure K) hcharL
  letI := hE
  obtain ⟨P, hP⟩ := hPt
  exact nonempty_gamma1Datum_of_weierstrassPoint (AlgebraicClosure K) E P hP

/-- **The rigidified moduli scheme is nonempty** (PROVEN 2026-07-28 over
`exists_gamma1Datum_fieldExtension`; formerly the first conjunct of
`geometricComponents_of_gamma1GITPresentation`).

No moduli geometry is used, only the CLASSIFYING map: a `Γ₁(N)`-datum
over `Spec L` for a field extension `L/K` is an `S`-scheme carrying a
datum, so `P.classify` returns a morphism `Spec L ⟶ Spec B`, i.e. (by
full faithfulness of `Spec`, through `Spec.preimage`) a ring map
`B →+* L`.  A ring map into a nontrivial ring has nontrivial domain
(`RingHom.domain_nontrivial`), so `B` is nontrivial, and
`injective_algebraMap` carries that up to `A`.

The same argument through `cover` would work — `cover` produces a flat
SURJECTIVE `p : T' ⟶ Spec L` and a rigidification `m : T' ⟶ Spec A` — but
it needs surjectivity of `p` on underlying spaces to see `T' ≠ ∅`, where
the `classify` route needs nothing at all. -/
theorem nontrivial_A_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; Nontrivial P.A := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  obtain ⟨L, _, _, ⟨d⟩⟩ := exists_gamma1Datum_fieldExtension N hN K hchar
  -- the classifying map of `d`, a morphism `Spec L ⟶ Spec B`
  have c : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of P.B) :=
    (P.classify (Spec.map (CommRingCat.ofHom (algebraMap K L))) d).1
  haveI : Nontrivial P.B := (Spec.preimage c).hom.domain_nontrivial
  exact P.injective_algebraMap.nontrivial

/-! #### Katz–Mazur 8.2.1 on the RIGIDIFIED ring `A`, stated once

**Added 2026-07-28.**  Before this block the file carried Katz–Mazur 8.2.1
TWICE — once as `isReduced_A_of_gamma1GITPresentation` (reducedness of `A`)
and once as `smooth_coarseRing_of_gamma1GITPresentation` (smoothness of `B`
plus `ringKrullDim B = 1`).  Both are now THEOREMS over the single leaf
`smoothCurve_A_of_gamma1GITPresentation` below, which states 8.2.1 in the
form Katz–Mazur actually proves it: `Spec A` is a smooth affine curve.

The two bridges that make that possible were both already in the tree and
both were recorded as unavailable:

* `Algebra.Smooth.isReduced_of_isField`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`,
  **PROVEN**) — a smooth algebra over a field is reduced.
* `ringKrullDim_eq_of_isIntegral_of_injective`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`,
  **PROVEN**) — Krull dimension is preserved by an INJECTIVE INTEGRAL
  extension, with **no domain hypothesis**.  See the correction recorded on
  `ringKrullDim_eq_of_gamma1GITPresentation`.
-/

/-- **The `K`-algebra structure of the rigidified ring `A`** — the `A`-side
companion of `Gamma1GITPresentation.algebraB`, obtained from `P.strM` exactly
as that one is obtained from `P.str`.

`Spec` is fully faithful, so the chosen preimage is the unique ring map with
`Spec.map (CommRingCat.ofHom (algebraMap K P.A)) = P.strM`; that identity is
`Gamma1GITPresentation.specMap_algebraMap_A` immediately below.  It was
deliberately left undeclared until 2026-07-30, because nothing consumed it and
a proven-but-unconsumed lemma is free-floating; `Gamma1GITPresentation.isScalarTower`
now does. -/
@[reducible] noncomputable def Gamma1GITPresentation.algebraA {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; Algebra K P.A :=
  letI := P.commRing_A
  (Spec.map_surjective P.strM).choose.hom.toAlgebra

/-- **`P.strM` IS `Spec` of the structure map of `Gamma1GITPresentation.algebraA`**
(PROVEN 2026-07-30) — the `A`-side twin of
`Gamma1GITPresentation.specMap_algebraMap`, by `choose_spec`. -/
theorem Gamma1GITPresentation.specMap_algebraMap_A {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.algebraA;
    Spec.map (CommRingCat.ofHom (algebraMap K P.A)) = P.strM := by
  letI := P.commRing_A
  letI := P.algebraA
  show Spec.map (CommRingCat.ofHom (Spec.map_surjective P.strM).choose.hom) = P.strM
  rw [CommRingCat.ofHom_hom]
  exact (Spec.map_surjective P.strM).choose_spec

/-- **`K → B → A` IS a scalar tower** (PROVEN 2026-07-30) — and this corrects a
documented claim that it is not available.

The docstring of `smoothCurve_A_of_gamma1GITPresentation` records that "there is
no `IsScalarTower K B A` in scope and none is needed".  The second half was true
of its two consumers; the first half is FALSE, and the tower is forced by the
axioms rather than being extra data.

`Gamma1GITPresentation.algebraB` and `.algebraA` are the unique ring maps whose
`Spec` is `P.str` and `P.strM`.  The universal family's classifying map is a
relative point of `P.str` over `P.strM`, so it commutes with the two structure
morphisms — `(P.classify P.strM P.dM).2` — and `P.classify_dM` says that map IS
`Spec (algebraMap B A)`.  So

    Spec (algebraMap B A) ≫ Spec (algebraMap K B) = Spec (algebraMap K A)

and `Spec.map_injective` turns that into the tower identity.  Nothing modular is
used: only `classify_dM` and the subtype property of a `RelPoint`.

Consumed by `finitePresentation_invariants_of_gamma1GITPresentation`, which is
Noether's theorem on invariants and cannot be stated without it. -/
theorem Gamma1GITPresentation.isScalarTower {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.commRing_B; letI := P.algebra_BA;
    letI := P.algebraA; letI := P.algebraB;
    IsScalarTower K P.B P.A := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.algebraA
  letI := P.algebraB
  have hstr : Spec.map (CommRingCat.ofHom (algebraMap P.B P.A)) ≫ P.str = P.strM := by
    rw [← P.classify_dM]; exact (P.classify P.strM P.dM).2
  refine IsScalarTower.of_algebraMap_eq' ?_
  have key : CommRingCat.ofHom (algebraMap K P.A) =
      CommRingCat.ofHom ((algebraMap P.B P.A).comp (algebraMap K P.B)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, P.specMap_algebraMap, P.specMap_algebraMap_A]
    exact hstr.symm
  simpa using congrArg CommRingCat.Hom.hom key

/-- **`A` and `B = A^G` have the same Krull dimension** (PROVEN 2026-07-28,
unconditionally — no modular input, no domain hypothesis, no hypothesis on
`N` or on `char K` at all).

`Algebra.IsInvariant.isIntegral` makes `A` integral over `B` from `Finite G`
alone, `P.injective_algebraMap` is a field of the structure, and
`ringKrullDim_eq_of_isIntegral_of_injective` (Stacks `00OK` + `00OJ`,
PROVEN in `SmoothConnectedCriteria.lean`) needs exactly those two.

## CORRECTION — this refutes a documented blocker

The previous version of `smooth_coarseRing_of_gamma1GITPresentation`'s
docstring recorded, as item 2 of "THE ROUTE FROM `A`, AND EXACTLY WHAT IS
MISSING FOR IT", that `ringKrullDim B = ringKrullDim A` was **blocked**:

> the pieces are `dimensionLEOne_of_isInvariant` and
> `ringKrullDim_eq_one_of_isInvariant` in the same file, but **both carry
> `[IsDomain S]`, i.e. `IsDomain A`, which is FALSE here**

The first half is TRUE and was re-checked on 2026-07-28: both of those
`InvariantCoarseRing.lean` lemmas do carry `[IsDomain S]`, and `IsDomain A`
is indeed false here (as soon as `ζ_n ∈ K` the scheme
`𝔐([Γ₁(N)], [Γ(n)])` has `φ(n)` components).  The CONCLUSION is stale:
those two lemmas are not the only route, and
`ringKrullDim_eq_of_isIntegral_of_injective` — which landed in
`SmoothConnectedCriteria.lean` in the same 2026-07-28 release that wrote
the note — proves the transfer with no domain hypothesis whatever.  Its own
faithfulness note confirms injectivity is the ONLY load-bearing hypothesis
(without it take `S = 0`, integral over `R` with `ringKrullDim S = ⊥`).

So the dimension half of the route from `A` is now fully open; only the
smoothness half still needs descent along the torsor.  *The check that would
refute this*: a use of `IsDomain` in the proof of
`ringKrullDim_eq_of_isIntegral_of_injective`, which has none — it is
`Order.krullDim_le_of_strictMono` one way and a lifted `LTSeries` the
other. -/
theorem ringKrullDim_eq_of_gamma1GITPresentation {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.commRing_B;
    ringKrullDim P.A = ringKrullDim P.B := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  letI := P.isInvariant_BAG
  haveI : Algebra.IsIntegral P.B P.A := Algebra.IsInvariant.isIntegral P.B P.A P.G
  exact ringKrullDim_eq_of_isIntegral_of_injective P.B P.A P.injective_algebraMap

/-- **`Spec A` is a smooth affine curve over `K`** (sorry leaf, opened
2026-07-28 as the SINGLE statement of Katz–Mazur 8.2.1 in this file) —
Katz–Mazur 8.2.1, Deligne–Rapoport III.1.

TRUE and classical, and this is the form 8.2.1 is actually proved in:
`𝔐([Γ₁(N)], [Γ(n)])` is SMOOTH of relative dimension one over `ℤ[1/Nn]`,
hence smooth of relative dimension one over every field `K` in which `N`
is invertible.  `P` presents that scheme as the affine `Spec A`, so the
statement is the ring-level `Algebra.Smooth K A` together with
`ringKrullDim A = 1`.

## Why this leaf replaced two others

It is consumed twice, and those two consumptions were previously two
independent statements of the same theorem:

| consumer | conjunct used | bridge |
|---|---|---|
| `isReduced_A_of_gamma1GITPresentation` | `Algebra.Smooth K A` | `Algebra.Smooth.isReduced_of_isField` (PROVEN) |
| `smooth_coarseRing_of_gamma1GITPresentation` | `ringKrullDim A = 1` | `ringKrullDim_eq_of_gamma1GITPresentation` (PROVEN) |

Stating 8.2.1 once, on `A`, is strictly better than stating it on `A` for
reducedness and again on `B` for dimension: `A` is where Katz–Mazur proves
it, and the descent to `B` is now a theorem rather than a second appeal to
the literature.

## `Algebra.Smooth` and `ringKrullDim` are the right two conjuncts

`Algebra.Smooth` unfolds to `FormallySmooth` plus `FinitePresentation`, so
the finite-type half ("`𝔐` is affine of finite type over the base") is
inside it; over the Noetherian base `K` finite type and finite presentation
coincide.  Relative dimension is NOT part of `Algebra.Smooth`, which is why
the Krull dimension is carried alongside rather than folded in — and it is
carried as `ringKrullDim` rather than as `SmoothOfRelativeDimension`
because that is the shape both consumers want and because
`smoothOfRelativeDimension_specMap_algebraMap_of_smooth` converts one into
the other downstream, on `B`.

The algebra structure is `Gamma1GITPresentation.algebraA`, i.e. the one
induced by `P.strM`; the two consumers use the two conjuncts separately and
so need no `IsScalarTower K B A`.  **This docstring used to add "and there is
none in scope", which is FALSE** (corrected 2026-07-30): the tower is forced
by `classify_dM` and is now available as
`Gamma1GITPresentation.isScalarTower`, which is what lets
`finitePresentation_invariants_of_gamma1GITPresentation` state Noether's
theorem on invariants over this leaf.

## FAITHFULNESS

`hchar` is load-bearing: at `char K ∣ N` the moduli problem `[Γ₁(p)]` in
characteristic `p` is not étale over the `j`-line, `𝔐` is not smooth, and
`Spec A` acquires nilpotents — which is exactly what would make the
reducedness consumer false.  `hN` is what makes `[Γ₁(N)]` rigid (no extra
automorphisms) and is required by every consumer, so it is kept even though
smoothness of the rigidified problem does not need it on its own.

NOT VACUOUS, and the dimension conjunct is what rules vacuity out: at
`N = 0` or at `char K ∣ N` the ring `A` would be the zero ring, whose
`ringKrullDim` is `⊥ ≠ 1`.  So this leaf asserts nonemptiness of `Spec A`
as well, and agrees on that point with `nontrivial_A_of_gamma1GITPresentation`
(PROVEN above over `exists_gamma1Datum_fieldExtension`) — the two are
consistent, and neither is implied by the other, since `Nontrivial A` does
not pin a dimension and `ringKrullDim A = 1` is stated with no reference to
a datum.

## WHY THIS IS NOT PROVABLE FROM THE STRUCTURE (route audit, 2026-07-28)

`Gamma1GITPresentation` carries only moduli-FUNCTOR data — `classify`,
`classify_natural`, `classify_dM`, `cover`, `strM_invariant`,
`dM_equivariant` — and no geometric input whatever.  Those axioms are far
more rigid than they look, and it is worth recording what they DO force, so
the next prover does not re-derive it:

> Naturality together with `classify_dM` forbids `Spec A` from being a
> nilpotent thickening whose universal datum is pulled back from the
> reduction.  Concretely, if `dM ≅ h^* e` for some `h : Spec A ⟶ Z`, then
> naturality makes `(classify strM dM).1` factor through `h`, while
> `classify_dM` says that morphism IS `Spec (algebraMap B A)`.  Taking
> `A = A₀[ε]` with `dM` pulled back along `Spec A₀[ε] ⟶ Spec A₀` — by the
> projection, or by `a ↦ a + ε D(a)` for any derivation `D` — the factoring
> map misses `ε`, and the two descriptions of `π` disagree.  A disjoint junk
> component `A₀ × k[ε]` is excluded the same way, using surjectivity of the
> fpqc cover produced by `cover` to see that the classifying map of the
> junk family would have to land in two disjoint clopens at once.

What the axioms do NOT force is smoothness itself: `cover` says only that
`Spec A ⟶ 𝔐` is an fpqc EPIMORPHISM, not that it is smooth or a
monomorphism, and nothing in the structure knows that elliptic curves with
`Γ₁(N)`-structure deform unobstructedly.  That is the content of 8.2.1 and
it has to be cited.  *The check that would refute this audit*: a
`Gamma1GITPresentation N (Spec (CommRingCat.of K))` built with a
non-smooth `A` satisfying all nine fields, or a derivation of
`Algebra.FormallySmooth K A` from `cover` alone. -/
theorem smoothCurve_A_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.algebraA;
    Algebra.Smooth K P.A ∧ ringKrullDim P.A = (1 : ℕ) :=
  sorry

/-- **The rigidified moduli scheme is reduced** (**PROVEN 2026-07-28** over
`smoothCurve_A_of_gamma1GITPresentation`; opened as a sorry leaf earlier the
same day, cut out of `geometricComponents_of_gamma1GITPresentation`) —
Katz–Mazur 8.2.1.

`𝔐([Γ₁(N)], [Γ(n)])` is SMOOTH over `ℤ[1/Nn]` (8.2.1), hence smooth over
every field `K` in which `N` is invertible, and a smooth algebra over a
field is reduced (it is even regular).

**The bridge was already in the tree.**  The previous version of this
docstring said only that this is "the SAME geometric input as
`locallyStandardSmooth_of_gamma1GITPresentation`" and that "whoever proves
either of them should look at the other", proposing a descent argument
(`A` smooth gives `B = A^G` normal) as the link.  That is true but is not
what was needed: `Algebra.Smooth.isReduced_of_isField`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`) is
**PROVEN** — from `Algebra.IsStandardSmooth.isReduced_of_field` by the
standard open cover on which a smooth algebra is standard smooth — and
`X0.lean` was already consuming its scheme-level form
`AlgebraicGeometry.isReduced_of_smooth_over_field`.  So reducedness needs no
descent and no normality: it is one application of an existing lemma to the
smoothness conjunct of the leaf above.

Reducedness rather than smoothness is still what is STATED here, because
reducedness is all that `isDomain_of_minimalPrimes_transitive` consumes. -/
theorem isReduced_A_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; IsReduced P.A := by
  letI := P.commRing_A
  letI := P.algebraA
  haveI := (smoothCurve_A_of_gamma1GITPresentation hN hchar P).1
  exact Algebra.Smooth.isReduced_of_isField (Field.toIsField K)

/-! #### The deck group acts `K`-linearly, hence on every base change

Four small declarations, all PROVEN 2026-07-30, whose only purpose is to
give the base-changed transitivity leaf below something to say.  The
non-formal one is the first: `strM_invariant` is a statement about
`Spec`, and what the tensor product needs is the RING-level fact that `σ`
fixes `K` pointwise.  `Spec` is fully faithful, so the two are the same
fact — the proof is `Gamma1GITPresentation.specMap_algebraMap_A` followed
by `Spec.map_injective`, exactly as in
`Gamma1GITPresentation.isScalarTower`. -/

/-- **Every `σ ∈ G` fixes `K` pointwise inside `A`** (PROVEN 2026-07-30) —
the ring-level content of `Gamma1GITPresentation.strM_invariant`.

`strM_invariant σ` says `Spec σ ≫ strM = strM`; `specMap_algebraMap_A` says
`strM = Spec (algebraMap K A)`; `Spec.map_injective` turns the composite
into `σ ∘ algebraMap K A = algebraMap K A`.  Nothing modular is used. -/
theorem Gamma1GITPresentation.smul_algebraMap_A {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) (σ : P.G) :
    letI := P.commRing_A; letI := P.algebraA; letI := P.group_G; letI := P.action_GA;
    ∀ c : K, MulSemiringAction.toRingHom P.G P.A σ (algebraMap K P.A c) = algebraMap K P.A c := by
  letI := P.commRing_A
  letI := P.algebraA
  letI := P.group_G
  letI := P.action_GA
  intro c
  have key : CommRingCat.ofHom
      ((MulSemiringAction.toRingHom P.G P.A σ).comp (algebraMap K P.A)) =
      CommRingCat.ofHom (algebraMap K P.A) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, P.specMap_algebraMap_A]
    exact P.strM_invariant σ
  have h2 : (MulSemiringAction.toRingHom P.G P.A σ).comp (algebraMap K P.A) =
      algebraMap K P.A := by
    simpa using congrArg CommRingCat.Hom.hom key
  simpa using RingHom.congr_fun h2 c

/-- **`σ ∈ G` as a `K`-algebra endomorphism of `A`** (PROVEN 2026-07-30) —
`MulSemiringAction.toRingHom` upgraded along `smul_algebraMap_A`. -/
noncomputable def Gamma1GITPresentation.algHomA {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) (σ : P.G) :
    letI := P.commRing_A; letI := P.algebraA; letI := P.group_G; letI := P.action_GA;
    P.A →ₐ[K] P.A :=
  letI := P.commRing_A
  letI := P.algebraA
  letI := P.group_G
  letI := P.action_GA
  AlgHom.mk (MulSemiringAction.toRingHom P.G P.A σ) (P.smul_algebraMap_A σ)

/-- **`σ ∈ G` acting on the base change `A ⊗[K] L`** (PROVEN 2026-07-30) —
`σ ⊗ 1`, which is a ring map because `σ` is `K`-linear.

Stated as a bare `AlgHom` rather than as a `MulSemiringAction P.G (A ⊗[K] L)`
instance on purpose: the group structure is never used downstream (see
`isDomain_of_minimalPrimes_transitive_family`), and assembling it would cost
the functoriality of `Algebra.TensorProduct.map` for no gain. -/
noncomputable def Gamma1GITPresentation.tensorAlgHomA {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L]
    (σ : P.G) :
    letI := P.commRing_A; letI := P.algebraA; letI := P.group_G; letI := P.action_GA;
    TensorProduct K P.A L →ₐ[K] TensorProduct K P.A L :=
  letI := P.commRing_A
  letI := P.algebraA
  letI := P.group_G
  letI := P.action_GA
  Algebra.TensorProduct.map (P.algHomA σ) (AlgHom.id K L)

/-- **`(σ ⊗ 1)(a ⊗ l) = σa ⊗ l`** (PROVEN 2026-07-30, definitionally). -/
theorem Gamma1GITPresentation.tensorAlgHomA_tmul {N : ℕ} {K : Type} [Field K]
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L]
    (σ : P.G) :
    letI := P.commRing_A; letI := P.algebraA; letI := P.group_G; letI := P.action_GA;
    ∀ (a : P.A) (l : L),
      P.tensorAlgHomA L σ (a ⊗ₜ[K] l) = (MulSemiringAction.toRingHom P.G P.A σ a) ⊗ₜ[K] l := by
  letI := P.commRing_A
  letI := P.algebraA
  letI := P.group_G
  letI := P.action_GA
  intro a l
  rfl

/-! #### `minimalPrimes` transported along a ring isomorphism

Three lines of general order theory, needed only to read the base-changed
leaf below at `L := K`.  `Ideal.comap` along a ring isomorphism is an order
isomorphism on ideals preserving `IsPrime` in both directions, so
`Minimal Ideal.IsPrime` transports; `minimalPrimes_eq_minimals` is the
bridge to `minimalPrimes`.  GENERAL COMMUTATIVE ALGEBRA: it belongs in
`Fermat/FLT/Mathlib/RingTheory/`, and lives here only because it has a
single consumer. -/

/-- **`comap e.symm ∘ comap e = id` on ideals** (PROVEN 2026-07-30). -/
theorem comap_comap_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal S) :
    Ideal.comap (e.symm : S →+* R) (Ideal.comap (e : R →+* S) I) = I :=
  Ideal.ext fun x => by
    rw [Ideal.mem_comap, Ideal.mem_comap]
    simp

/-- **`comap e ∘ comap e.symm = id` on ideals** (PROVEN 2026-07-30). -/
theorem comap_comap_ringEquiv' {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (J : Ideal R) :
    Ideal.comap (e : R →+* S) (Ideal.comap (e.symm : S →+* R) J) = J :=
  Ideal.ext fun x => by
    rw [Ideal.mem_comap, Ideal.mem_comap]
    simp

/-- **`comap` along a ring isomorphism is injective** (PROVEN 2026-07-30). -/
theorem comap_injective_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Function.Injective (fun I : Ideal S => Ideal.comap (e : R →+* S) I) := by
  intro I J h
  rw [← comap_comap_ringEquiv e I, ← comap_comap_ringEquiv e J]
  exact congrArg _ h

/-- **A minimal prime pulls back to a minimal prime along a ring
isomorphism** (PROVEN 2026-07-30). -/
theorem mem_minimalPrimes_comap_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    {p : Ideal S} (hp : p ∈ minimalPrimes S) :
    Ideal.comap (e : R →+* S) p ∈ minimalPrimes R := by
  rw [minimalPrimes_eq_minimals] at hp ⊢
  haveI := hp.prop
  refine ⟨Ideal.comap_isPrime _ _, ?_⟩
  intro q hq hle
  haveI := hq
  have h1 : Ideal.comap (e.symm : S →+* R) q ≤ p := by
    have := Ideal.comap_mono (f := (e.symm : S →+* R)) hle
    rwa [comap_comap_ringEquiv e p] at this
  have h2 : p ≤ Ideal.comap (e.symm : S →+* R) q := hp.le_of_le (Ideal.comap_isPrime _ _) h1
  have := Ideal.comap_mono (f := (e : R →+* S)) h2
  rwa [comap_comap_ringEquiv' e q] at this

/-- **The deck group permutes the components of EVERY BASE CHANGE of the
rigidified moduli scheme transitively** (sorry leaf, NEW 2026-07-30) —
Deligne–Rapoport IV.5.5, Katz–Mazur (8.1.1), and after this cut the ONLY
open modular input to the geometric irreducibility of `Y_1(N)`.

**What this replaces, and why the count goes DOWN.**  It replaces TWO
leaves, both of which are now theorems over it:

| former leaf | how it is now proved |
|---|---|
| `transitiveMinimalPrimes_of_gamma1GITPresentation` (immediately below) | this leaf at `L := K`, transported along `Algebra.TensorProduct.rid` |
| `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation` (far below) | this leaf plus `isDomain_of_minimalPrimes_transitive_family`, `smoothCurve_A_of_gamma1GITPresentation` and `nontrivial_A_of_gamma1GITPresentation` |

So this is a MERGE, not a decomposition: two open leaves become one, and
the survivor is the statement Deligne–Rapoport actually prove.  That is
also why it is strictly STRONGER than the leaf below rather than a
reformulation of it — `A ⊗[K] L` genuinely has more components than `A`
(over `K(ζ_n)` the rigidified curve splits into `φ(n)` pieces where over
`K` it may be irreducible), and it is exactly those components that IV.5.5
is about.  A prover of the untensored statement was already having to run
the geometric argument over `K̄`, so nothing extra is being asked for; what
changes is that the extra strength is now recorded instead of thrown away.

TRUE and classical, and this is the form of IV.5.5 that survives base
change to an arbitrary `K`.  The geometric components of
`𝔐([Γ₁(N)], [Γ(n)])` are indexed by the value of the Weil pairing on the
level-`n` structure, i.e. by the primitive `n`-th roots of unity, and
`G = GL₂(ℤ/n)` moves that value through `det`, which is SURJECTIVE onto
`(ℤ/n)ˣ` — so the action on the geometric components is transitive.  Over a
general `L` the components of `Spec (A ⊗[K] L)` are the `Gal(L̄/L)`-orbits
of the geometric ones, and `G` acts `L`-linearly, hence commutes with that
Galois action and stays transitive on the orbits.  This is why the
base-changed form costs a prover nothing beyond the untensored one.

**FAITHFULNESS.**  The base-change axis introduces no new vacuity and no new
strength beyond the components: `L` is an arbitrary field extension, at
`L := K` the statement is the old leaf verbatim (via
`Algebra.TensorProduct.rid`), and `A ⊗[K] L` is nontrivial and reduced for
every such `L` — nontrivial because `L` is a faithfully flat `K`-module and
`A` is nontrivial (`nontrivial_A_of_gamma1GITPresentation`), reduced because
`Algebra.Smooth K A` base changes (`smoothCurve_A_of_gamma1GITPresentation`
plus `Algebra.Smooth.isReduced_of_isField`).  So `minimalPrimes (A ⊗[K] L)`
is a nonempty set of genuine components in every instance and the
quantifiers are never vacuous.  The transitivity clause is phrased with
`Ideal.comap` rather than a pointwise ideal action for the same reason as on
the leaf below: it is the form the proof consumes and it needs no
`Pointwise` scope.

The hypotheses are REQUIRED for the same reasons as on the leaf below: at
`N = 0`, or at `char K ∣ N`, the moduli problem is not representable by a
nonempty smooth scheme and `minimalPrimes (A ⊗[K] L)` is not the component
set of anything.

**The ROUTE AUDIT is on the leaf immediately below** and applies verbatim
here, because it is an audit of the transitivity CONTENT, which is what
moved: both routes it closes (the mathlib invariant-theory route, which is
circular with the only consumer; and the component-algebra route, which
needs the cyclotomic datum as STRUCTURE) are insensitive to whether the
statement is read over `K` or over `L`.  The audit's recommendation —
carry the level-`n` torsor and its `det`-equivariant Weil pairing as a
FIELD of `Gamma1Rigidification` / `Gamma1GITPresentation` — is the
recommended route for THIS leaf too, and if anything it is more natural
here, since a pairing valued in `μ_n` is a statement about a base change. -/
theorem transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K)))
    (L : Type) [Field L] [Algebra K L] :
    letI := P.commRing_A; letI := P.algebraA; letI := P.group_G; letI := P.action_GA;
    ∀ p ∈ minimalPrimes (TensorProduct K P.A L),
      ∀ q ∈ minimalPrimes (TensorProduct K P.A L),
        ∃ σ : P.G, Ideal.comap (P.tensorAlgHomA L σ).toRingHom p = q :=
  sorry

/-- **The deck group permutes the components of the rigidified moduli
scheme transitively** (**PROVEN 2026-07-30** over
`transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation` above, at
`L := K`; a sorry leaf from 2026-07-28, when it was cut out of
`geometricComponents_of_gamma1GITPresentation`) — Deligne–Rapoport
IV.5.5, Katz–Mazur (8.1.1).

**The statement is unchanged and no consumer moved.**  What happened is
that the base-changed form of the same sentence had to be opened anyway,
for `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation`, and it
IMPLIES this one: `A ⊗[K] K ≅ A` as `K`-algebras `G`-equivariantly
(`Algebra.TensorProduct.rid`), `Ideal.comap` along that isomorphism is an
order isomorphism carrying minimal primes to minimal primes
(`mem_minimalPrimes_comap_ringEquiv`), and it intertwines `σ ⊗ 1` with `σ`
because `σ` is `K`-linear (`Gamma1GITPresentation.smul_algebraMap_A`).  So
rather than leave two leaves stating one fact at two generalities, this one
is derived and the frontier carries only the stronger.

**The ROUTE AUDIT below is RETAINED deliberately** and is about the leaf
above, not about this declaration: it records what a prover of the
transitivity content must not waste a cycle on, and that obligation moved
upward without changing.

TRUE and classical, and this is the form of IV.5.5 that survives base
change to an arbitrary `K`.  The geometric components of
`𝔐([Γ₁(N)], [Γ(n)])` are indexed by the value of the Weil pairing on the
level-`n` structure, i.e. by the primitive `n`-th roots of unity, and
`G = GL₂(ℤ/n)` moves that value through `det`, which is SURJECTIVE onto
`(ℤ/n)ˣ` — so the action on components, equivalently on
`minimalPrimes A`, is transitive.

**Why this rather than `IsDomain A`.**  `isDomain_of_gamma0Atlas`'s
docstring proposes folding `IsDomain A` into the presentation and
finishing with `Function.Injective.isDomain`.  Over `ℚ` that is right.
Over a general `K` it is **FALSE**: as soon as `ζ_n ∈ K` the scheme
`𝔐([Γ₁(N)], [Γ(n)])` has `φ(n)` components and `A` is not a domain.
What survives is precisely this leaf, and
`isDomain_of_minimalPrimes_transitive` converts it into `IsDomain B`.

The transitivity clause is phrased with `Ideal.comap` rather than a
pointwise ideal action because that is the form the proof consumes and
it needs no `Pointwise` scope: `q = comap σ p` says `x ∈ q ↔ σ • x ∈ p`.

## ROUTE AUDIT (2026-07-28) — two routes CLOSED, and how to refute each

The two ring-level cuts that suggest themselves both fail, for reasons
that are cheap to re-check; a prover should not spend a cycle
rediscovering them.

**(1) The mathlib invariant-theory route is CIRCULAR with the only
consumer.**  Mathlib has exactly the transitivity statement one wants —
`Algebra.IsInvariant.exists_smul_of_under_eq`
(`Mathlib/RingTheory/Invariant/Basic.lean`): under `Algebra.IsInvariant`,
`Finite G` and `SMulCommClass`, `G` is transitive on the primes of `A`
lying over a FIXED prime of `B`.  `Gamma1GITPresentation` carries every
one of those hypotheses, so the leaf reduces to

    all `p ∈ minimalPrimes A` have the same `Ideal.under B p`.

That residue is not a smaller leaf — it is EQUIVALENT to `IsDomain B`,
which is what this leaf exists to prove.  Indeed, if the common value is
`q` then `q = ⋂_{p} (p ∩ B) = (⋂_{p} p) ∩ B = 0` (`A` reduced, so
`⋂ minimalPrimes A = nilradical A = 0`), so `⊥` is prime in `B`;
conversely `isDomain_of_minimalPrimes_transitive` runs the implication
back.  Taking this route therefore deletes the cut instead of advancing
it, and `isDomain_invariants_of_gamma1GITPresentation` would become a
cycle.  *Refuting check*: exhibit a hypothesis strictly weaker than
`IsDomain B` from which `Algebra.IsInvariant.exists_smul_of_under_eq`
still gives the conclusion.

(Useful all the same, and free: `Algebra.IsInvariant.isIntegral` gives
`Algebra.IsIntegral B A` for this `P` with no extra hypotheses.)

**(2) The component-algebra route needs the cyclotomic datum as
STRUCTURE, not as an existential.**  The natural transcription of the
paragraph above is: a `G`-equivariant `ι : C →+* A` from the algebra of
"constants", inducing an equivariant bijection
`minimalPrimes A ≃ minimalPrimes C`, with `G` transitive downstairs.
Written as a bare `∃ C`, it is discharged by `C := A`, `ι := id`, and
buys nothing.  Written with `C` pinned as a finite `K`-algebra
(`Module.Finite K C`, i.e. `Spec C` the étale algebra of components) it
does carry content — but it is then STRICTLY STRONGER than this leaf and
FALSE for a general reduced `A` with transitive `G`:

> `A = K[x, y]/(xy)`, `G = ℤ/2` swapping `x` and `y`.  `A` is reduced and
> nontrivial, `minimalPrimes A = {(x), (y)}` and `σ` swaps them, so the
> conclusion of this leaf HOLDS.  But any `C` as above would have two
> distinct minimal primes and be Artinian, hence would contain an
> idempotent `e` lying in one and not the other; `ι e` would then be a
> nontrivial idempotent of the CONNECTED ring `A`, and there is none.

So the component algebra exists only once `A` is known to be normal —
i.e. only downstream of reducedness of `A` strengthened to smoothness, or
with the Weil-pairing map carried as a
FIELD of `Gamma1Rigidification` / `Gamma1GITPresentation` (the level-`n`
torsor and its `det`-equivariant pairing, which is what Katz–Mazur
(8.1.1) actually constructs).

**UPDATE 2026-07-28 — the smoothness half of that precondition is now IN
THE FILE.**  When this audit was written, the only reducedness statement
available was `isReduced_A_of_gamma1GITPresentation`, and "strengthened to
smoothness" named something that did not exist.  It does now:
`smoothCurve_A_of_gamma1GITPresentation` states `Algebra.Smooth K A`
(together with `ringKrullDim A = 1`), so a prover attacking THIS leaf may
write

    haveI := (smoothCurve_A_of_gamma1GITPresentation hN hchar P).1

and work with a smooth — hence normal — `A`.  That does not by itself close
this leaf, and the audit's two refutations above stand unchanged: the
mathlib invariant-theory route is still circular, and the bare `∃ C` form is
still discharged by `C := A`.  What it changes is that the *normality*
precondition of the component-algebra route is no longer a missing
statement, so that route is now worth re-examining rather than being ruled
out on availability grounds.  It is recorded here as an axis this audit did
NOT search: every route considered above was ring-level and normality-free.  That structural repair is the recommended
route, and it is the same shape as the `coequalises` field: a clause the
construction supplies for free and that no abstract presentation implies.
*Refuting check*: produce a finite `K`-subalgebra of the above `A`
separating `(x)` from `(y)`.

The hypotheses are REQUIRED: at `N = 0`, or at `char K ∣ N`, the moduli
problem is not representable by a nonempty smooth scheme and
`minimalPrimes A` is not the component set of anything. -/
theorem transitiveMinimalPrimes_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.group_G; letI := P.action_GA;
    ∀ p ∈ minimalPrimes P.A, ∀ q ∈ minimalPrimes P.A,
      ∃ σ : P.G, Ideal.comap (MulSemiringAction.toRingHom P.G P.A σ) p = q := by
  letI := P.commRing_A
  letI := P.algebraA
  letI := P.group_G
  letI := P.action_GA
  intro p hp q hq
  set e : TensorProduct K P.A K ≃+* P.A :=
    (Algebra.TensorProduct.rid K K P.A).toRingEquiv with he
  obtain ⟨σ, hσ⟩ := transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation hN hchar P K
    (Ideal.comap (e : TensorProduct K P.A K →+* P.A) p)
    (mem_minimalPrimes_comap_ringEquiv e hp)
    (Ideal.comap (e : TensorProduct K P.A K →+* P.A) q)
    (mem_minimalPrimes_comap_ringEquiv e hq)
  -- `e` intertwines `σ ⊗ 1` with `σ`, because `σ` is `K`-linear
  have hpt : ∀ z : TensorProduct K P.A K,
      e (P.tensorAlgHomA K σ z) = MulSemiringAction.toRingHom P.G P.A σ (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
        rw [P.tensorAlgHomA_tmul K σ]
        show (Algebra.TensorProduct.rid K K P.A) ((σ • a) ⊗ₜ[K] c) =
          σ • ((Algebra.TensorProduct.rid K K P.A) (a ⊗ₜ[K] c))
        rw [Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.rid_tmul,
          Algebra.smul_def, Algebra.smul_def, smul_mul',
          show σ • (algebraMap K P.A) c = (algebraMap K P.A) c from P.smul_algebraMap_A σ c]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hint : (e : TensorProduct K P.A K →+* P.A).comp (P.tensorAlgHomA K σ).toRingHom =
      (MulSemiringAction.toRingHom P.G P.A σ).comp (e : TensorProduct K P.A K →+* P.A) :=
    RingHom.ext hpt
  refine ⟨σ, comap_injective_ringEquiv e ?_⟩
  show Ideal.comap (e : TensorProduct K P.A K →+* P.A)
      (Ideal.comap (MulSemiringAction.toRingHom P.G P.A σ) p) =
    Ideal.comap (e : TensorProduct K P.A K →+* P.A) q
  rw [Ideal.comap_comap, ← hint, ← Ideal.comap_comap, hσ]

/-- **The rigidified moduli scheme is nonempty and reduced, and its deck
group permutes its components transitively** (PROVEN 2026-07-28 over the
three leaves above; formerly a sorry leaf itself, cut 2026-07-27 out of
`isDomain_of_gamma1GITPresentation`) — Katz–Mazur (8.1.1) plus
Deligne–Rapoport IV.5.5.

The three conjuncts were split because they are three DIFFERENT classical
inputs with three different difficulties, and bundling them made the leaf
undispatchable:

| conjunct | where it went | theory |
|---|---|---|
| `Nontrivial A` | PROVEN over `exists_gamma1Datum_fieldExtension` | an elliptic curve with a point of exact order `N` over *some* field — no modular curves at all |
| `IsReduced A` | `isReduced_A_of_gamma1GITPresentation` | Katz–Mazur 8.2.1, smoothness |
| transitivity | `transitiveMinimalPrimes_of_gamma1GITPresentation` | Deligne–Rapoport IV.5.5, the `det`-surjectivity |

Each split is a CONJUNCT of the original statement, so no faithfulness
question arises: the three together are the original, verbatim.  The
ROUTE AUDIT on the transitivity leaf records the two ring-level cuts that
do NOT work below it. -/
theorem geometricComponents_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.group_G; letI := P.action_GA;
    Nontrivial P.A ∧ IsReduced P.A ∧
      ∀ p ∈ minimalPrimes P.A, ∀ q ∈ minimalPrimes P.A,
        ∃ σ : P.G, Ideal.comap (MulSemiringAction.toRingHom P.G P.A σ) p = q :=
  ⟨nontrivial_A_of_gamma1GITPresentation hN hchar P,
    isReduced_A_of_gamma1GITPresentation hN hchar P,
    transitiveMinimalPrimes_of_gamma1GITPresentation hN hchar P⟩

/-- **The ring of invariants is a DOMAIN** (PROVEN 2026-07-27 over
`geometricComponents_of_gamma1GITPresentation` and
`isDomain_of_minimalPrimes_transitive`).

This is the `Γ₁` analogue of `isDomain_of_gamma0GITPresentation`, and
unlike that one it is a theorem rather than a leaf, because the modular
input has been pushed one step further down to the components of
`Spec A`. -/
theorem isDomain_invariants_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N) {K : Type} [Field K]
    (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; IsDomain P.B := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.group_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  obtain ⟨hnt, hred, htrans⟩ := geometricComponents_of_gamma1GITPresentation hN hchar P
  haveI := hnt
  haveI := hred
  exact isDomain_of_minimalPrimes_transitive P.G P.injective_algebraMap htrans

/-- **The ring of global functions of the coarse space is a DOMAIN**
(PROVEN 2026-07-27 over `isDomain_invariants_of_gamma1GITPresentation`;
formerly a sorry leaf) — the integrality half of Katz–Mazur (8.1.1).

TRUE and classical: `Y_1(N)` is geometrically irreducible over any field
in which `N` is invertible (Deligne–Rapoport IV.5.5 — the subgroup
`{[[1, b], [0, d]]}` of `GL₂(ℤ/N)` has surjective determinant), so its
coordinate ring `B = A^G` is a domain.

The proof is `Scheme.ΓSpecIso` alone, exactly as the previous version of
this docstring predicted: the coarse space here IS `Spec B`, so its ring
of global sections is `B` up to a ring isomorphism.  Unlike
`isDomain_of_gamma0Atlas` no transport along an atlas comparison is
needed, because the statement is already at the presentation. -/
theorem isDomain_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N) {K : Type} [Field K]
    (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    IsDomain Γ(P.toGamma1Atlas.Y, ⊤) := by
  letI := P.commRing_B
  haveI : IsDomain P.B := isDomain_invariants_of_gamma1GITPresentation hN hchar P
  show IsDomain Γ(Spec (CommRingCat.of P.B), ⊤)
  exact MulEquiv.isDomain P.B
    (Scheme.ΓSpecIso (CommRingCat.of P.B)).commRingCatIsoToRingEquiv.toMulEquiv

/-- **The coarse ring `B = A^G` is of FINITE PRESENTATION over `K`** — Noether's
theorem on invariants (PROVEN 2026-07-30 over
`smoothCurve_A_of_gamma1GITPresentation`).

`Algebra.Smooth` unfolds to `FormallySmooth` plus `FinitePresentation`, and this
is the second conjunct, which is NOT a leaf: `smoothCurve_A_of_gamma1GITPresentation`
gives `Algebra.Smooth K A` hence `Algebra.FiniteType K A`,
`Algebra.IsInvariant.finiteType_of_isInvariant`
(`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`, PROVEN — Artin–Tate)
descends finite type to `B = A^G` from `Finite G` and `P.injective_algebraMap`
alone, and over the Noetherian base `K` finite type and finite presentation
coincide (`Algebra.FinitePresentation.of_finiteType`).

The one thing that had to be supplied for this is the scalar tower
`IsScalarTower K B A`, recorded above as `Gamma1GITPresentation.isScalarTower`.
It is not a field of the structure and it was documented as unavailable; it is
in fact forced by `classify_dM`.

No domain hypothesis, no smoothness of `B`, and nothing modular beyond the one
appeal to 8.2.1 on `A`. -/
theorem finitePresentation_invariants_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB; Algebra.FinitePresentation K P.B := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.algebraA
  letI := P.algebraB
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  letI := P.isInvariant_BAG
  haveI := P.isScalarTower
  haveI : Algebra.Smooth K P.A := (smoothCurve_A_of_gamma1GITPresentation hN hchar P).1
  haveI : Algebra.FiniteType K P.A := Algebra.FinitePresentation.of_finiteType.2 inferInstance
  haveI : Algebra.FiniteType K P.B :=
    Algebra.IsInvariant.finiteType_of_isInvariant K P.B P.A P.G P.injective_algebraMap
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance

/-- **The coarse ring `B = A^G` is FORMALLY SMOOTH over `K`** (sorry leaf, cut
2026-07-30 out of `smoothInvariants_of_gamma1GITPresentation`, which is now a
THEOREM over it and the finite-presentation half above) — Deligne–Rapoport
III.1, Katz–Mazur 8.2.1.

`Algebra.Smooth` unfolds to `FormallySmooth` plus `FinitePresentation`.  The
finite-presentation conjunct is Noether's theorem on invariants and is PROVEN
above, so THIS is the whole residue: the infinitesimal lifting property of
`Spec B` over `K`.

Everything the previous docstring of `smoothInvariants_of_gamma1GITPresentation`
recorded about the obstruction applies verbatim to this conjunct and to this
conjunct only — Stacks `02VL` (descent of smoothness along a surjective flat
finitely-presented cover) together with freeness of the `G`-action, which is not
a field of `Gamma1GITPresentation` and does not follow from the fields that are
there.  See that docstring below for the route audit and for why the
perfect-field shortcut does not apply. -/
theorem formallySmoothInvariants_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB; Algebra.FormallySmooth K P.B :=
  sorry

/-- **The coarse ring `B = A^G` is a SMOOTH `K`-algebra** (**PROVEN 2026-07-30**
over `formallySmoothInvariants_of_gamma1GITPresentation` and
`finitePresentation_invariants_of_gamma1GITPresentation`; opened as a sorry leaf
2026-07-28 as the residue of `smooth_coarseRing_of_gamma1GITPresentation` after
its Krull-dimension conjunct was discharged onto `A`) —
Deligne–Rapoport III.1, Katz–Mazur 8.2.1.

**The statement is unchanged**; what changed on 2026-07-30 is that
`Algebra.Smooth` was unfolded into its two conjuncts and the SECOND one paid
for.  `Algebra.FinitePresentation K B` is Noether's theorem on invariants, which
this tree already had — see the declaration two above — and only
`Algebra.FormallySmooth K B` remains open.

This is the HALF of the old `smooth_coarseRing_of_gamma1GITPresentation`
that survives the relocation of Katz–Mazur 8.2.1 onto the rigidified ring
`A` (`smoothCurve_A_of_gamma1GITPresentation`).  The dimension conjunct is
now a theorem — `ringKrullDim_eq_of_gamma1GITPresentation` transfers it from
`A` unconditionally — and this conjunct is not, for one specific reason.

## Exactly what stands between this and `Algebra.Smooth K A`

Descending smoothness from `A` to `B = A^G` is Stacks `02VL`: if
`X → Y` is surjective, flat and locally of finite presentation and `X → S`
is smooth, then `Y → S` is smooth.  Two things are missing, and they are
different in kind:

1. *Flatness of `Spec A → Spec B`.*  Classically this is free — for `N ≥ 4`
   the objects of `[Γ₁(N)]` have no nontrivial automorphisms, so `G` acts
   FREELY on `Spec A` and `Spec A → Spec B` is a finite étale `G`-torsor.
   But **freeness of the action is not a field of `Gamma1GITPresentation`**,
   and it does not follow from the fields that are there: the structure
   records `Algebra.IsInvariant B A G`, `Finite G` and injectivity, none of
   which sees the stabilisers.  So this would have to be added as a field
   (the same shape as the repair recommended on
   `transitiveMinimalPrimes_of_gamma1GITPresentation`) or as a hypothesis.
2. *Stacks `02VL` itself.*  Re-checked 2026-07-28: mathlib's smooth descent
   at this pin is `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`
   and `RingHom.Smooth.codescendsAlong_faithfullyFlat`
   (`Mathlib/RingTheory/Etale/Descent.lean`), which are
   `CodescendsAlong Smooth FaithfullyFlat` — descent along a faithfully flat
   base change of the SOURCE `K`, i.e. from `Smooth T (T ⊗[K] B)` to
   `Smooth K B`.  That is the wrong direction: it moves along the base, not
   along a cover of the target.  *The check that would refute this*: a lemma
   in `Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/Morphisms/`
   concluding `Smooth R B` from `Smooth R A` and flatness of `B → A`.

## The perfect-field shortcut does NOT apply, and this is why the leaf is real

Over a PERFECT `K` one could avoid `02VL` entirely: `A` smooth implies `A`
normal, invariants of a normal ring under a finite group are normal, a
one-dimensional normal Noetherian domain is regular, and over a perfect
field regular implies smooth.  Every step of that survives here EXCEPT the
last, and `K` is arbitrary by design — see the note at the foot of
`smooth_coarseRing_of_gamma1GITPresentation` and the quasi-elliptic
counterexample `y² = x³ + t` over `𝔽₃(t)` recorded on
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`.  Over an
imperfect `K` regular is strictly weaker than smooth, and closing that gap
needs `Frac B / K` separably generated — which is exactly what THIS
statement supplies to
`isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` (PROVEN
2026-07-30 over it), so it is not available here without circularity.

## FAITHFULNESS

`hchar` is load-bearing exactly as on the leaf it was split from: at
`char K ∣ N` the moduli problem is not smooth over `K`.  Unlike its former
partner conjunct this statement does NOT carry nonemptiness — the zero ring
is smooth over `K` — so it is not by itself enough for
`ringKrullDim B = 1`; that is supplied by
`smoothCurve_A_of_gamma1GITPresentation`, which is where nonemptiness now
lives. -/
theorem smoothInvariants_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB; Algebra.Smooth K P.B := by
  letI := P.commRing_B
  letI := P.algebraB
  exact { formallySmooth := formallySmoothInvariants_of_gamma1GITPresentation hN hchar P
          finitePresentation :=
            finitePresentation_invariants_of_gamma1GITPresentation hN hchar P }

/-- **The coarse ring `B = A^G` is a SMOOTH `K`-algebra of Krull dimension
one** (**PROVEN 2026-07-28** over `smoothInvariants_of_gamma1GITPresentation`,
`smoothCurve_A_of_gamma1GITPresentation` and
`ringKrullDim_eq_of_gamma1GITPresentation`; opened as a sorry leaf earlier
the same day) — Deligne–Rapoport III.1, Katz–Mazur 8.2.1.

This is the `Γ₁` analogue of `X0.lean`'s
`isRegularRing_coarseRing_of_gamma0GITPresentation`, with the ONE
difference that the whole `Γ₁` layer turns on: that statement concludes
`IsRegularRing B` and is consumed through a bridge carrying
`[PerfectField K]`, and here `K` is arbitrary, so the conclusion has to
be smoothness itself.

TRUE and classical, and one of the two genuinely modular geometric
inputs of this file.  `[Γ₁(N)]` is a smooth Deligne–Mumford stack of
relative dimension one over `ℤ[1/N]` (Katz–Mazur 8.2.1 proves that
`ℤ[1/N]`-smoothness directly, and it specialises to every field in which
`N` is invertible); for `N ≥ 4` it is moreover representable, so the
coarse space is the fine one and smoothness is immediate from 8.2.1.
At the level of the GIT presentation the same argument reads: `A` is a
smooth `K`-algebra of relative dimension one, and for `N ≥ 4` the action
of `G` on `Spec A` is free, so `Spec A → Spec B` is a finite étale
`G`-torsor and `Spec (A^G)` is smooth as well.

`Algebra.Smooth` unfolds to `FormallySmooth` plus `FinitePresentation`,
so the finite-type half of the classical statement ("Noether's theorem on
invariants") is inside it; over the Noetherian base `K` finite type and
finite presentation coincide.

## THE ROUTE FROM `A` — ITEM 2 IS NOW DONE, AND THE OLD NOTE WAS STALE

A prover who wants to push this one step further down, onto the
rigidified ring `A` where Katz–Mazur actually applies, needs three
things.  As of 2026-07-28 the first two EXIST and are used here; only the
third is genuinely missing, and it now blocks the smoothness conjunct
alone:

1. *`Algebra.FiniteType K B` from `Algebra.FiniteType K A`* — PROVEN, as
   `Algebra.IsInvariant.finiteType_of_isInvariant`
   (`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`).  It needs
   only `Finite G` and `P.injective_algebraMap`, no domain hypothesis.
2. *`ringKrullDim B = ringKrullDim A`* — **DONE**, as
   `ringKrullDim_eq_of_gamma1GITPresentation` above, and this docstring
   previously recorded it as BLOCKED.  The stale note read: "the pieces are
   `dimensionLEOne_of_isInvariant` and `ringKrullDim_eq_one_of_isInvariant`
   in the same file, but **both carry `[IsDomain S]`, i.e. `IsDomain A`,
   which is FALSE here**".  Both halves of that observation are true — the
   two lemmas were re-checked on 2026-07-28 and do carry `[IsDomain S]`,
   and `IsDomain A` is indeed false as soon as `ζ_n ∈ K` — but the
   conclusion did not follow, because those two lemmas are not the only
   route.  `ringKrullDim_eq_of_isIntegral_of_injective`
   (`SmoothConnectedCriteria.lean`, PROVEN) gives the transfer from
   `Algebra.IsIntegral B A` plus injectivity alone, with **no domain
   hypothesis anywhere**, and `Algebra.IsInvariant.isIntegral` supplies the
   integrality from `Finite G`.  It landed in the same release that wrote
   the note.
3. *Descent of smoothness along the `G`-torsor `Spec A → Spec B`* — this
   is the genuinely missing one, and it is now isolated in
   `formallySmoothInvariants_of_gamma1GITPresentation` above (2026-07-30;
   until that day the isolation was only as far as
   `smoothInvariants_of_gamma1GITPresentation`, which still bundled Noether's
   finiteness theorem with it), whose docstring records it in full together
   with the second missing ingredient (freeness of the `G`-action, which is
   not a field of the structure).
   It is Stacks `02VL` ("if `X → Y` is surjective, flat and locally of
   finite presentation and `X → S` is smooth, then `Y → S` is smooth"), and
   mathlib's descent at this pin goes the other way:
   `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`
   and `RingHom.Smooth.codescendsAlong_faithfullyFlat`
   (`Mathlib/RingTheory/Etale/Descent.lean`) descend along a faithfully
   flat extension of the BASE, not along a cover of the target — re-checked
   2026-07-28, still true.  *The check that would refute this*: a lemma in
   `Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/Morphisms/`
   concluding `Smooth R B` from `Smooth R A` and flatness of `B → A`.

So this declaration is now a THEOREM: item 2 discharges the dimension
conjunct onto `smoothCurve_A_of_gamma1GITPresentation`, and item 3 is the
whole of the remaining leaf.

## FAITHFULNESS

`hchar` is load-bearing: at `char K ∣ N` the moduli problem is not smooth
over `K` and `[Γ₁(N)]` degenerates.  `hN` is inherited rather than
strictly needed for the CONCLUSION — a coarse space of a tame quotient is
still a smooth curve — but it is what makes the free-action route above
available, and it is required by every consumer, so it is kept.

`ringKrullDim B = 1` needs `Spec B` NONEMPTY, and that nonemptiness now
lives on `smoothCurve_A_of_gamma1GITPresentation` rather than here: at
`N = 0`, or at `char K ∣ N`, `A` and hence `B` would be the zero ring and
the Krull dimension `⊥ ≠ 1`.  It remains the same input as
`Nontrivial P.A` in `geometricComponents_of_gamma1GITPresentation`, so the
leaves of this block still agree about when the moduli space exists, and
none of them is vacuous.

**No `[PerfectField K]` appears, and adding it would be the WRONG repair**
(recorded 2026-07-27, re-affirmed here).  The regular-ring bridge
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` carries
that hypothesis and it is load-bearing THERE — see the quasi-elliptic
counterexample `y² = x³ + t` over `𝔽₃(t)` in its docstring — but this
statement is TRUE over an imperfect `K`, because `Y_1(N)` over `K` is a
base change of `Y_1(N)` over the prime field and both `Algebra.Smooth`
and `ringKrullDim` of a geometrically integral curve survive it.  The
perfect-field bridge is the right tool for the `Γ₀` sibling (base `ℚ`)
and for `CurveCompactification.lean`, not for here. -/
theorem smooth_coarseRing_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB;
    Algebra.Smooth K P.B ∧ ringKrullDim P.B = (1 : ℕ) := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebraB
  refine ⟨smoothInvariants_of_gamma1GITPresentation hN hchar P, ?_⟩
  rw [← ringKrullDim_eq_of_gamma1GITPresentation P]
  exact (smoothCurve_A_of_gamma1GITPresentation hN hchar P).2

/-- **`B` is locally standard smooth of relative dimension `1` over `K`**
(**PROVEN 2026-07-28** over `smooth_coarseRing_of_gamma1GITPresentation`,
`isDomain_invariants_of_gamma1GITPresentation` and the release's shared
bridge `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`; opened
as a sorry leaf 2026-07-27) — Deligne–Rapoport III.1, Katz–Mazur 8.2, in
the ring-level form that the pin can actually express.

## The route, and why it is NOT the regular-ring one

`AlgebraicGeometry.smoothOfRelativeDimension_specMap_algebraMap_of_smooth`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`) is
the release's shared statement "the relative dimension of a smooth
affine variety is its Krull dimension", for a finite-type DOMAIN over an
ARBITRARY field:

    [Field K] [IsDomain B] [Algebra.Smooth K B] → ringKrullDim B = n →
      SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B)))

It carries **no `PerfectField` and no `IsRegularRing`** — those were both
consumed one level up, into
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`, when
that leaf was closed over Stacks `056S` on 2026-07-28.  That is exactly
what makes it usable here where `K` is arbitrary, and it is the reason
this declaration is a theorem rather than a leaf.

`HasRingHomProperty.Spec_iff` for the instance
`HasRingHomProperty (@SmoothOfRelativeDimension n)
(Locally (IsStandardSmoothOfRelativeDimension n))` converts the scheme
conclusion back into the ring statement asked for here; `IsDomain B`
comes from `isDomain_invariants_of_gamma1GITPresentation`, so the only
thing left to supply is `Algebra.Smooth K B` together with
`ringKrullDim B = 1`, which is the single leaf immediately above.

**The regular-ring bridge cannot be used here and must not be reached
for** (2026-07-27, and it is worth keeping the record): it carries
`[PerfectField K]`, load-bearing there, while this statement and
everything above it up to `exists_isCoarseModuliY1_isSmoothCurve`
quantifies over an ARBITRARY `K` with `char K ∤ N`.  Adding
`[PerfectField K]` would be a restatement reaching several declarations
with other owners, and it would be wrong anyway, since the statement IS
true over an imperfect `K` — `Y_1(N)` over `K` is a base change from the
prime field and `SmoothOfRelativeDimension` is stable under base change
(`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`). -/
theorem locallyStandardSmooth_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB;
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K P.B) := by
  letI := P.commRing_B
  letI := P.algebraB
  obtain ⟨hsm, hdim⟩ := smooth_coarseRing_of_gamma1GITPresentation hN hchar P
  haveI := hsm
  haveI : IsDomain P.B := isDomain_invariants_of_gamma1GITPresentation hN hchar P
  have h := smoothOfRelativeDimension_specMap_algebraMap_of_smooth K P.B 1 hdim
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)] at h
  exact h

/-- **The coarse space is smooth of relative dimension `1` over `K`**
(PROVEN 2026-07-27 over `locallyStandardSmooth_of_gamma1GITPresentation`;
formerly a sorry leaf) — Deligne–Rapoport III.1, Katz–Mazur 8.2.

The proof is `Gamma1GITPresentation.specMap_algebraMap` followed by
`HasRingHomProperty.Spec_iff`: the coarse space is `Spec B` and its
structure morphism is `Spec` of the `K`-algebra structure map, so
`SmoothOfRelativeDimension 1` on it IS
`Locally (IsStandardSmoothOfRelativeDimension 1)` on `K → B`. -/
theorem smoothOfRelativeDimension_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    SmoothOfRelativeDimension 1 P.toGamma1Atlas.str := by
  letI := P.commRing_B
  letI := P.algebraB
  show SmoothOfRelativeDimension 1 P.str
  rw [← P.specMap_algebraMap, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact locallyStandardSmooth_of_gamma1GITPresentation hN hchar P

/-- **Common denominators in `Frac B ⊗[K] L`** (PROVEN 2026-07-30).

Every element of `Frac B ⊗[K] L` becomes an element of the image of
`B ⊗[K] L` after multiplication by a single denominator `s ⊗ₜ 1` with
`s ∈ B⁰`.  This is the concrete form of "`Frac B ⊗[K] L` is a localization
of `B ⊗[K] L` at the image of `B⁰`", proved by the tensor-product induction
rather than through `Algebra.isLocalization_iff_isPushout`, which would
need an `Algebra (B ⊗[K] L) (Frac B ⊗[K] L)` instance and two scalar towers
to be introduced by hand first.

GENERAL COMMUTATIVE ALGEBRA, nothing modular: it belongs in
`Fermat/FLT/Mathlib/RingTheory/`, and lives here only because it has a
single consumer, immediately below.  Hoist it if a second one appears. -/
theorem exists_commonDenominator_tensorProduct {K B : Type} [Field K] [CommRing B]
    [Algebra K B] (L : Type) [Field L] [Algebra K L]
    (z : TensorProduct K (FractionRing B) L) :
    ∃ (s : nonZeroDivisors B) (w : TensorProduct K B L),
      ((algebraMap B (FractionRing B) (s : B)) ⊗ₜ[K] (1 : L)) * z =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom K B (FractionRing B))
          (AlgHom.id K L) w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, by simp⟩
  | tmul x l =>
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) x
      refine ⟨s, b ⊗ₜ[K] l, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul]
      congr 1
      exact IsLocalization.mk'_spec' _ b s
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨s₁, w₁, e₁⟩ := h₁
      obtain ⟨s₂, w₂, e₂⟩ := h₂
      refine ⟨s₁ * s₂, ((s₂ : B) ⊗ₜ[K] (1 : L)) * w₁ + ((s₁ : B) ⊗ₜ[K] (1 : L)) * w₂, ?_⟩
      have hu : ((algebraMap B (FractionRing B) ((s₁ * s₂ : nonZeroDivisors B) : B)) ⊗ₜ[K]
            (1 : L)) =
          ((algebraMap B (FractionRing B) ((s₁ : nonZeroDivisors B) : B)) ⊗ₜ[K] (1 : L)) *
            ((algebraMap B (FractionRing B) ((s₂ : nonZeroDivisors B) : B)) ⊗ₜ[K] (1 : L)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Submonoid.coe_mul, map_mul]
      rw [hu, map_add, map_mul, map_mul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, ← e₁, ← e₂]
      simp only [AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      ring

/-- **Passing `IsDomain` from `B ⊗[K] L` to `Frac B ⊗[K] L`** (PROVEN
2026-07-30).

`Frac B ⊗[K] L` is a localization of `B ⊗[K] L` (at the image of `B⁰`), and
a localization of a domain at a submonoid of nonzerodivisors is a domain.
The proof clears denominators with `exists_commonDenominator_tensorProduct`
and uses that `B ⊗[K] L → Frac B ⊗[K] L` is injective, `L` being flat over
the field `K`.

GENERAL COMMUTATIVE ALGEBRA — see the note on the previous declaration. -/
theorem isDomain_fractionRing_tensorProduct_of_isDomain_tensorProduct {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] (L : Type) [Field L] [Algebra K L]
    (h : IsDomain (TensorProduct K B L)) :
    IsDomain (TensorProduct K (FractionRing B) L) := by
  haveI := h
  set φ : TensorProduct K B L →ₐ[K] TensorProduct K (FractionRing B) L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K B (FractionRing B)) (AlgHom.id K L)
    with hφdef
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective B (FractionRing B))
  have hunit : ∀ s : nonZeroDivisors B,
      IsUnit (((algebraMap B (FractionRing B) (s : B)) ⊗ₜ[K] (1 : L)) :
        TensorProduct K (FractionRing B) L) := by
    intro s
    have h1 : IsUnit (algebraMap B (FractionRing B) (s : B)) := IsLocalization.map_units _ s
    have h2 := h1.map (Algebra.TensorProduct.includeLeft :
      FractionRing B →ₐ[K] TensorProduct K (FractionRing B) L)
    simpa using h2
  haveI : Nontrivial (TensorProduct K (FractionRing B) L) := hφ.nontrivial
  haveI : NoZeroDivisors (TensorProduct K (FractionRing B) L) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨s₁, w₁, e₁⟩ := exists_commonDenominator_tensorProduct L a
    obtain ⟨s₂, w₂, e₂⟩ := exists_commonDenominator_tensorProduct L b
    have hz : φ w₁ * φ w₂ = 0 := by
      rw [← e₁, ← e₂]
      calc _ = (((algebraMap B (FractionRing B) (s₁ : B)) ⊗ₜ[K] (1 : L)) *
            ((algebraMap B (FractionRing B) (s₂ : B)) ⊗ₜ[K] (1 : L))) * (a * b) := by ring
        _ = 0 := by rw [hab, mul_zero]
    have hw : w₁ * w₂ = 0 := hφ (by rw [map_mul, hz, map_zero])
    rcases mul_eq_zero.1 hw with h1 | h1
    · refine Or.inl ?_
      rw [h1, map_zero] at e₁
      exact (hunit s₁).mul_right_eq_zero.1 e₁
    · refine Or.inr ?_
      rw [h1, map_zero] at e₂
      exact (hunit s₂).mul_right_eq_zero.1 e₂
  exact NoZeroDivisors.to_isDomain _

set_option maxHeartbeats 1000000 in
/-- **`Spec (B ⊗[K] L)` is IRREDUCIBLE for every field extension `L/K`**
(**PROVEN 2026-07-30** over
`transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`,
`smoothCurve_A_of_gamma1GITPresentation` and
`nontrivial_A_of_gamma1GITPresentation`; opened as a sorry leaf earlier the
same day, cut out of
`isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation`, which is now
a THEOREM over it) — Deligne–Rapoport IV.5.5, and the whole of what that
leaf's docstring identified as its genuinely modular residue.

## HOW IT IS PROVED (2026-07-30), and why the frontier went DOWN by one

**The statement is unchanged.**  What changed is that the modular content was
recognised as the base change of a leaf that was ALREADY OPEN one screen up —
`transitiveMinimalPrimes_of_gamma1GITPresentation`, "the deck group permutes
the components of the rigidified moduli scheme transitively".  Both are
Deligne–Rapoport IV.5.5, one read on `B = A^G` after base change and one read
on `A` over `K`; the base-changed form of the transitivity statement implies
BOTH.  So the two leaves were merged into
`transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation` and this
declaration and that one are now theorems over it.

The route is exactly the one the untensored pair already used, run one level
up.  `Spec (A ⊗ L) → Spec (B ⊗ L)` is not needed at all; what is needed is:

1. `B ⊗ L → A ⊗ L` is INJECTIVE — `P.injective_algebraMap` plus flatness of
   `L` over the field `K` (`Module.Flat.rTensor_preserves_injective_linearMap`,
   the same idiom as `isDomain_fractionRing_tensorProduct_of_isDomain_tensorProduct`
   below).
2. `A ⊗ L` is NONTRIVIAL and REDUCED — nontrivial from
   `nontrivial_A_of_gamma1GITPresentation` and faithful flatness of `L`,
   reduced from `smoothCurve_A_of_gamma1GITPresentation` through
   `Algebra.Smooth.baseChange` and `Algebra.Smooth.isReduced_of_isField`.
   This is the same two-line step as `isReduced_A_of_gamma1GITPresentation`,
   after base change.
3. every `σ ∈ G` acts on `A ⊗ L` as `σ ⊗ 1` and FIXES the image of `B ⊗ L`
   pointwise — `Gamma1GITPresentation.tensorAlgHomA` and `smul_algebraMap`.
   Note step 3 is where `σ` has to be known `K`-LINEAR, which is
   `Gamma1GITPresentation.smul_algebraMap_A`, the ring-level reading of
   `strM_invariant`.
4. `isDomain_of_minimalPrimes_transitive_family` — the FAMILY form of
   `isDomain_of_minimalPrimes_transitive`, generalised for this consumer
   because `{σ ⊗ 1}` is not naturally a `MulSemiringAction` and the proof
   never needed one.

That gives `IsDomain (B ⊗[K] L)`, which is STRICTLY STRONGER than the
conclusion stated here; only the weaker form is stated, because that is what
`isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` below consumes
and restating it would move a consumer for no gain.  (The strengthening is
free and not an accident: reducedness of `B ⊗ L` is separately free from
smoothness of `B`, so the consumer recombines the two into the same domain
statement anyway.)

`(nilradical R).IsPrime` is exactly `IrreducibleSpace (PrimeSpectrum R)` —
`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`
(`Mathlib/RingTheory/Spectrum/Prime/Topology.lean`) — so this says the
geometric fibres of `Y_1(N)` are IRREDUCIBLE, with no reducedness content
whatever.  That is the `det`-surjectivity of IV.5.5: the subgroup of
`GL₂(ℤ/N)` attached to `[Γ₁(N)]` is `{[[1, b], [0, d]]}`, whose determinant
is `d`, so `det` is onto `(ℤ/N)ˣ`, the constants of `Y_1(N)` are `K`
itself, and no base change breaks the space into components.

## WHY THE CUT: reducedness was the OTHER half and it is FREE

The leaf this was cut from asked for `Frac B ⊗[K] L` to be a DOMAIN, i.e.
for `Frac B / K` to be a regular field extension, i.e. (MacLane) for `K` to
be algebraically closed in `Frac B` **and** `Frac B / K` to be separably
generated.  Its own docstring recorded — compiler-checked, 2026-07-28 —
that the second half costs nothing once
`smoothInvariants_of_gamma1GITPresentation` exists:
`Algebra.Smooth.baseChange` is an instance, so `Algebra.Smooth K B` gives
`Algebra.Smooth L (L ⊗[K] B)` by typeclass search, and the project's
`Algebra.Smooth.isReduced_of_isField` finishes.  Separability is paid for by
smoothness.

What was recorded but NOT done there was the corresponding restatement.  It
is done here, and without moving any consumer: the old leaf keeps its
statement verbatim and becomes a theorem over this one plus smoothness, so
`connectedSpace_tensorProduct_of_gamma1GITPresentation` and everything below
it are untouched.

The ring is `B ⊗[K] L` rather than `Frac B ⊗[K] L` because irreducibility
of `Spec` is insensitive to localization and `B` is where smoothness lives;
`isDomain_fractionRing_tensorProduct_of_isDomain_tensorProduct` above moves
the assembled domain statement across.

## FAITHFULNESS

`_hB` is kept, and for the same reason it was kept on the leaf this was cut
from: at `L := K` the statement reads `(nilradical (B ⊗[K] K)).IsPrime`,
which together with the free reducedness would give `IsDomain B` — the
content of `isDomain_invariants_of_gamma1GITPresentation`, which this
development obtains from the components of the RIGIDIFIED scheme, where
Katz–Mazur (8.1.1) actually leaves it.  Taking `_hB` as an INPUT confines
this leaf to the irreducibility content alone and makes the `L := K` case
trivial, so it cannot be used to re-derive its sibling.  That deliberate
asymmetry with the `Γ₀` side is preserved here rather than quietly dropped.

`hN` and `hchar` are REQUIRED: at `N = 0`, or at `char K ∣ N`, the moduli
problem is not representable by a nonempty smooth curve and `_hB` itself
fails. -/
theorem isPrime_nilradical_tensorProduct_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K)))
    (hB : letI := P.commRing_B; IsDomain P.B)
    (L : Type) [Field L] [Algebra K L] :
    letI := P.commRing_B; letI := P.algebraB;
    (nilradical (TensorProduct K P.B L)).IsPrime := by
  letI := P.commRing_A
  letI := P.commRing_B
  letI := P.algebra_BA
  letI := P.algebraA
  letI := P.algebraB
  letI := P.group_G
  letI := P.finite_G
  letI := P.action_GA
  letI := P.smulComm_GBA
  haveI := P.isScalarTower
  haveI := hB
  -- the rigidified ring, base changed: nontrivial and reduced
  haveI : Nontrivial P.A := nontrivial_A_of_gamma1GITPresentation hN hchar P
  haveI : Algebra.Smooth K P.A := (smoothCurve_A_of_gamma1GITPresentation hN hchar P).1
  haveI : IsReduced (TensorProduct K P.A L) := by
    haveI : IsReduced (TensorProduct K L P.A) :=
      Algebra.Smooth.isReduced_of_isField (R := L) (Field.toIsField L)
    exact isReduced_of_injective (Algebra.TensorProduct.comm K P.A L).toRingHom
      (Algebra.TensorProduct.comm K P.A L).injective
  haveI : Nontrivial (TensorProduct K P.A L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left (R := K) P.A L
      (FaithfulSMul.algebraMap_injective K L)
  -- `B ⊗ L → A ⊗ L`, injective because `L` is flat over the field `K`
  set φ : TensorProduct K P.B L →ₐ[K] TensorProduct K P.A L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K P.B P.A) (AlgHom.id K L) with hφdef
  letI : Algebra (TensorProduct K P.B L) (TensorProduct K P.A L) := φ.toRingHom.toAlgebra
  have hmap : (algebraMap (TensorProduct K P.B L) (TensorProduct K P.A L)) = φ.toRingHom := rfl
  have hφinj : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap _ P.injective_algebraMap
  -- each `σ ⊗ 1` fixes the image of `B ⊗ L` pointwise
  have hfix : ∀ (σ : P.G) (b : TensorProduct K P.B L),
      (P.tensorAlgHomA L σ).toRingHom
        (algebraMap (TensorProduct K P.B L) (TensorProduct K P.A L) b) =
      algebraMap (TensorProduct K P.B L) (TensorProduct K P.A L) b := by
    intro σ b
    rw [hmap]
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x l =>
        show P.tensorAlgHomA L σ (φ (x ⊗ₜ[K] l)) = φ (x ⊗ₜ[K] l)
        rw [hφdef, Algebra.TensorProduct.map_tmul, P.tensorAlgHomA_tmul L σ]
        congr 1
        show σ • (algebraMap P.B P.A x) = algebraMap P.B P.A x
        exact smul_algebraMap σ x
    | add a b ha hb => simp only [map_add, ha, hb]
  haveI : IsDomain (TensorProduct K P.B L) := by
    refine isDomain_of_minimalPrimes_transitive_family
      (fun σ : P.G => (P.tensorAlgHomA L σ).toRingHom) hfix ?_ ?_
    · rw [hmap]; exact hφinj
    · exact transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation hN hchar P L
  haveI : IsReduced (TensorProduct K P.B L) := inferInstance
  rw [nilradical_eq_zero]
  simpa using (Ideal.isPrime_bot : (⊥ : Ideal (TensorProduct K P.B L)).IsPrime)

/-- **`Frac B` is a REGULAR field extension of `K`** (**PROVEN 2026-07-30**
over `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation` and
`smoothInvariants_of_gamma1GITPresentation`; opened as a sorry leaf
2026-07-28, cut out of
`connectedSpace_tensorProduct_of_gamma1GITPresentation`) —
Deligne–Rapoport IV.5.5, in the function-field form.

**The statement is unchanged**; only the proof and the leaf beneath it are
new.  The 2026-07-28 docstring recorded a "recommended cut" and deliberately
did not perform it, on the ground that it would restate this leaf and move
its consumer at the same time.  Only the first half of that was true: the
cut can be made with the statement kept verbatim, by proving this
declaration from a SMALLER leaf.  That is what is done here, and
`connectedSpace_tensorProduct_of_gamma1GITPresentation` did not move.

## The proof, in three steps

1. `IsReduced (B ⊗[K] L)` — free from `smoothInvariants_of_gamma1GITPresentation`
   via the instance `Algebra.Smooth.baseChange` and the project's
   `Algebra.Smooth.isReduced_of_isField`.  This is the *separability* half of
   MacLane's criterion, and it costs nothing.
2. `IsDomain (B ⊗[K] L)` — step 1 plus the irreducibility leaf: a reduced
   ring whose nilradical is prime has `(⊥ : Ideal _)` prime.  This is the
   *primary* half, i.e. IV.5.5.
3. `IsDomain (Frac B ⊗[K] L)` —
   `isDomain_fractionRing_tensorProduct_of_isDomain_tensorProduct`, general
   commutative algebra (localization of a domain).

Everything modular is in step 2.

## The `Γ₀` sibling of this statement exists, and CANNOT be reused verbatim

`isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot`
(`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`, itself a sorry
leaf) has exactly this conclusion, with the modular input replaced by the
hypotheses `[IsIntegrallyClosed B]`, `∀ x : B, IsAlgebraic k x → x ∈ ⊥` —
and **`[CharZero k]`**.  The `CharZero` is what blocks reuse: this statement
quantifies over an arbitrary `K` with `char K ∤ N`, and the `𝔽_ℓ` case is
not decoration, it is what `exists_x1Compactification_finiteField` consumes.
Nor is that hypothesis lazy over there — its own faithfulness note gives the
counterexample (`k = 𝔽_p(u)`, `B = L = k(u^{1/p})`, where `L ⊗[k] L` carries
the nonzero nilpotent `u^{1/p} ⊗ 1 - 1 ⊗ u^{1/p}`).  Note that the route
taken here is precisely the char-free replacement that note asked for: the
separability input that `CharZero` was standing in for is supplied by
SMOOTHNESS of `B`, which the `Γ₁` presentation carries and the abstract
`Γ₀` statement does not.  That is the merge worth making if anyone
generalises that file.

**What is still missing from the pin, re-checked 2026-07-28.**  Mathlib has
the linear-disjointness theory (`Mathlib/FieldTheory/LinearDisjoint.lean`)
and the relative algebraic closure
(`Mathlib/FieldTheory/AlgebraicClosure.lean`), but no notion of a regular or
primary extension, and nothing relating `algebraicClosure` to base change.
It does have `IsGeometricallyReduced`
(`Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`) and, at scheme
level, `GeometricallyIntegral` with
`GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`
— so the DECOMPOSITION used here is supported even though the
field-theoretic packaging (`IsRegularExtension` / `IsPrimaryExtension`) is
absent.

## Why `IsDomain P.B` is a HYPOTHESIS here and not a consequence

Without `_hB` this statement would carry integrality a second time: at
`L := K` it reads `IsDomain (Frac B)`, which forces `IsDomain B`.  This
development obtains integrality from
`geometricComponents_of_gamma1GITPresentation` instead — from the components
of the RIGIDIFIED scheme, which is where Katz–Mazur (8.1.1) actually leaves
it.  The hypothesis is passed straight through to the leaf below, which
keeps it for the same reason.

The hypotheses are REQUIRED: at `N = 0` or at `char K ∣ N` the moduli
problem is not representable by a nonempty smooth curve, and `Frac B` is
then not a regular extension of `K` — indeed `_hB` itself fails. -/
theorem isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K)))
    (hB : letI := P.commRing_B; IsDomain P.B)
    (L : Type) [Field L] [Algebra K L] :
    letI := P.commRing_B; letI := P.algebraB;
    IsDomain (TensorProduct K (FractionRing P.B) L) := by
  letI := P.commRing_B
  letI := P.algebraB
  haveI := hB
  haveI : Algebra.Smooth K P.B := smoothInvariants_of_gamma1GITPresentation hN hchar P
  -- step 1: the separability half, free from smoothness
  haveI hred : IsReduced (TensorProduct K P.B L) := by
    haveI : IsReduced (TensorProduct K L P.B) :=
      Algebra.Smooth.isReduced_of_isField (R := L) (Field.toIsField L)
    exact isReduced_of_injective (Algebra.TensorProduct.comm K P.B L).toRingHom
      (Algebra.TensorProduct.comm K P.B L).injective
  -- step 2: the primary half, the modular leaf
  have hirr := isPrime_nilradical_tensorProduct_of_gamma1GITPresentation hN hchar P hB L
  rw [nilradical_eq_zero] at hirr
  haveI : Nontrivial (TensorProduct K P.B L) := by
    refine nontrivial_of_ne (1 : TensorProduct K P.B L) 0 fun e => hirr.ne_top ?_
    exact (Ideal.eq_top_iff_one _).2 (by simp [e])
  haveI : NoZeroDivisors (TensorProduct K P.B L) :=
    ⟨fun {a b} hab => by
      rcases hirr.mem_or_mem (show a * b ∈ (0 : Ideal (TensorProduct K P.B L)) by
        simpa using hab) with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)⟩
  -- step 3: localize
  exact isDomain_fractionRing_tensorProduct_of_isDomain_tensorProduct L
    (NoZeroDivisors.to_isDomain _)

/-- **`B ⊗[K] L` has connected spectrum for every field extension `L/K`**
(PROVEN 2026-07-28 over
`isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation`; opened as a
sorry leaf 2026-07-27 out of
`geometricallyConnected_of_gamma1GITPresentation`) — Deligne–Rapoport
IV.5.5, in the function-field form.

The proof is the two-step descent the `Γ₀` side had already released, reused
here rather than rewritten: `B ⊗[K] L` embeds into `Frac B ⊗[K] L` because
`L` is flat over the field `K` (`isDomain_tensorProduct_of_injective`,
`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`, PROVEN), the
latter is a domain by the leaf above, a subring of a domain is a domain, and
the spectrum of a domain is irreducible hence connected.  Nothing modular
happens in this step — all of it is in the leaf.

TRUE and classical, and the second genuinely modular geometric input.
The criterion is that the subgroup of `GL₂(ℤ/N)` attached to the level
structure surjects onto `(ℤ/N)ˣ` under `det`; for `[Γ₁(N)]` that subgroup
is `{[[1, b], [0, d]]}`, whose determinant is `d`, so `det` IS surjective
and the geometric fibres of `Y_1(N)` over `ℤ[1/N]` are connected.
Equivalently, and this is what the statement says: `K` is algebraically
closed in `Frac B`, so `Frac B / K` is a regular field extension and
`B ⊗[K] L` has no nontrivial idempotents for any field extension `L/K`.
That is the q-expansion-principle content of IV.5.5.

**This is where the parenthetical in `exists_x0Compactification`'s
docstring — "unlike for `Γ₁(N)` or `Γ(N)`" — is WRONG**, and the
correction is recorded at length on
`exists_isCoarseModuliY1_isSmoothCurve` below.  What genuinely splits at
level `Γ₁(N)` is the set of CUSPS, not the curve; `Γ(N)` is the case
where the curve itself splits, its field of constants being `ℚ(ζ_N)`.
Note this is exactly where the rigidified moduli scheme cannot be used
directly: `𝔐([Γ₁(N)], [Γ(n)])` is NOT geometrically connected for
`n ≥ 3`, and connectedness is recovered only after quotienting by
`G = GL₂(ℤ/n)` — the same fact that
`geometricComponents_of_gamma1GITPresentation` states for the minimal
primes.

## Why this is where the cut has to be made

The cheap criterion — connected plus a `k`-rational point, EGA IV
4.5.13 — is unavailable for a MATHEMATICAL reason, not a formal one:
`Y_1(N)(ℚ)` is empty for most `N`, and stating that emptiness is the
entire purpose of this module.  So the route must go through the
function field.  Mathlib still offers no sufficient criterion for
`GeometricallyConnected` itself — the string occurs 31 times, all in
`Geometrically/Connected.lean`, every one a consequence or a stability
property (re-checked 2026-07-27) — but the missing constructor for the
affine case now exists in this project, as
`AlgebraicGeometry.geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`,
PROVEN, written for the `Γ₀` sibling in the same release and reused
verbatim here), whose hypothesis this leaf states.

## Note on the asymmetry with the `Γ₀` side, which is PRESERVED

The `Γ₀` side states the STRONGER hypothesis
`isDomain_tensorCoarseRing_of_gamma0GITPresentation` — `B ⊗[ℚ] K` is a
DOMAIN — and goes through
`geometricallyConnected_specMap_algebraMap_of_forall_isDomain`.  That is
also true here (`Y_1(N)` is geometrically *irreducible*, not merely
connected), and stating THIS node as `IsDomain (B ⊗ L)` would additionally
re-prove `isDomain_of_gamma1GITPresentation` by taking `L := K`.  It is
deliberately NOT stated that way: integrality is obtained here from
`geometricComponents_of_gamma1GITPresentation`, i.e. from the components
of the RIGIDIFIED scheme, which is where Katz–Mazur (8.1.1) actually
leaves it.  Anyone who prefers the merged form should delete
`geometricComponents_of_gamma1GITPresentation` at the same time, not in
addition to it.

The 2026-07-28 decomposition respects that, and this is the one thing to
check before touching it: `IsDomain (B ⊗ L)` is now *derived* here, but it
is derived from `IsDomain B` — supplied by
`isDomain_invariants_of_gamma1GITPresentation`, hence ultimately by the
components leaf — TOGETHER WITH the new leaf, which takes `IsDomain P.B` as
a hypothesis precisely so that it cannot supply integrality itself.  So
integrality is still carried exactly once, and the two leaves below this
node have disjoint content: one says `Spec A` is reduced with `G`
transitive on its components, the other says `Frac B / K` is regular.

The hypotheses are REQUIRED: at `N = 0` or at `char K ∣ N` the coarse
space is empty, and `ConnectedSpace` carries nonemptiness. -/
theorem connectedSpace_tensorProduct_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K)))
    (L : Type) [Field L] [Algebra K L] :
    letI := P.commRing_B; letI := P.algebraB;
    ConnectedSpace (PrimeSpectrum (TensorProduct K P.B L)) := by
  letI := P.commRing_B
  letI := P.algebraB
  haveI hB : IsDomain P.B := isDomain_invariants_of_gamma1GITPresentation hN hchar P
  haveI : IsDomain (TensorProduct K (FractionRing P.B) L) :=
    isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation hN hchar P hB L
  haveI : IsDomain (TensorProduct K P.B L) :=
    isDomain_tensorProduct_of_injective K P.B (FractionRing P.B) L
      (IsScalarTower.toAlgHom K P.B (FractionRing P.B)) (IsFractionRing.injective P.B _)
  infer_instance

/-- **The coarse space is geometrically connected over `K`** (PROVEN
2026-07-27 over `connectedSpace_tensorProduct_of_gamma1GITPresentation`;
formerly a sorry leaf) — Deligne–Rapoport IV.5.5.

`Gamma1GITPresentation.specMap_algebraMap` puts the structure morphism
in the shape `Spec.map (ofHom (algebraMap K B))`, and the criterion
`geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace`
(`SmoothConnectedCriteria.lean`, PROVEN) does the rest.  An earlier
version of this proof inlined that criterion —
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` followed by
transport along `pullbackSpecIso K B L` — before the same release landed
it as a reusable lemma for the `Γ₀` side; the inline copy was deleted in
favour of the shared one. -/
theorem geometricallyConnected_of_gamma1GITPresentation {N : ℕ} (hN : 4 ≤ N)
    {K : Type} [Field K] (hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    GeometricallyConnected P.toGamma1Atlas.str := by
  letI := P.commRing_B
  letI := P.algebraB
  show GeometricallyConnected P.str
  rw [← P.specMap_algebraMap]
  exact geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace K P.B
    fun L _ _ => connectedSpace_tensorProduct_of_gamma1GITPresentation hN hchar P L

/-- **The affine integral Katz–Mazur model of `Y_1(N)`** — an atlas
together with the four geometric properties read off it.

The `Γ₁` analogue of `Gamma0AffineModel`.  It is stated over an arbitrary
atlas rather than over a presentation because that is the form its only
consumer, `exists_isCoarseModuliY1_isSmoothCurve`, uses: the consumer
never looks at `A`, `B` or `G` again, only at the coarse space and its
four properties.  Nothing here is a strengthening — the only inhabitant
this development builds comes from a presentation. -/
structure Gamma1AffineModel (N : ℕ) (S : Scheme.{0}) extends Gamma1Atlas N S where
  /-- the coarse space is affine — Katz–Mazur (8.1.1)'s `Spec (A^G)` -/
  isAffine : IsAffine toGamma1Atlas.Y
  /-- its ring of global functions is a domain -/
  isDomain : IsDomain Γ(toGamma1Atlas.Y, ⊤)
  /-- it is smooth of relative dimension `1` over the base -/
  smooth : SmoothOfRelativeDimension 1 toGamma1Atlas.str
  /-- and geometrically connected -/
  connected : GeometricallyConnected toGamma1Atlas.str

/-- **Existence of the affine integral Katz–Mazur model of `Y_1(N)` over
`K`** (PROVEN 2026-07-27).

The atlas half is `exists_gamma1GITPresentation` followed by
`Gamma1GITPresentation.toGamma1Atlas` — which is where
`specInvariants_universal` is consumed.  Of the four geometric fields,
`isAffine` is `AlgebraicGeometry.isAffine_Spec` because the presentation's
coarse space is literally `Spec (CommRingCat.of P.B)`, and the other
three are the three leaves above. -/
theorem exists_gamma1AffineModel (N : ℕ) (hN : 4 ≤ N) (K : Type) [Field K]
    (hchar : ¬ ringChar K ∣ N) :
    Nonempty (Gamma1AffineModel N (Spec (CommRingCat.of K))) :=
  (exists_gamma1GITPresentation N hN K hchar).map fun P =>
    { toGamma1Atlas := P.toGamma1Atlas
      isAffine := by
        letI := P.commRing_B
        show IsAffine (Spec (CommRingCat.of P.B))
        infer_instance
      isDomain := isDomain_of_gamma1GITPresentation hN hchar P
      smooth := smoothOfRelativeDimension_of_gamma1GITPresentation hN hchar P
      connected := geometricallyConnected_of_gamma1GITPresentation hN hchar P }

/-- **SOME coarse moduli space of the `Γ₁(N)`-problem is a geometrically
connected smooth curve over `K`, for `4 ≤ N` and `char K ∤ N`** (PROVEN
2026-07-27 over `exists_gamma1AffineModel`, by exhibiting the Katz–Mazur
model and reading the five properties off it; formerly a sorry leaf, and
still the ONLY place the modular content enters the existence of
`X_1(N)`, over BOTH base fields this file uses).

TRUE and classical.  For `N ≥ 4` the moduli problem `[Γ₁(N)]` is rigid —
a pair `(E, P)` with `P` of order `≥ 4` has no nontrivial automorphism —
so over a base where `N` is invertible it is representable, and `Y_1(N)`
is a smooth affine curve (Deligne–Rapoport III.1; Katz–Mazur 4.7.0 for
rigidity, 8.2 for smoothness).

**Geometric connectedness is the one clause that is not formal, and it
is TRUE for `Γ₁(N)` — this corrects the parenthetical in
`exists_x0Compactification`'s docstring** (`X0.lean`), which reads
"unlike for `Γ₁(N)` or `Γ(N)`".  The criterion is that the subgroup of
`GL₂(ℤ/N)` attached to the level structure surjects onto `(ℤ/N)ˣ` under
`det`.  For `[Γ₁(N)]` that subgroup is `{[[1, b], [0, d]]}`, whose
determinant is `d`, so `det` IS surjective and `Y_1(N)_ℚ` is
geometrically connected.  What genuinely does split over `ℚ(ζ_N)` at
level `Γ₁(N)` is the set of CUSPS, not the curve — see
`nonempty_cuspLocusX1`, where exactly `φ(N)/2` of the `28` cusps at
`N = 25` are rational.  `Γ(N)` is the case where the curve itself
splits, its field of constants being `ℚ(ζ_N)`.

**Stated over an arbitrary base field, deliberately**, following the
merge recorded at `exists_x0Compactification_field`: the `ℚ` case
(`exists_x1Compactification`) and the `𝔽_ℓ` case
(`exists_x1Compactification_finiteField`) differ only in `K`, and both
are one-line corollaries below.  `¬ ringChar K ∣ N` is exactly the
condition under which the `Γ₁(N)`-problem is smooth: at `char K = p ∣ N`
a point of exact order `N` acquires an infinitesimal part and the
`smooth` field of `IsX1Compactification` would be FALSE.  At `char K = 0`
the hypothesis reads `N ≠ 0`, which `hN` already gives.

The five conclusions were exactly the hypotheses of the general
compactification theorem `AlgebraicGeometry.exists_isSmoothCompactification`.
**Since 2026-07-28 the consumer calls the AFFINE variant**
`AlgebraicGeometry.exists_isSmoothCompactification_of_isAffine` (see the
sixth `IsAffine` clause below), whose hypotheses are the strict subset
`IsIntegral` and `SmoothOfRelativeDimension 1`: `QuasiCompact` and
`IsSeparated` come free from affineness and are no longer consumed here.
They are retained in the conjunction so that existing destructurings keep
working, and the general theorem itself has since been deleted as
free-floating together with the Nagata gluing induction it rested on.

Of the clauses still consumed, none is decoration: `IsIntegral` is what
makes the relative normalization integral, `SmoothOfRelativeDimension 1`
pins the relative dimension of the compactification, and
`GeometricallyConnected` is what
`geometricallyConnected_of_isSmoothCompactification` carries across.

**Why the statement is EXISTENTIAL, and this is the whole point of the
cut.**  Initiality (`IsCoarseModuliY1.exists_inverse`) makes all coarse
spaces of one level over one base isomorphic over that base, so it
suffices to exhibit ONE model.  The model exhibited is
`Gamma1AffineModel.Y`, and the five properties are read off it rather
than off the universal property — which is the form Deligne–Rapoport
III.1 and Katz–Mazur 8.2 state them in.  Three of the five are then NOT
modular: the model is affine over the affine `Spec K`, so `QuasiCompact`
and `IsSeparated` come from `isAffineHom_of_isAffine`, and `IsIntegral`
from `isIntegral_of_isAffine_of_isDomain`.

AXIS SEARCHED: the BASE-FIELD axis (taken — one node for `ℚ` and `𝔽_ℓ`
at once), the COMPACTIFICATION axis (taken — the whole
Nagata/normalization half is
`AlgebraicGeometry.exists_isSmoothCompactification_of_isAffine` and is not
modular),
and, as of 2026-07-27, the GIT axis: the `Γ₁` analogue of
`exists_gamma0AffineModel` is now built above, the previous "NOT
searched" note is DISCHARGED.  What remains open below this node is a
representability statement plus three properties of one curve, in place of
one statement asserting a curve with five properties exists — and (release
14, 2026-07-28) each of the three has itself been cut once more, so the
LIVE leaves are:

* representability — `exists_gamma1RigidifiedModuliScheme` and
  `isAffine_of_gamma1RigidifiedModuliScheme` (the two citation halves of
  `exists_gamma1RigidifiedModuli`, which has been PROVEN over them since
  2026-07-30), `exists_gamma1FullLevelStructure_cover`,
  `exists_gamma1DeckAction` (`exists_gamma1Rigidification` and
  `exists_gamma1GITPresentation` are PROVEN over them);
* the domain property — `exists_gamma1Datum_fieldExtension`,
  `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`
  (`transitiveMinimalPrimes_of_gamma1GITPresentation`,
  `geometricComponents_of_gamma1GITPresentation` and
  `isDomain_of_gamma1GITPresentation` are PROVEN over them, together with
  the smoothness row below: `isReduced_A_of_gamma1GITPresentation` was
  itself PROVEN on 2026-07-28 over `smoothCurve_A_of_gamma1GITPresentation`,
  so reducedness is no longer a separate citation);
* smoothness — `smoothCurve_A_of_gamma1GITPresentation` (Katz–Mazur 8.2.1
  on the rigidified ring, now the file's SINGLE statement of 8.2.1) and
  `formallySmoothInvariants_of_gamma1GITPresentation` (the torsor-descent
  residue; `smoothInvariants_of_gamma1GITPresentation` is PROVEN over it and
  Noether's finiteness theorem, 2026-07-30)
  — `smooth_coarseRing_of_gamma1GITPresentation`,
  `locallyStandardSmooth_of_gamma1GITPresentation` and
  `smoothOfRelativeDimension_of_gamma1GITPresentation` are PROVEN over them;
* geometric connectedness — the SAME leaf as the domain property since
  2026-07-30, `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`,
  over which `isPrime_nilradical_tensorProduct_of_gamma1GITPresentation`,
  `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` and in turn
  `connectedSpace_tensorProduct_of_gamma1GITPresentation` are PROVEN.

**Updated 2026-07-27**: the three properties were first stated at the
scheme level (`isDomain_of_gamma1GITPresentation`,
`smoothOfRelativeDimension_of_gamma1GITPresentation`,
`geometricallyConnected_of_gamma1GITPresentation`).  All three are now
PROVEN, over the ring-level leaves named above — so the open frontier
below this node is now entirely commutative algebra over `K` plus the
representability statements, with no scheme theory left in it.

**`IsAffine Y` is exported as a sixth clause** (2026-07-28), and it costs
nothing: it is `Gamma1AffineModel.isAffine`, i.e. Katz–Mazur's
`Y = Spec (A^G)`, which the exhibited model has carried all along (three of
the five clauses above are already *derived* from it) and which was simply
not being passed on.  It is what lets `exists_x1Compactification_field`
below call `AlgebraicGeometry.exists_isSmoothCompactification_of_isAffine`
instead of the general compactification theorem, and so avoid the open
Nagata gluing induction — the hardest leaf `CurveCompactification.lean`
ever carried — entirely.  With every consumer rewired, that general
theorem and its gluing induction had no consumer left and were deleted as
free-floating on 2026-07-28, removing the leaf outright.

Stating the affineness existentially loses nothing: initiality
(`IsCoarseModuliY1.exists_inverse`) makes every coarse space of the level
over the base isomorphic to the exhibited one, and `IsAffine` transports
along an isomorphism.  It is stated here rather than as a standalone
transport lemma only because `IsCoarseModuliY1.exists_inverse` is declared
further down this file; the `Γ₀` side, where the initiality lemma is
available early, does export it as
`isAffine_of_isCoarseModuliY0` (`X0.lean`). -/
theorem exists_isCoarseModuliY1_isSmoothCurve (N : ℕ) (hN : 4 ≤ N) (K : Type) [Field K]
    (hchar : ¬ ringChar K ∣ N) :
    ∃ (Y : Scheme.{0}) (strY : Y ⟶ Spec (CommRingCat.of K)) (_hc : IsCoarseModuliY1 N strY),
      IsAffine Y ∧ IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
        SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY := by
  obtain ⟨M⟩ := exists_gamma1AffineModel N hN K hchar
  haveI := M.isAffine
  haveI := M.isDomain
  haveI := M.smooth
  haveI := M.connected
  -- `Γ(Y, ⊤)` is a domain, hence nontrivial, so `Spec Γ(Y, ⊤) ≅ Y` is nonempty.
  haveI : Nonempty M.toGamma1Atlas.Y :=
    Nonempty.map M.toGamma1Atlas.Y.isoSpec.inv.base inferInstance
  haveI : IsIntegral M.toGamma1Atlas.Y :=
    isIntegral_of_isAffine_of_isDomain (X := M.toGamma1Atlas.Y)
  -- affine source over the affine `Spec K`: the structure morphism is affine,
  -- hence quasi-compact and separated.
  haveI : IsAffineHom M.toGamma1Atlas.str := inferInstance
  exact ⟨_, M.toGamma1Atlas.str, M.toGamma1Atlas.toIsCoarseModuliY1, M.isAffine,
    inferInstance, inferInstance, IsSeparated.of_isAffineHom _, inferInstance, inferInstance⟩

/-- **Existence of the compactified coarse moduli space `X_1(N)` over an
ARBITRARY perfect base field whose characteristic does not divide `N`**
(PROVEN 2026-07-27, over one modular leaf plus general curve theory).

TRUE and classical: `Y_1(N)` is a smooth affine curve over `K` and every
smooth curve over a perfect field has a smooth proper compactification
with finite complement; for `Y_1(N)` it is the modular curve `X_1(N)` of
Deligne–Rapoport, obtained directly as the coarse space of the moduli
problem of GENERALISED elliptic curves with `Γ₁(N)`-structure, the added
points being the cusps.

The proof is the two-step assembly `X0.lean` uses at
`exists_x0Compactification`, and only the first step is modular:

* `exists_isCoarseModuliY1_isSmoothCurve` supplies a coarse space
  together with the five properties the compactification theorem
  consumes;
* `AlgebraicGeometry.exists_isSmoothCompactification_of_isAffine` and
  `AlgebraicGeometry.geometricallyConnected_of_isSmoothCompactification`
  supply the compactification itself, from
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.  The
  AFFINE variant is used (2026-07-28), on the `IsAffine Y` clause the
  leaf above now exports: the general variant routes through the open
  Nagata gluing induction and the affine one does not.

Note that `connected` and `finite_compl` — the two fields of
`IsX1Compactification` beyond a bare compactification — come from the
general theory and not from anything modular: geometric connectedness is
inherited from `Y_1(N)` along a dense open immersion, and finiteness of
the cusp locus is finiteness of the complement of a dense open in an
irreducible curve.  Neither is assumed, which is what keeps this
interface from smuggling in a cusp count; see `exists_rationalCuspsX1`
for the count, which is a genuinely separate and still-open statement.

`PerfectField K` is needed only by the normalization step and holds at
both bases used here — `ℚ` by `PerfectField.ofCharZero`, `𝔽_ℓ` by
`PerfectField.ofFinite`. -/
theorem exists_x1Compactification_field (N : ℕ) (hN : 4 ≤ N) (K : Type) [Field K]
    [PerfectField K] (hchar : ¬ ringChar K ∣ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ Spec (CommRingCat.of K))
      (strY : Y ⟶ Spec (CommRingCat.of K)) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) := by
  obtain ⟨Y, strY, hc, haff, hint, -, -, hsmd, hconn⟩ :=
    exists_isCoarseModuliY1_isSmoothCurve N hN K hchar
  haveI := haff; haveI := hint; haveI := hsmd; haveI := hconn
  obtain ⟨X, strX, jY, hX⟩ := exists_isSmoothCompactification_of_isAffine (K := K) strY
  exact ⟨X, Y, strX, strY, jY,
    ⟨{ comm := hX.comm
       coarse := hc
       isOpen := hX.isOpenImmersion
       isProper := hX.isProper
       smooth := hX.smooth
       connected := geometricallyConnected_of_isSmoothCompactification hX
       finite_compl := hX.finite_compl }⟩⟩

/-- **Existence of the compactified coarse moduli space `X_1(N)` over
`ℚ`** (PROVEN 2026-07-27, as the characteristic-`0` case of
`exists_x1Compactification_field`; formerly a sorry node).

`ringChar ℚ = 0`, so the characteristic hypothesis reads `¬ 0 ∣ N`,
i.e. `N ≠ 0`, which `hN : 4 ≤ N` supplies.

`hN : 4 ≤ N` rather than `0 < N`.  At `N ≤ 3` the pair `(E, P)` has extra
automorphisms and the moduli problem is not rigid, and — more to the
point here — at `N = 0` the problem is empty over a nonempty base,
exactly as `isEmpty_of_gamma0Datum_zero` records on the `Γ₀` side: a
section of infinite order on every geometric fibre cannot exist on a
proper fibre.  Only `N = 25` is used, so the stronger hypothesis costs
nothing.

The previous "IRREDUCIBLE at this pin" verdict on this node — "neither
modular curves nor a smooth-compactification theorem for curves exists
anywhere in `Mathlib`, in `~/cs/FLT`, or in this project" — was right
about the theories and wrong about irreducibility, in the way this
development keeps meeting.  The compactification theorem was written in
the interim (`CurveCompactification.lean`), and the leaf split along the
two theories: what remains modular is only
`exists_isCoarseModuliY1_isSmoothCurve`. -/
theorem exists_x1Compactification (N : ℕ) (hN : 4 ≤ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecQ) (strY : Y ⟶ SpecQ) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) := by
  refine exists_x1Compactification_field N hN ℚ ?_
  rw [ringChar.eq_zero]
  simp only [Nat.zero_dvd]
  omega

/-- **`X_1(N)` exists over `𝔽_ℓ` for `ℓ ∤ N`** (PROVEN 2026-07-27, as the
characteristic-`ℓ` case of `exists_x1Compactification_field`).

For `ℓ ∤ N` the modular curve has good reduction at `ℓ` and its special
fibre is the coarse space of the same `Γ₁(N)`-problem over `𝔽_ℓ`, so no
integral model appears anywhere on this route — the special fibre is
obtained directly, and the reduction map (which is what would need the
model) is never formed.

`ringChar (ZMod ℓ) = ℓ`, so `hℓN` is literally the characteristic
hypothesis; `hℓ` is needed only to make `ZMod ℓ` a field, and
`PerfectField (ZMod ℓ)` is then `PerfectField.ofFinite`. -/
theorem exists_x1Compactification_finiteField (N ℓ : ℕ) (hN : 4 ≤ N) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact exists_x1Compactification_field N hN (ZMod ℓ)
    (by simpa only [ZMod.ringChar_zmod_n] using hℓN)

/-- **The cusp locus of `X_1(N)`, as a finite `ℚ`-scheme with prescribed
residue degrees.**

The cuspidal part of the Deligne–Rapoport model of `X_1(N)`, written down
as data: `X ∖ Y` is the disjoint union, over an index set `C` of cusps,
of `Spec` of a residue field `K c` over `ℚ`; and `φ(N)/2` of those cusps
— the orbit of `∞`, indexed by `(ℤ/N)ˣ/±1` — have residue degree `1`,
i.e. are `ℚ`-rational.

**Why this is the shape of the leaf, and what it avoids.**  Verbatim the
reasoning of `IsX0Compactification.CuspLocus` (`X0.lean`), which is the
`Γ₀` sibling of this structure.  Mathlib's
`CuspOrbits (CongruenceSubgroup.Gamma1 N)`
(`Mathlib/NumberTheory/ModularForms/Cusps.lean`) does describe the cusps
— but as a `Γ_1(N)`-set of points of `OnePoint ℝ`, and turning a
`Γ_ℚ`-fixed geometric point into an element of `RelPoint strX (𝟙 SpecQ)`
needs a Galois-descent theorem present in none of `Fermat/`,
`.lake/packages/mathlib/`, `~/cs/FLT/`.  Recording the cusps **over `ℚ`
from the start**, as residue ALGEBRAS rather than as a Galois orbit,
sidesteps that entirely: rationality becomes `finrank ℚ (K c) = 1` and
`exists_specSection_of_finrank_eq_one` extracts the `ℚ`-point by pure
algebra.  Descent is not defeated, it is *relocated* — absorbed into the
Deligne–Rapoport statement, which is where the literature proves it.

**`cover` is what forbids the junk witness.**  Without it, `C = Empty`
with `infty` vacuous would satisfy everything at `N ≤ 2` and, worse, a
family of "cusps" unrelated to `X ∖ Y` would satisfy it at every level.
`cover` forces the `κ c` to EXHAUST `(Set.range jY.base)ᶜ`, so the datum
determines the cusp locus exactly.  It is strictly more than
`exists_rationalCuspsX1` consumes — that derivation uses only the `⊆`
direction — and it is carried anyway, so that the leaf states the theorem
the literature proves rather than the weakest thing that happens to
suffice.

**Only the EASY half of Ogg's description is asked for even so.**  The
residue degrees of the `∞`-cusps are recorded as `1`; nothing here says
anything about the residue fields of the OTHER cusps, so the hard
direction — that the Galois action on the remaining `18` cusps at
`N = 25` is exactly cyclotomic, hence that none of them is rational — is
not an obligation.  See `numRationalCuspsX1` for why a lower bound
suffices throughout.

**Which `φ(N)/2` cusps are the rational ones is deliberately NOT pinned**
beyond `infty_degree`.  The literature's two conventions for the
`(E, P)` model disagree about whether the rational orbit sits over the
cusp `0` or the cusp `∞` of `X_0(N)` — in the Deligne–Rapoport moduli
description the rational ones are the pairs (Néron `N`-gon, generator of
the component group `ℤ/N`), the others being (Néron `1`-gon, generator of
`μ_N`) and defined over `ℚ(ζ_N)⁺`.  The COUNT is `φ(N)/2` on either
convention, and the count is all that is consumed, so the field is named
`infty` for continuity with `numRationalCuspsX1`'s prose and carries no
claim about which orbit it is.

Stated over `Spec ℚ` rather than over the general base of
`IsX1Compactification`, deliberately: residue fields change under base
change, so `finrank ℚ (K c) = 1` would be the wrong condition over
`Spec 𝔽_ℓ`.  The `𝔽_ℓ` cusp count is a separate statement,
`card_cusp_x1_finiteField`. -/
structure IsX1Compactification.CuspLocus {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) where
  /-- an index set for the cusps of `X_1(N)` -/
  C : Type
  /-- the residue field of the cusp `c` -/
  K : C → Type
  /-- each residue algebra is a field -/
  [isField : ∀ c, Field (K c)]
  /-- each residue field is a `ℚ`-algebra -/
  [isAlgebra : ∀ c, Algebra ℚ (K c)]
  /-- the cusp `c`, as a `ℚ`-morphism `Spec (K c) ⟶ X` -/
  κ : ∀ c, Spec (CommRingCat.of (K c)) ⟶ X
  /-- `κ c` is a morphism over `Spec ℚ`.  Named `comm` rather than the
  obvious `over`, which is a reserved token in this file's notation scope
  and silently truncates the structure. -/
  comm : ∀ c, κ c ≫ strX = Spec.map (CommRingCat.ofHom (algebraMap ℚ (K c)))
  /-- the cusps exhaust the complement of `Y` -/
  cover : ⋃ c, Set.range (κ c).base = (Set.range jY.base)ᶜ
  /-- distinct cusps are disjoint -/
  disj : ∀ c c' : C, c ≠ c' → Disjoint (Set.range (κ c).base) (Set.range (κ c').base)
  /-- the `φ(N)/2` cusps of the rational orbit, indexed by `(ℤ/N)ˣ/±1` -/
  infty : Fin (numRationalCuspsX1 N) → C
  /-- they are pairwise distinct -/
  infty_inj : Function.Injective infty
  /-- each of them is `ℚ`-rational -/
  infty_degree : ∀ i, Module.finrank ℚ (K (infty i)) = 1

attribute [instance] IsX1Compactification.CuspLocus.isField
  IsX1Compactification.CuspLocus.isAlgebra

/-! ### The cusp locus as a set of points

`IsX1Compactification.CuspLocus` presents the cusps as `Spec` of a residue
ALGEBRA over `ℚ`.  Deligne–Rapoport (VI.5, *L'action de Galois sur les
pointes*) describe the cusp locus as what it is: the finite set of CLOSED
POINTS `X ∖ Y`, together with the Galois action on it, from which the residue
fields — and hence the residue degrees — are read off.

`nonempty_cuspLocusX1_of_rationalCuspPoints` below is the dictionary between
the two, and it is the exact `Γ₁` mirror of `X0.lean`'s
`nonempty_cuspLocus_of_residueIndexing`: it discharges every field of
`CuspLocus` except the arithmetic one, using nothing but mathlib's
residue-field API (`Scheme.residueField`, `Scheme.fromSpecResidueField`,
`Scheme.range_fromSpecResidueField`, `Spec.map_preimage`) and `X0.lean`'s
`residueQAlgebra` / `residueQDegree`.  What is left open,
`exists_rationalCuspPointsX1_field` (2026-07-28; `exists_rationalCuspPointsX1`
is PROVEN over it), is then exactly the Deligne–Rapoport sentence and nothing
else. -/

/-- **The cusp locus, assembled from `φ(N)/2` rational points of the
complement** (PROVEN 2026-07-27; axiom-audited
`[propext, Classical.choice, Quot.sound]`).

The sorry-free half of `nonempty_cuspLocusX1`, and the `Γ₁` mirror of
`X0.lean`'s `nonempty_cuspLocus_of_residueIndexing`.  Given an injection
`ε : Fin (φ(N)/2) ↪ X ∖ Y` whose values have residue degree `1` over `ℚ`,
every field of `CuspLocus` is discharged here:

* `C` — the complement `X ∖ Y` ITSELF, as a subtype of `X`.  Nothing is
  gained by indexing it: `CuspLocus` asks only that the `κ c` exhaust the
  complement disjointly, and the tautological indexing does that by
  construction.  Note this is *stronger* than the `Γ₀` version, which needs a
  bijection `N.divisors ≃ X ∖ Y` supplied from outside — here the bijection
  is `Equiv.refl`, and the count of cusps outside the `∞`-orbit is never
  mentioned, which is the whole reason the `Γ₁` cusp classification (messier
  than the `Γ₀` one — the cusps are `Γ_1(N)\ℙ¹(ℚ)`, not the divisors of `N`)
  does not have to be formalised for this route.
* `K c` — the residue field `κ(c)`, with `isField` mathlib's instance and
  `isAlgebra` the `residueQAlgebra` of the structure morphism.
* `κ c` — `X.fromSpecResidueField c`, mathlib's canonical `Spec κ(c) ⟶ X`.
* `comm` — `Spec.map_preimage`, definitionally: see `residueQAlgebra`
  (`X0.lean`) for why the algebra structure is *defined* to make this hold.
* `cover` — `Scheme.range_fromSpecResidueField` says the image of `κ c` is the
  single point `c`, so the union over `c` is all of `(Set.range jY.base)ᶜ`.
* `disj` — distinct singletons.
* `infty`, `infty_inj`, `infty_degree` — the hypotheses, unchanged;
  `residueQDegree strX x` unfolds to `Module.finrank ℚ (X.residueField x)`
  under `residueQAlgebra`, which is what `infty_degree` asks for.

`h` is consumed only through the type of the conclusion — `CuspLocus` is
indexed by it — so no field of `IsX1Compactification` is used, not even
`finite_compl`.  That is honest: finiteness of the cusp locus is not needed
to *build* the datum, only to make it interesting. -/
theorem nonempty_cuspLocusX1_of_rationalCuspPoints {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY)
    (ε : Fin (numRationalCuspsX1 N) → ((Set.range jY.base)ᶜ : Set X))
    (hinj : Function.Injective ε)
    (hdeg : ∀ i, residueQDegree strX (ε i).1 = 1) :
    Nonempty h.CuspLocus := by
  have hr : ∀ c : ((Set.range jY.base)ᶜ : Set X),
      Set.range (X.fromSpecResidueField c.1).base = {(c.1 : X)} := fun c =>
    Scheme.range_fromSpecResidueField _
  refine ⟨{ C := ((Set.range jY.base)ᶜ : Set X)
            K := fun c => (X.residueField c.1 : Type)
            isField := fun c => inferInstance
            isAlgebra := fun c => residueQAlgebra strX c.1
            κ := fun c => X.fromSpecResidueField c.1
            comm := fun c => (Spec.map_preimage _).symm
            cover := ?_
            disj := ?_
            infty := ε
            infty_inj := hinj
            infty_degree := hdeg }⟩
  · simp only [hr]
    ext p
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨by rintro ⟨c, rfl⟩; exact c.2, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  · intro c c' hne
    rw [hr c, hr c']
    exact Set.disjoint_singleton.mpr fun hc => hne (Subtype.ext hc)

/-! ### Residue degree over an ARBITRARY base field

`X0.lean`'s `residueQDegree` and `residueFDegree` (further below) are the
same definition at two different base fields, and — this is the point — the
cusp statements they carry are the same STATEMENT at two different base
fields.  `residueDegreeOver` is that definition written once, over any
field `K`; both named versions are `rfl`-equal to it
(`residueDegreeOver_eq_residueQDegree` here,
`residueDegreeOver_eq_residueFDegree` below), so nothing downstream moves.

It exists for exactly one reason.  `exists_rationalCuspPointsX1_field`
below is "`X_1(N)` has `φ(N)/2` cusps rational over `K`", for any `K` in
which `N` is invertible, and it is consumed twice: at `K = ℚ` by
`exists_rationalCuspPointsX1`, and at `K = 𝔽_ℓ` by the `≥` half of
`card_cuspLocusPoints_x1_finiteField`.  Before this cut (2026-07-28) those
were two independent Deligne–Rapoport leaves asserting the same theorem of
Deligne–Rapoport VI.5, one over `ℚ` and one over `𝔽_3`, each with its own
owner.  They are now one leaf. -/

/-- **The `K`-algebra structure on the residue field of a point of a
`K`-scheme**, for an arbitrary field `K`.

Verbatim `X0.lean`'s `residueQAlgebra` and this file's `residueFAlgebra`
with the base field left free, and defined the same way — through
`Spec.preimage`, so that `Spec.map_preimage` discharges the compatibility
square by construction.  `@[reducible]` for the same reason: consumers
state `Module.finrank K (X.residueField x)` under it and instance search
must see through it. -/
@[reducible] noncomputable def residueAlgebraOver (K : Type) [Field K] {X : Scheme.{0}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (x : X) : Algebra K (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ strX)).hom.toAlgebra

/-- **The residue degree of a point of a `K`-scheme over `K`**, for an
arbitrary field `K`.  `residueDegreeOver K strX x = 1` says `κ(x) = K`,
i.e. that `x` is a `K`-rational point. -/
noncomputable def residueDegreeOver (K : Type) [Field K] {X : Scheme.{0}}
    (strX : X ⟶ Spec (CommRingCat.of K)) (x : X) : ℕ :=
  letI := residueAlgebraOver K strX x
  Module.finrank K (X.residueField x)

/-- **`residueDegreeOver ℚ` IS `residueQDegree`** (PROVEN, definitionally).

`SpecQ` is an `abbrev` for `Spec (CommRingCat.of ℚ)` and `residueQAlgebra`
is `residueAlgebraOver ℚ` spelled out, so the two sides are the same term.
Recorded as a lemma rather than left implicit because the `CommRing ℚ`
instance reaches the two spellings by different paths (`Rat.instCommRing`
against `Field.toCommRing`), which is precisely the diamond
`nonempty_gamma1Datum_of_ratPoint`'s elaboration note warns about; the
`rfl` here is the compiler's confirmation that it closes at this base. -/
theorem residueDegreeOver_eq_residueQDegree {X : Scheme.{0}} (strX : X ⟶ SpecQ) (x : X) :
    residueDegreeOver ℚ strX x = residueQDegree strX x := rfl

/-! ### `K`-rational points versus residue degree one, over an arbitrary base

The dictionary between the two ways this file describes a rational cusp — as a
SECTION of `strX` missing `Y`, and as a POINT of `X ∖ Y` with residue field `K`
— written once over an arbitrary base field.  Over `ℚ` half of it is free and
`X0.lean` proves it that way (`exists_residueAlgHom_of_isCusp`); over a general
`K` it is not, and the difference is exactly the step that docstring flags:

> Over a base where `ℚ` is not initial this step would be real, and would be
> `Spec.map_preimage` plus `x.2`.

It is real because `residueAlgebraOver K strX p` is defined through
`Spec.preimage`, so "the embedding `κ(p) ⟶ K` is `K`-LINEAR" is the assertion
that a certain square of affine schemes commutes; at `ℚ` it holds for every ring
map whatsoever (both `algebraMap`s out of `ℚ` are the rational cast), at `𝔽_ℓ`
it holds because `x` is a SECTION.  `exists_residueSection_of_ratPoint` below is
that argument, and it is where the `x.2` of the relative point is consumed.

This subsection is base-agnostic and `Γ₁`-agnostic: nothing in it mentions `N`,
the moduli problem, or `IsX1Compactification`.  It is stated with `jY` and
`hcomm` loose so that the `Γ₀` side can consume it unchanged should
`exists_residueAlgHom_of_isCusp` ever need generalising. -/

/-- **A retraction of the structure map on a residue field, packaged as a
`K`-algebra map** (PROVEN 2026-07-28).

`hg` says `algebraMap K κ(p)` — which under `residueAlgebraOver` *is*
`Spec.preimage (X.fromSpecResidueField p ≫ strX)` — is a section of `g`, i.e.
precisely `AlgHom.commutes'`.  So the `K`-linearity of `g` is not an extra
hypothesis but a repackaging of `hg`, and that is the whole content of the
general-base step. -/
noncomputable def residueSectionAlgHom {K : Type} [Field K] {X : Scheme.{0}}
    {strX : X ⟶ Spec (CommRingCat.of K)} (p : X)
    (g : X.residueField p ⟶ CommRingCat.of K)
    (hg : Spec.preimage (X.fromSpecResidueField p ≫ strX) ≫ g = 𝟙 _) :
    letI := residueAlgebraOver K strX p
    X.residueField p →ₐ[K] K :=
  letI := residueAlgebraOver K strX p
  ⟨g.hom, fun c => congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of K => h.hom c) hg⟩

/-- **A point whose residue field retracts onto `K` is `K`-rational** (PROVEN
2026-07-28), i.e. `residueDegreeOver K strX p = 1`.

`finrank_eq_one_of_algHom_to_base` (`X0.lean`, stated over a VARIABLE base
field for exactly this reason) applied to `residueSectionAlgHom`. -/
theorem residueDegreeOver_eq_one_of_residueSection {K : Type} [Field K] {X : Scheme.{0}}
    {strX : X ⟶ Spec (CommRingCat.of K)} (p : X)
    (g : X.residueField p ⟶ CommRingCat.of K)
    (hg : Spec.preimage (X.fromSpecResidueField p ≫ strX) ≫ g = 𝟙 _) :
    residueDegreeOver K strX p = 1 := by
  letI := residueAlgebraOver K strX p
  show Module.finrank K (X.residueField p) = 1
  exact finrank_eq_one_of_algHom_to_base (residueSectionAlgHom p g hg)

/-- **The retraction is UNIQUE** (PROVEN 2026-07-28) — `algHom_to_base_unique`
(`X0.lean`) transported back through `CommRingCat.hom_ext`.

This is what makes the cusp-counting map INJECTIVE: two `K`-rational sections of
`strX` with the same image point factor through the same `κ(p)` by the same map,
hence are equal.  Without it, `n` distinct sections could a priori collapse onto
fewer than `n` points and the count would be lost. -/
theorem residueSection_unique {K : Type} [Field K] {X : Scheme.{0}}
    {strX : X ⟶ Spec (CommRingCat.of K)} (p : X)
    (g g' : X.residueField p ⟶ CommRingCat.of K)
    (hg : Spec.preimage (X.fromSpecResidueField p ≫ strX) ≫ g = 𝟙 _)
    (hg' : Spec.preimage (X.fromSpecResidueField p ≫ strX) ≫ g' = 𝟙 _) : g = g' := by
  letI := residueAlgebraOver K strX p
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom
    (algHom_to_base_unique (residueSectionAlgHom p g hg) (residueSectionAlgHom p g' hg'))

/-- **A `K`-rational point of `X` that is not a point of `Y` is a point of the
complement, carrying a retraction of the structure map on its residue field**
(PROVEN 2026-07-28) — the general-base form of `X0.lean`'s
`exists_residueAlgHom_of_isCusp`, and it needs no moduli input whatever.

Two independent halves, neither of them modular:

* *The factorisation.*  `Scheme.SpecToEquivOfField` says a morphism
  `Spec K ⟶ X` is exactly a point `p` together with an embedding `κ(p) ⟶ K`,
  with no hypothesis.  That the embedding RETRACTS the structure map is
  `Spec.map_injective` applied to `Spec.map_preimage` together with `x.2` — see
  the subsection note; this is the step that is vacuous at `ℚ` and real here.
* *The point lies off `Y`.*  Where `IsOpenImmersion jY` is used: a section of
  `Spec K` has a ONE-POINT image, so if that point were in the open
  `Set.range jY.base` then `IsOpenImmersion.lift` would factor `x` through `jY`,
  exhibiting it as a `sectionAlong` and contradicting the cusp hypothesis. -/
theorem exists_residueSection_of_ratPoint {K : Type} [Field K] {X Y : Scheme.{0}}
    {strX : X ⟶ Spec (CommRingCat.of K)} {strY : Y ⟶ Spec (CommRingCat.of K)}
    {jY : Y ⟶ X} [IsOpenImmersion jY] (hcomm : jY ≫ strX = strY)
    (x : RelPoint strX (𝟙 (Spec (CommRingCat.of K))))
    (hx : ¬ ∃ y : RelPoint strY (𝟙 (Spec (CommRingCat.of K))), sectionAlong jY hcomm y = x) :
    ∃ p : ((Set.range jY.base)ᶜ : Set X),
      ∃ g : X.residueField p.1 ⟶ CommRingCat.of K,
        Spec.preimage (X.fromSpecResidueField p.1 ≫ strX) ≫ g = 𝟙 _ ∧
        Spec.map g ≫ X.fromSpecResidueField p.1 = x.1 := by
  classical
  set q := Scheme.SpecToEquivOfField K X x.1 with hq
  have hfac : Spec.map q.2 ≫ X.fromSpecResidueField q.1 = x.1 :=
    (Scheme.SpecToEquivOfField K X).symm_apply_apply x.1
  have hpt : ∀ s, x.1.base s = q.1 := by
    intro s
    rw [← hfac]
    simp
  have hmem : q.1 ∈ (Set.range jY.base)ᶜ := by
    intro hcon
    apply hx
    have hrange : Set.range x.1.base ⊆ Set.range jY.base := by
      rintro _ ⟨s, rfl⟩
      rw [hpt s]
      exact hcon
    refine ⟨⟨IsOpenImmersion.lift jY x.1 hrange, ?_⟩, ?_⟩
    · rw [← hcomm, ← Category.assoc, IsOpenImmersion.lift_fac, x.2]
    · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨⟨q.1, hmem⟩, q.2, ?_, hfac⟩
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, ← Category.assoc, hfac, x.2]

/-- **`n` distinct `K`-rational cusp SECTIONS give `n` distinct points of
`X ∖ Y` of residue degree one** (PROVEN 2026-07-28).

The whole scheme-theoretic bookkeeping of the cusp count, discharged once over
an arbitrary base: `exists_residueSection_of_ratPoint` produces the points,
`residueDegreeOver_eq_one_of_residueSection` gives the degrees, and
`residueSection_unique` transports injectivity of `σ` to injectivity of `ε`.

The transport is stated as `key` with the two points as bound VARIABLES so that
`rintro … rfl` can substitute; the residue field of a point is a dependent type,
so rewriting `(p i).1 = (p j).1` in place would leave a motive that is not type
correct. -/
theorem exists_rationalCuspPoints_of_sections {K : Type} [Field K] {X Y : Scheme.{0}} {n : ℕ}
    {strX : X ⟶ Spec (CommRingCat.of K)} {strY : Y ⟶ Spec (CommRingCat.of K)}
    {jY : Y ⟶ X} [IsOpenImmersion jY] (hcomm : jY ≫ strX = strY)
    (σ : Fin n → RelPoint strX (𝟙 (Spec (CommRingCat.of K))))
    (hinj : Function.Injective σ)
    (hcusp : ∀ i, ¬ ∃ y : RelPoint strY (𝟙 (Spec (CommRingCat.of K))),
      sectionAlong jY hcomm y = σ i) :
    ∃ ε : Fin n → ((Set.range jY.base)ᶜ : Set X),
      Function.Injective ε ∧ ∀ i, residueDegreeOver K strX (ε i).1 = 1 := by
  classical
  choose p hp using fun i => exists_residueSection_of_ratPoint hcomm (σ i) (hcusp i)
  choose g hg hfac using hp
  have key : ∀ (a b : X) (_ : a = b)
      (ga : X.residueField a ⟶ CommRingCat.of K) (gb : X.residueField b ⟶ CommRingCat.of K),
      Spec.preimage (X.fromSpecResidueField a ≫ strX) ≫ ga = 𝟙 _ →
      Spec.preimage (X.fromSpecResidueField b ≫ strX) ≫ gb = 𝟙 _ →
      Spec.map ga ≫ X.fromSpecResidueField a = Spec.map gb ≫ X.fromSpecResidueField b := by
    rintro a b rfl ga gb hga hgb
    rw [residueSection_unique a ga gb hga hgb]
  refine ⟨p, ?_, ?_⟩
  · intro i j hij
    apply hinj
    apply Subtype.ext
    rw [← hfac i, ← hfac j]
    exact key (p i).1 (p j).1 (congrArg Subtype.val hij) (g i) (g j) (hg i) (hg j)
  · intro i
    exact residueDegreeOver_eq_one_of_residueSection (p i).1 (g i) (hg i)

/-- **`X_1(N)` has `φ(N)/2` distinct `K`-rational cusp SECTIONS, for any field
`K` in which `N` is invertible** (sorry leaf — Deligne–Rapoport VI.5, and ALL
that is left of the cusp route on BOTH sides).

**The form is the one Deligne–Rapoport actually delivers.**  Over `ℤ[1/N]` the
`φ(N)/2` cusps of the distinguished orbit are SECTIONS of the smooth model, and
this leaf asks for exactly those, read at a fibre.  The residue-degree form the
consumers want is `exists_rationalCuspPointsX1_field` below, proved from this
one by `exists_rationalCuspPoints_of_sections`.  The two are EQUIVALENT — a
point of `X ∖ Y` with residue field `K` yields a section by
`exists_specSection_of_finrank_eq_one` (`X0.lean`, at `ℚ`; the same two lines
over any `K`), and a section yields such a point by the subsection above — so
the change of form on 2026-07-28 added no strength; only one direction is used.

**What moved, and why this node is now the whole difficulty** (2026-07-28).
As cut earlier the same day, the leaf carried two things at once: the
arithmetic (there ARE `φ(N)/2` rational cusps) and the scheme-theoretic
bookkeeping (a rational cusp is a point of `X ∖ Y` whose residue field is `K`,
and distinct cusps give distinct points).  The second is not Deligne–Rapoport
and mentions neither `N`, nor `K`, nor the moduli problem; it is now the
subsection above, proved over an arbitrary base.  Only the arithmetic is left,
and it is here.

TRUE and classical (Ogg 1973; Deligne–Rapoport VI.5, Construction 5.3;
Diamond–Shurman §3.8 for the cusp count and §9.3 for the rationality): the
cusps of `X_1(N)` over `K̄` are `Γ_1(N)\ℙ¹(ℚ)`, of which there are
`½ Σ_{d ∣ N} φ(d)φ(N/d)` for `N ≥ 5` (`28` at `N = 25`); they fall into
Galois orbits under Deligne–Rapoport's `σ_t : a ↦ t⁻¹ a`, and the `φ(N)/2`
cusps of one distinguished orbit are individually rational — i.e. their
residue field is `K`, which is what `residueDegreeOver K strX (ε i) = 1`
says.  Over `ℤ[1/N]` those `φ(N)/2` cusps are SECTIONS of the smooth model
(Deligne–Rapoport VI.5), which is why the statement is uniform in `K` and
not two statements: `ℚ` and `𝔽_ℓ` with `ℓ ∤ N` are two fibres of one
cuspidal subscheme.

**WHY THE BASE FIELD IS FREE, and what it bought** (2026-07-28).  This
leaf replaces two: the former `exists_rationalCuspPointsX1` over `ℚ` and
the `≥` half of `card_cuspLocusPoints_x1_finiteField` over `𝔽_3`.  Both
were the same sentence of Deligne–Rapoport and both were open, so a prover
of either was proving the other without being credited with it.  Note the
axis is available here and is NOT available for the `≤` half — see
`card_cuspLocusPoints_x1_finiteField_le`, which needs the count EXACTLY
and therefore the HARD direction of Ogg's description.

WHAT REMAINS, precisely: the identification of `X ∖ Y` with the cuspidal
part of the Deligne–Rapoport model — the uniformisation
`X_1(N)(ℂ) ≅ Γ_1(N)∖ℍ*` together with its `ℤ[1/N]`-structure.
`IsX1Compactification` supplies only that the complement is finite, so
nothing weaker than that identification can produce a single cusp: the
structure's fields do not by themselves forbid `jY` from being an
isomorphism with no cusps at all, and that is excluded only because
`coarse` pins `Y` as the affine curve `Y_1(N)`, which is moduli input
rather than scheme-theoretic bookkeeping.

**`hNK : IsUnit ((N : ℕ) : K)` is the ONLY hypothesis on the base**, and
it is load-bearing rather than decorative: at `char K ∣ N` the `Γ₁(N)`
problem is not the étale one, its cuspidal locus is not `Γ_1(N)\ℙ¹(ℚ)`,
and the count `φ(N)/2` is not claimed by any reference.  Both consumers
discharge it for free — over `ℚ` because `numRationalCuspsX1 N ≠ 0` forces
`N ≥ 3`, over `𝔽_ℓ` because `x1WitnessTable_spec` carries `¬ ℓ ∣ N`.

**This leaf is the `Γ₁` sibling of `X0.lean`'s
`exists_cuspResidueIndexing`, and it is strictly weaker.**  The `Γ₀` leaf
asks for a BIJECTION `N.divisors ≃ X ∖ Y` with each residue field
identified as `ℚ(ζ_{gcd(d, N/d)})`; this one asks only for `φ(N)/2` cusp
sections — equivalently, `φ(N)/2` points of `X ∖ Y` with residue field `K` —
and says nothing whatever about the
other `18` cusps at `N = 25` or about how many cusps there are in total.
That is deliberate and is the economy `numRationalCuspsX1` records.

Stated with `residueDegreeOver = 1` rather than with `IsResidueCyclotomic
… 1`: at the distinguished orbit the residue field is `K` itself, so the
cyclotomic phrasing would add the obligation
`IsCyclotomicExtension {1} K K` for zero information.  Do NOT restate it as
`Nonempty (κ(x) ≃ₐ[K] K)` either — that is the algebra diamond
`IsResidueCyclotomic`'s docstring warns about.

The axes searched for a further cut are recorded on
`exists_rationalCuspPointsX1` immediately below, which is now a corollary
of this leaf and keeps them; they are unchanged by the base-field
generalisation, since every one of them was about the CUSP description and
none about `ℚ`. -/
theorem exists_rationalCuspSectionsX1_field (N : ℕ) (K : Type) [Field K]
    (_hNK : IsUnit ((N : ℕ) : K))
    {X Y : Scheme.{0}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strY : Y ⟶ Spec (CommRingCat.of K)} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    ∃ σ : Fin (numRationalCuspsX1 N) → RelPoint strX (𝟙 (Spec (CommRingCat.of K))),
      Function.Injective σ ∧ ∀ i, h.IsCusp (σ i) :=
  sorry

/-- **`X_1(N)` has `φ(N)/2` cusps rational over ANY field `K` in which `N` is
invertible** (PROVEN 2026-07-28 over `exists_rationalCuspSectionsX1_field`; a
bare sorry leaf until then — Deligne–Rapoport VI.5).

The residue-degree form of the leaf above, which is what both consumers read:
`exists_rationalCuspPointsX1` at `K = ℚ` and the `≥` half of
`card_cuspLocusPoints_x1_finiteField` at `K = 𝔽_ℓ`.  Its whole proof is
`exists_rationalCuspPoints_of_sections`, i.e. scheme-theoretic bookkeeping over
an arbitrary base with no moduli input; see the leaf for the mathematics, the
axes searched, and why `hNK` is load-bearing.

`h.isOpen` is the only field of `IsX1Compactification` this step consumes, and
it is consumed only to know that a section landing in `Y`'s image would factor
through `jY`. -/
theorem exists_rationalCuspPointsX1_field (N : ℕ) (K : Type) [Field K]
    (hNK : IsUnit ((N : ℕ) : K))
    {X Y : Scheme.{0}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strY : Y ⟶ Spec (CommRingCat.of K)} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    ∃ ε : Fin (numRationalCuspsX1 N) → ((Set.range jY.base)ᶜ : Set X),
      Function.Injective ε ∧ ∀ i, residueDegreeOver K strX (ε i).1 = 1 := by
  haveI := h.isOpen
  obtain ⟨σ, hinj, hcusp⟩ := exists_rationalCuspSectionsX1_field N K hNK h
  exact exists_rationalCuspPoints_of_sections h.comm σ hinj hcusp

/-- **`X_1(N)` has `φ(N)/2` distinct `ℚ`-rational points in the cusp locus
`X ∖ Y`** (PROVEN 2026-07-28 over `exists_rationalCuspPointsX1_field`; a
sorry leaf until then — Deligne–Rapoport VI.5).

**What is left here is the DEGENERATE-LEVEL split and nothing else.**  The
leaf above needs `N` invertible in the base; `ℚ` supplies that as soon as
`N ≠ 0`, and at `N = 0` — the only case it does not cover — the conclusion
is vacuous, because `numRationalCuspsX1 0 = φ(0)/2 = 0` and `Fin 0` is
empty.  So the case split is on `numRationalCuspsX1 N = 0`: below it the
statement carries nothing, above it `N.totient ≥ 2` forces `N ≥ 3`.

TRUE and classical (Ogg 1973; Deligne–Rapoport VI.5, Construction 5.3;
Diamond–Shurman §3.8 for the cusp count and §9.3 for the rationality): the
cusps of `X_1(N)` over `ℚ̄` are `Γ_1(N)\ℙ¹(ℚ)`, of which there are
`½ Σ_{d ∣ N} φ(d)φ(N/d)` for `N ≥ 5` (`28` at `N = 25`); they fall into
Galois orbits under Deligne–Rapoport's `σ_t : a ↦ t⁻¹ a`, and the `φ(N)/2`
cusps of one distinguished orbit are individually `ℚ`-rational — i.e. their
residue field is `ℚ`, which is what `residueQDegree strX (ε i) = 1` says.

WHAT REMAINS, precisely: the identification of `X ∖ Y` with the cuspidal part
of the Deligne–Rapoport model — the uniformisation `X_1(N)(ℂ) ≅ Γ_1(N)∖ℍ*`
together with its `ℚ`-structure.  `IsX1Compactification` supplies only that
the complement is finite, so nothing weaker than that identification can
produce a single cusp: the structure's fields do not by themselves forbid
`jY` from being an isomorphism with no cusps at all, and that is excluded
only because `coarse` pins `Y` as the affine curve `Y_1(N)`, which is moduli
input rather than scheme-theoretic bookkeeping.

**This leaf is the `Γ₁` sibling of `X0.lean`'s `exists_cuspResidueIndexing`,
and it is strictly weaker.**  The `Γ₀` leaf asks for a BIJECTION
`N.divisors ≃ X ∖ Y` with each residue field identified as `ℚ(ζ_{gcd(d,
N/d)})`; this one asks only for `φ(N)/2` points of `X ∖ Y` with residue field
`ℚ`, and says nothing whatever about the other `18` cusps at `N = 25` or
about how many cusps there are in total.  That is deliberate and is the
economy `numRationalCuspsX1` records: the `ℚ`-side consumers need *enough*
rational cusps, never all of them, and never the hard direction of Ogg's
description.  (The `𝔽_ℓ` side is where the count is needed exactly — see
`card_cusp_x1_finiteField`, whose docstring says so.)

Stated with `residueQDegree = 1` rather than with `IsResidueCyclotomic
… 1`, unlike the `Γ₀` leaf: at the `∞`-orbit the residue field is `ℚ`
itself, so the cyclotomic phrasing would add the obligation
`IsCyclotomicExtension {1} ℚ ℚ` for zero information.  Do NOT restate it as
`Nonempty (K ≃ₐ[ℚ] ℚ)` either — that is the `ℚ`-algebra diamond
`IsResidueCyclotomic`'s docstring warns about.

AXES SEARCHED, each with the check that would refute it.

1. *The count* — weakening to a lower bound.  Already done upstream and
   inherited here: `numRationalCuspsX1` is a lower bound by construction.
   It does not help — the difficulty is producing cusps, not bounding them.
2. *The index set* — `Fin (φ(N)/2)` against `(ℤ/N)ˣ/±1`.  Exhausted: the two
   are interderivable and moving the index around cannot make either side
   smaller.  `Fin` is taken so that no consumer inherits a
   `Nat.card ((ZMod N)ˣ ⧸ ±1) = φ(N)/2` obligation.
3. *The `j`-map dictionary* — characterise a cusp as a pole of an extended
   `j`-map.  DEAD, by `X0.lean`'s axis-3 argument verbatim: such an extension
   is definable from `IsCusp` itself, unconditionally, hence carries no
   information about it and has a model with no rational cusp at all.
4. *An invariant-first cut* — peel the cusp invariant off as one leaf and
   "each value is attained" as another.  UNSAFE for the reason `X0.lean`
   records at its axis 4: quantified over an arbitrary invariant the
   existence half is FALSE by a constant junk witness.
5. *The RESIDUE-FIELD axis* — TAKEN (2026-07-27), and it is what turned
   `nonempty_cuspLocusX1` into a theorem: the scheme-level bookkeeping is
   `nonempty_cuspLocusX1_of_rationalCuspPoints` and this leaf now carries
   only the arithmetic.  Refuted by exhibiting a model of `CuspLocus` over
   some `IsX1Compactification` whose cusps are not those of `X_1(N)`.
6. *The GALOIS-DESCENT axis* — DEAD, and a successor should not reinstate it.
   Descent for rational points of a `ℚ`-scheme is on the route only while the
   cusps are described as a Galois SET; described as a `ℚ`-SCHEME with
   prescribed residue degrees, rationality is `finrank ℚ (K c) = 1` and
   `exists_specSection_of_finrank_eq_one` (`X0.lean`, PROVEN) extracts the
   point by pure algebra.  This is the cut `X0.lean` made at
   `nonempty_cuspLocus` on the same day. -/
theorem exists_rationalCuspPointsX1 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY) :
    ∃ ε : Fin (numRationalCuspsX1 N) → ((Set.range jY.base)ᶜ : Set X),
      Function.Injective ε ∧ ∀ i, residueQDegree strX (ε i).1 = 1 := by
  rcases Nat.eq_zero_or_pos (numRationalCuspsX1 N) with h0 | hpos
  · haveI : IsEmpty (Fin (numRationalCuspsX1 N)) := by rw [h0]; infer_instance
    exact ⟨isEmptyElim, fun a => isEmptyElim a, fun i => isEmptyElim i⟩
  · have hN0 : N ≠ 0 := by
      rintro rfl
      simp [numRationalCuspsX1] at hpos
    exact exists_rationalCuspPointsX1_field N ℚ
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN0)) h

/-- **The cusp locus of `X_1(N)` exists** (PROVEN 2026-07-27 over
`exists_rationalCuspPointsX1`; formerly a sorry leaf).

TRUE and classical (Ogg 1973; Deligne–Rapoport VI.5; Diamond–Shurman
§3.8 for the cusp count and §9.3 for the rationality): the cusps of
`X_1(N)` over `ℚ̄` are `Γ_1(N)\ℙ¹(ℚ)`, of which there are
`½ Σ_{d ∣ N} φ(d)φ(N/d)` for `N ≥ 5` (`28` at `N = 25`); they fall into
Galois orbits, and the `φ(N)/2` cusps of one distinguished orbit are
individually `ℚ`-rational, the Galois action on them being trivial.

**The whole scheme-theoretic content is now discharged**, and this node
carries none of it: `nonempty_cuspLocusX1_of_rationalCuspPoints` builds every
field of `CuspLocus` from `φ(N)/2` residue-degree-`1` points of `X ∖ Y`, and
`exists_rationalCuspPointsX1_field` is the one remaining Deligne–Rapoport
input (2026-07-28: `exists_rationalCuspPointsX1` between them is itself now a
theorem, carrying only the `N = 0` degenerate split).  See that leaf for the
axes searched and for why Galois descent is OFF the route; a successor should
attack it and not this node.

`hN` is NOT carried, unlike on the `Γ₀` side.  `numRationalCuspsX1 N =
φ(N)/2` is already `0` at `N ∈ {0, 1, 2}`, so `infty` is vacuous there
and no degenerate-level case has to be split off; the remaining fields
are a statement about `X ∖ Y` that is meaningful at every `N`. -/
theorem nonempty_cuspLocusX1 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY) :
    Nonempty h.CuspLocus :=
  let ⟨ε, hinj, hdeg⟩ := exists_rationalCuspPointsX1 N h
  nonempty_cuspLocusX1_of_rationalCuspPoints h ε hinj hdeg

/-- **`X_1(N)` has at least `φ(N)/2` distinct `ℚ`-rational cusps** (PROVEN
2026-07-27 over `nonempty_cuspLocusX1`; formerly a sorry node).

TRUE and classical (Ogg; Deligne–Rapoport VI.6, or Diamond–Shurman §3.8):
the cusps of `X_1(N)` over `ℚ̄` are `Γ_1(N)\ℙ¹(ℚ)`, and those lying over
the cusp `∞` of `X_0(N)` are indexed by `(ℤ/N)ˣ/±1`, on which the Galois
action is trivial; so all `φ(N)/2` of them are `ℚ`-rational, and they are
pairwise distinct because the index is a `Γ_1(N)`-invariant.

WHAT REMAINS, precisely.  Only the EASY direction of the cusp
description, for the reason `numRationalCuspsX1` records — an injection
is all that is consumed, so nothing has to be proved about the cusps
*outside* the `∞`-orbit.  The missing input is the identification of
`X ∖ Y` with `Γ_1(N)\ℙ¹(ℚ)` compatibly with the `Γ_ℚ`-action, which is
the cuspidal part of the Deligne–Rapoport model.  `IsX1Compactification`
supplies only that the complement is finite, so nothing weaker than that
identification can produce a single cusp: the structure's fields do not
by themselves forbid `jY` from being an isomorphism with no cusps at all,
and that is excluded only because `coarse` pins `Y` as the affine curve
`Y_1(N)`, which is moduli input rather than scheme-theoretic
bookkeeping.

AXIS SEARCHED.  Searched: the *count* axis (weakening `=` to `≥`, which
is already done — the statement is a lower bound) and the *index set*
axis (`Fin` rather than `(ℤ/N)ˣ/±1`, taken here because the quotient
would force a `Nat.card` computation into every consumer for no
mathematical gain).  NOT searched: a route characterising a cusp as a
pole of a `j`-map, which would need `IsJMapOn`'s `Γ₁` analogue extended
across the boundary — `X0.lean`'s `IsJMapOn` deliberately does not carry
that even on the `Γ₀` side.  This note is refuted by exhibiting, in
`Fermat/`, `.lake/packages/mathlib/` or `~/cs/FLT/`, either a
modular-curve cusp theory or a `Γ_1(N)\ℙ¹(ℚ)` description with its Galois
action; as of 2026-07-27 `grep` over all three finds neither.

**UPDATE 2026-07-27 — the RESIDUE-FIELD axis is now TAKEN, and it is
what makes this a theorem.**  The obstruction recorded above is *Galois
descent for rational points of a `ℚ`-scheme*, and it is on the route only
while the cusps are described as a Galois SET.  Described instead as a
finite `ℚ`-SCHEME with prescribed residue degrees —
`IsX1Compactification.CuspLocus` below, which is how Deligne–Rapoport
states it — rationality of a cusp becomes `finrank ℚ (K c) = 1`, and
`exists_specSection_of_finrank_eq_one` (`X0.lean`, PROVEN) extracts the
`ℚ`-point by pure algebra.  This is the same cut `X0.lean` made on
2026-07-27 at `nonempty_cuspLocus`, and the derivation below is the `Γ₁`
mirror of `nonempty_cuspIndexing_of_cuspLocus`.  A successor should NOT
go and build descent for this leaf. -/
theorem exists_rationalCuspsX1 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY) :
    ∃ cusp : Fin (numRationalCuspsX1 N) → RelPoint strX (𝟙 SpecQ),
      Function.Injective cusp ∧ ∀ i, h.IsCusp (cusp i) := by
  classical
  obtain ⟨C⟩ := nonempty_cuspLocusX1 N h
  choose σ hσ using fun i : Fin (numRationalCuspsX1 N) =>
    exists_specSection_of_finrank_eq_one (C.infty_degree i)
  refine ⟨fun i => ⟨σ i ≫ C.κ (C.infty i), ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, C.comm (C.infty i), hσ i]
  · intro i j hij
    by_contra hne
    obtain ⟨P⟩ : Nonempty (PrimeSpectrum ℚ) := inferInstance
    have heq : σ i ≫ C.κ (C.infty i) = σ j ≫ C.κ (C.infty j) := congrArg Subtype.val hij
    have hp := congrArg (fun (f : SpecQ ⟶ X) => f.base P) heq
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hp
    exact Set.disjoint_left.mp (C.disj _ _ fun hh => hne (C.infty_inj hh)) ⟨_, rfl⟩ ⟨_, hp.symm⟩
  · rintro i ⟨y, hy⟩
    obtain ⟨P⟩ : Nonempty (PrimeSpectrum ℚ) := inferInstance
    have heq : y.1 ≫ jY = σ i ≫ C.κ (C.infty i) := congrArg Subtype.val hy
    have hp := congrArg (fun (f : SpecQ ⟶ X) => f.base P) heq
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hp
    have hout : ((C.κ (C.infty i)).base ((σ i).base P)) ∈ (Set.range jY.base)ᶜ := by
      rw [← C.cover]
      exact Set.mem_iUnion.mpr ⟨C.infty i, ⟨_, rfl⟩⟩
    exact hout ⟨y.1.base P, hp⟩

/-- **The witness table `(N, ℓ, #X_1(N)(𝔽_ℓ))`**, with the single row this
development needs.

`(25, 3, 10)`: `#X_1(25)(𝔽_3) = 10`.  See
`exists_x1Compactification_mod_prime` for why this row is SHALLOW — the
count equals `φ(25)/2 = numRationalCuspsX1 25`, i.e. it is the cusp count
and nothing else, because `X_1(25)` has no non-cuspidal `𝔽_3`-point at
all.

Kept as a table rather than inlined, mirroring `x0WitnessTable`, so that
a successor adding a level adds a row rather than a theorem. -/
def x1WitnessTable : List (ℕ × ℕ × ℕ) := [(25, 3, 10)]

/-- **Every row of `x1WitnessTable` has `4 ≤ N`, `ℓ` prime, `ℓ ∤ N` and
`2ℓ + 1 < N`** (PROVEN, by `decide` over the single row).

The side conditions that `exists_x1Compactification_mod_prime` needs in
order to hand its leaves a good prime.  `2 * ℓ + 1 < N` is the crude
Weierstrass bound `#E(𝔽_ℓ) ≤ 2ℓ + 1` beaten by `N`, which is exactly what
`isEmpty_gamma1Datum_finiteField` consumes; at the one row it reads
`7 < 25`.  Note `ℓ ≠ 2` is NOT among them and is not needed — the point
COUNT on the special fibre is a statement about good reduction only, and
oddness enters one step later, in
`exists_injective_reduction_of_rankZeroJacobian`, where the formal group
of the Jacobian has to be torsion-free.

Verified independently with `gp` (2026-07-27): `3` is prime, `3 ∤ 25`. -/
theorem x1WitnessTable_spec {N ℓ m : ℕ} (h : (N, ℓ, m) ∈ x1WitnessTable) :
    4 ≤ N ∧ ℓ.Prime ∧ ¬ ℓ ∣ N ∧ 2 * ℓ + 1 < N := by
  fin_cases h
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- **A curve proper over `𝔽_ℓ` has finitely many rational points**
(PROVEN 2026-07-27, by a one-line appeal to `X0.lean`'s
`finite_relPoint_of_isProper`).

The one piece of this cluster that is not about modular curves at all:
`strX` is proper, hence of finite type, over `Spec 𝔽_ℓ`, and a
finite-type scheme over a FINITE ring has finitely many sections, because
a section is determined by the images of finitely many generators in a
finite ring.  The only field of `IsX1Compactification` consumed is
`isProper`.

`finite_relPoint_of_isProper` is stated in `X0.lean` over an arbitrary
finite base ring and contains nothing `Γ₀`-specific, so this is a
statement in that file's own vocabulary rather than a duplicate of
`finite_relPoint_of_x0Compactification_finiteField`; nothing in `X0.lean`
is edited.

`hℓ` is `ℓ ≠ 0` rather than `ℓ.Prime` deliberately — that is the honest
minimal hypothesis, since all that is used is that `ZMod ℓ` is finite,
and `ZMod 0 = ℤ` is the only excluded case. -/
theorem finite_relPoint_of_x1Compactification_finiteField (N ℓ : ℕ) (hℓ : ℓ ≠ 0)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Finite (RelPoint strX (𝟙 (SpecF ℓ))) := by
  haveI : NeZero ℓ := ⟨hℓ⟩
  haveI := h.isProper
  exact finite_relPoint_of_isProper (R := ZMod ℓ) strX (𝟙 (SpecF ℓ))

/-! #### An `𝔽_ℓ`-point of `Y_1(N)_{𝔽_ℓ}` comes from a `Γ₁(N)`-datum

The standing discussion of `exists_gamma1Datum_of_relPoint` — why it is a leaf
rather than a consequence of `IsCoarseModuliY1`, what each hypothesis does, the
FAITHFULNESS AUDIT that added `ℓ.Prime`, and the five axes searched — lives
here rather than on the theorem, because the node is now DECOMPOSED and the
discussion is about the whole cluster, not about any one of its three
declarations.  It is the fineness/Lang half of the `𝔽_ℓ` point count.

TRUE.  For `N ≥ 4` the moduli problem `[Γ₁(N)]` is rigid, so over a base
where `N` is invertible the coarse space is in fact FINE and its points
ARE the data; over a finite field one may alternatively invoke Lang's
theorem, `H¹(𝔽_ℓ, G) = 1` for connected `G`, to descend a
`ℚ̄`-datum.  Either way the conclusion holds for every `Y` satisfying
`IsCoarseModuliY1`, because initiality pins `(Y, classify)` up to unique
isomorphism and representability transports along it.

**Why this is a leaf and not a consequence of `IsCoarseModuliY1`.**  That
structure records `classify` in ONE direction (a datum gives a point)
plus initiality; it deliberately does NOT record bijectivity on points —
see its docstring, which says so explicitly and says why.  So
surjectivity of `classify` on `𝔽_ℓ`-points is genuinely extra input.  It
is exactly the step the `(25, 3, 10)` docstring called "immediate", and
isolating it is what lets the arithmetic half below be attacked on its
own.

`hN : 4 ≤ N` is load-bearing: at `N ≤ 3` the pair `(E, P)` has extra
automorphisms, the coarse space is not fine, and a rational point of the
coarse space need not lift to a datum over the same base — that is the
whole content of the coarse/fine distinction.

**`hℓN : ¬ ℓ ∣ N` ADDED 2026-07-27, and it repairs a mismatch between this
statement and its own justification.**  Both routes offered above need `N`
INVERTIBLE on the base: Katz–Mazur representability of `[Γ₁(N)]` (4.7 for
rigidity, 2.7 for representability) is stated over a base where `N` is
invertible, and at `char = ℓ ∣ N` the naive problem is not representable at
all — a section of "exact order `N`" acquires an infinitesimal part and
Katz–Mazur replace it by a Drinfeld level structure, which is a DIFFERENT
moduli problem with a different coarse space.  The same hypothesis is what
`exists_isCoarseModuliY1_isSmoothCurve` already carries (as
`¬ ringChar K ∣ N`) and what `IsX1Compactification`'s `smooth` field needs;
this leaf was the one place in the `Γ₁` cluster that omitted it.

The hypothesis costs its consumers NOTHING: it is threaded through
`isEmpty_relPoint_y1_finiteField` from `x1WitnessTable_spec`, whose third
component is exactly `¬ ℓ ∣ N` and was previously discarded at the
destructuring in `card_relPoint_x1_finiteField`.  At the one witness row it
reads `¬ 3 ∣ 25`.  This is deliberately the CONSERVATIVE direction — adding a
hypothesis every call site already has can neither make a provable leaf
unprovable nor weaken anything downstream, whereas omitting a necessary one
leaves a leaf nobody can close.  A successor who establishes the `ℓ ∣ N` case
independently may drop it again.

**FAITHFULNESS AUDIT, 2026-07-27 (LATER): `hℓ : ℓ.Prime` ADDED, because the
repair above was HALF-DONE and `¬ ℓ ∣ N` does not say what it was meant to
say.**  The paragraph above is right that both routes need `N` invertible on
the base — and `¬ ℓ ∣ N` is equivalent to `IsUnit (N : ZMod ℓ)` only when `ℓ`
is PRIME, which this statement did not assume.  `SpecF ℓ` is `Spec (ZMod ℓ)`
for a bare natural number `ℓ`, so before this repair the leaf ranged over
three regimes its justification does not cover:

* **`ℓ` composite.**  Take `ℓ = 9`, `N = 6`: `¬ 9 ∣ 6` holds, yet `6` is a
  zero divisor in `ℤ/9`, so `[Γ₁(6)]` over `ℤ/9` is again the Drinfeld
  problem and not the naive one.  This is precisely the failure the paragraph
  above describes, reached without `ℓ ∣ N`.
* **`ℓ = 0`.**  `ZMod 0 = ℤ`, so the base is `Spec ℤ`, `¬ 0 ∣ N` is just
  `N ≠ 0`, and the conclusion asks for an elliptic scheme over `Spec ℤ`
  carrying a section of exact order `N ≥ 4`.  Neither offered route applies —
  `ℤ` is not a field, so Lang's theorem is not available and the finite-field
  descent is meaningless — and the conclusion is one that Shafarevich–Tate
  makes very hard to satisfy, since no elliptic curve over `ℚ` has everywhere
  good reduction.  Whether the HYPOTHESES are satisfiable at `ℓ = 0` is NOT
  settled here (it would take building a coarse `Y_1(N)` over `Spec ℤ` and a
  section of it); what is settled is that the leaf's own justification says
  nothing there, so a successor could not close it.
* **`ℓ = 1`** is already excluded, but only accidentally: `ZMod 1` is the zero
  ring and `Spec` of it is the empty scheme, so `_y` exists for free — and
  `¬ 1 ∣ N` is false, which is what rules it out.  Relying on that is fragile.

So `ℓ.Prime` is added, in exactly the conservative direction the paragraph
above argues for: the sole consumer, `isEmpty_relPoint_y1_finiteField`,
already carries `hℓ : ℓ.Prime` and passes it on for free, so nothing
downstream is weakened, and the leaf now matches its stated justification
regime — a base that is a FIELD in which `N` is invertible.  With `ℓ` prime,
`¬ ℓ ∣ N` and `IsUnit (N : ZMod ℓ)` are equivalent, so no third hypothesis is
wanted.  A successor who wants the general base should state invertibility
directly (`IsUnit (N : ZMod ℓ)`) rather than dropping primality.

AXES SEARCHED.

1. *Initiality* — deriving surjectivity of `classify` on points from
   `IsCoarseModuliY1.universal`.  DEAD, and here is the check that kills it.
   To contradict a point `y` outside the image one needs two morphisms
   `Y ⟶ Y'` that agree on every `(classify g d).1` but differ at `y`, so that
   the `∃!` of `universal` fails.  Take `Y' = Y ⨿ Y`: the two candidates are
   `ι₁` and `ι₂`, and `ι₂` is *excluded by the second clause* of `universal`
   (`(c g d).1 = (classify g d).1 ≫ u`) as soon as a single `Γ₁(N)`-datum
   exists over a single base — which it does.  So uniqueness is never
   violated and no contradiction is available: initiality constrains maps OUT
   of `Y`, never the individual points of `Y`.  This is why
   `IsCoarseModuliY1`'s docstring says bijectivity on points is deliberately
   omitted, and it is not an oversight to be routed around.
2. *Transport between models* — proving the leaf at ONE coarse model and
   moving it to all of them.  AVAILABLE and already PROVEN
   (`IsCoarseModuliY1.exists_inverse`, below), but it buys nothing: the
   universal quantification over `Y` is free, and the residual one-model
   statement is the whole difficulty.  A cut along this axis is only apparent
   progress, and worse, phrasing the one-model half as an unconditional
   `∃ Y strY, IsCoarseModuliY1 N strY ∧ …` would STRENGTHEN the leaf, since it
   would additionally assert that a coarse model exists over `𝔽_ℓ` — which
   this statement does not claim and which is a separate leaf
   (`exists_isCoarseModuliY1_isSmoothCurve`).
3. *Lang's theorem* — `H¹(𝔽_ℓ, G) = 1` for connected `G`, descending a
   `𝔽̄_ℓ`-datum.  NOT searched in Lean: it needs the automorphism group scheme
   of `(E, P)` and Galois descent for the moduli functor, neither of which is
   in this tree, in mathlib, or in `~/cs/FLT`.  Refuted by finding a Lang's
   theorem or a descent datum for elliptic schemes in any of the three.
4. *Representability as a separate leaf* — state "`[Γ₁(N)]` is representable
   over `𝔽_ℓ` for `4 ≤ N`, `ℓ ∤ N`" and derive this from it.  NOT taken here
   because a faithful statement of representability needs the moduli FUNCTOR
   written as a functor (this file has `Gamma1Datum` and
   `IsBaseChangeOfGamma1`, but no `Gamma1Datum` presheaf on `Sch/𝔽_ℓ` and no
   isomorphism-classes quotient), which is a strictly larger construction than
   the leaf it would discharge.  This is the axis a successor should take if
   the `Γ₁` moduli layer is ever built out; it is refuted — i.e. becomes cheap
   — the moment a functor-valued form of `Gamma1Datum` exists.
5. *THE ATLAS* — the axis none of the four above searched, and the one the
   decomposition below takes.  See the next paragraph.

#### The atlas cut (2026-07-27), and why the four axes above missed it

The AXES SEARCHED list above ranges over ways of attacking the coarse space
`Y` directly — initiality, transport between models, Lang, a moduli functor.
It never asks what `Y` is BUILT from, and in this file it is built from
something with a much better handle: `Gamma1Atlas`, whose `M` carries an
actual universal family `dM : Gamma1Datum N M` and whose `Y` is the
categorical quotient of `M`.  That is the axis taken here, and it splits the
leaf in two:

* `exists_fineGamma1Atlas` — SOME atlas has its map `M ⟶ Y` lifting
  `𝔽_ℓ`-points.  This is where ALL of the fineness content goes, and it is a
  statement about ONE concrete morphism rather than about a coarse space in
  the abstract.
* `nonempty_gamma1Datum_baseChange` — a `Γ₁(N)`-datum base-changes along an
  arbitrary morphism of schemes.  Formal, moduli-free, level-free, base-free;
  no arithmetic and no finite fields.  **PROVEN 2026-07-28, by citing
  `exists_gamma1Datum_baseChange`, which was already in this file**: the cut
  named a sub-leaf that a concurrent branch had independently proven, so this
  half of the atlas cut cost nothing.  See its docstring for the duplication
  and for two corrections to the audit it was dispatched with.

The assembly is then two citations plus the glue: the first leaf produces the
atlas, `Gamma1Atlas.toIsCoarseModuliY1` makes its `Y` a coarse space, and
initiality transports the given point `y` onto it — which is axis 2 above,
used not as a cut but as the glue, which is exactly the role it can play.

**THE FIRST BULLET IS NOT WHAT THIS SECTION ORIGINALLY SAID, and the
correction is instructive** (2026-07-28).  The cut was first made with that
leaf quantified over ALL atlases — `nonempty_relPoint_atlas_of_relPoint`, "the
atlas map is surjective on `𝔽_ℓ`-points" — and in that form it is **FALSE at
the Katz–Mazur atlas**, which is the one `exists_gamma1AffineModel` handed the
assembly: `M` there is `𝔐([Γ₁(N)], [Γ(n)])`, whose `𝔽_ℓ`-points are triples
`(E, P, β)` with `β` a RATIONAL basis of `E[n]`, and Hasse forbids those long
before it forbids `(E, P)`.  The full refutation — the `N = 5, ℓ = 11`
witness, and the diagnosis of the two classical routes that were misquoted to
justify the leaf — is the FALSITY AUDIT on `exists_fineGamma1Atlas` below.
Read it before trusting any argument in this section that speaks of `M ⟶ Y`
as a torsor with rational points.

**With the repair, this DOES now touch axis 4's verdict.**  The `∃ atlas` form
is representability of `[Γ₁(N)]` in all but name, so the axis the cut takes is
4 after all, and axis 4's objection — that a faithful statement of
representability needs the moduli FUNCTOR written out — is answered by
`Gamma1Atlas` itself, which is that data in the form this file already uses.
What the cut does still contradict is the implicit premise that the leaf is
atomic; it is not, and the reason the list missed it is that every one of its
four axes searched the same space (properties of `IsCoarseModuliY1`), while
the atlas is a property of the CONSTRUCTION.  Recorded here because "an
irreducibility verdict is only as wide as the axis the auditor searched" —
and, now, because a cut can be along the right axis and still be wrong. -/

/-- **A `Γ₁(N)`-datum base-changes along an arbitrary morphism** (**PROVEN
2026-07-28** — and it was ALREADY PROVEN in this very file; see the DUPLICATE
note below, which is the finding that matters here).

TRUE for every `h : T' ⟶ T`, with no hypothesis at all.  Form the fibre
product `E ×_T T'`; it is proper, smooth and has geometrically connected
fibres because each of those is stable under base change, and the section
`pt.sec` pulls back to a section of it.  Exactness of the order is preserved
because a geometric fibre of `d'` over `t : Spec K ⟶ T'` IS the geometric
fibre of `d` over `t ≫ h` — `PointOfExactOrder.geom_order` is quantified over
exactly those, so the condition transports with no computation.

**Nothing arithmetic is here.**  No level, no base field, no finiteness: this
is the base-change bookkeeping that `IsBaseChangeOfGamma1` was written to
state.

## DUPLICATE: this leaf is a `Scheme.{0}` restatement of
## `exists_gamma1Datum_baseChange`, ~1800 lines above it in this same file

The two statements are the same statement, and the `u`-polymorphic one was
PROVEN on 2026-07-27 over the `Gamma1BaseChange` namespace (`secBC`,
`downHom`, `ptBC`, `datumBC`, `isBaseChangeBC`) — so this leaf is discharged
by one citation and is *not* new mathematics.

How the duplication arose is worth recording, because it is a pure
release-integration artefact and nobody made a mistake: the atlas cut of
`exists_gamma1Datum_of_relPoint` (branch `flt-lean-36`) named this sub-leaf on
the same day that a different branch added `Gamma1BaseChange` and
`exists_gamma1Datum_baseChange` for `exists_descendClassifyGamma1`.  Neither
branch could see the other, both landed in the same release, and the frontier
then carried a `sorry` for a theorem the file already contained.

**Two corrections to the ROUTE AUDIT this leaf was dispatched with**, both of
the "stale audit" shape the doctrine warns about:

* it recorded, as "the one real obstruction", that `AbelianSchemeStruct` has
  no base change anywhere in this tree, on the strength of a `grep` over
  `Modularity/AbelianScheme.lean` alone.  `AbelianSchemeStruct.baseChange` —
  with `RelPoint.baseChangeDown` / `baseChangeUp`, `baseChange_add`,
  `baseChange_zero`, `baseChangeDown_injective`, `baseChangeDown_pre` — is in
  `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`, and reaches this file
  publicly through `X0.lean`.  One file is not the tree.
* it recorded that this statement would be "`Γ₀`-usable verbatim once
  written".  Backwards: `X0.lean`'s `exists_gamma0Datum_baseChange` was proven
  FIRST, over `Gamma0BaseChange`, and `Gamma1BaseChange` is its transcription.

**Cleanup available, deliberately not taken here.**  This declaration can be
deleted outright once its single consumer `exists_gamma1Datum_of_relPoint`
below is repointed to `exists_gamma1Datum_baseChange h d` (note the argument
ORDER differs: `(h) (d)` there, `(d) (h)` here).  That edit was not made
because `exists_gamma1Datum_of_relPoint`'s docstring is shared with the
concurrently-owned leaf `nonempty_relPoint_atlas_of_relPoint`, and a one-line
alias costs less than a merge conflict in it.

**Non-vacuity.**  The conclusion produces `d'` TOGETHER WITH the cartesian
square `IsBaseChangeOfGamma1 h d' d`, so a junk datum over `T'` does not
discharge it: `isPullback` pins `d'.E` as the fibre product and `map_sec`
pins the level structure.  Both are genuinely produced:
`Gamma1BaseChange.isBaseChangeBC` supplies the square as
`(IsPullback.of_hasPullback d.f h).flip` and `map_sec` as
`Gamma1BaseChange.secBC_fst`. -/
theorem nonempty_gamma1Datum_baseChange {N : ℕ} {T' T : Scheme.{0}}
    (d : Gamma1Datum N T) (h : T' ⟶ T) :
    ∃ d' : Gamma1Datum N T', Nonempty (IsBaseChangeOfGamma1 h d' d) :=
  exists_gamma1Datum_baseChange h d

/-! #### Representability of `[Γ₁(N)]`, and the atlas it produces

The three declarations below decompose `exists_fineGamma1Atlas` (2026-07-28)
along the one axis its own docstring names as what has to be built —
"representability of `[Γ₁(N)]` over `𝔽_ℓ` for `N ≥ 4`, packaged as a
`Gamma1Atlas` with `π` an isomorphism".  The cut separates the two halves
of that sentence: `IsFineGamma1Moduli` and `exists_isFineGamma1Moduli` are
the representability, with no atlas bookkeeping in them at all, and
`Gamma1Atlas.ofFineModuli` is the packaging, which turns out to be formal
— four fields, no geometry, no arithmetic, and no use of `N`, `ℓ` or the
base.
-/

/-- **`dM` over `M` is a FINE moduli scheme for `[Γ₁(N)]` over `S`**:
every `Γ₁(N)`-datum over an `S`-scheme is a base change of `dM` along a
morphism of `S`-schemes, and that morphism is UNIQUE.

This is representability of the moduli problem, written with the data this
file already carries rather than as a functor on `Sch/S`.
`exists_classify` says `Hom(-, M)` covers the moduli functor;
`eq_of_isBaseChange` says it covers it injectively; together they say that
`Hom(T, M)` *is* the set of isomorphism classes of `Γ₁(N)`-data over `T`,
because `IsBaseChangeOfGamma1 m d dM` asserts exactly that `d` sits in the
class of `m^* dM`.  That is axis 4 of the AXES SEARCHED list above, whose
objection — that a faithful statement of representability needs the moduli
functor written out — is answered here by `Gamma1Datum` and
`IsBaseChangeOfGamma1`, which are that functor's data in the form this
file already uses.

**Why only `exists_classify` carries an "over `S`" clause.**  Uniqueness
is a statement about `M` alone and the structure morphism plays no part in
it; existence has to produce a morphism *of `S`-schemes*, which is what
`m ≫ strM = g` says.  Over `SpecF ℓ` that clause is in fact automatic —
`ZMod ℓ` is a quotient of the initial ring `ℤ`, so `Hom(T, SpecF ℓ)` is a
subsingleton, which is the `𝔽_ℓ` analogue of `subsingleton_hom_specQ` — but
it is stated so that the notion is the right one over a general base.

**NOT VACUOUS, and in particular `M` cannot be empty.**  `exists_classify`
demands a morphism `T ⟶ M` for every `T` carrying a datum, and data do
exist over nonempty bases: for `ℓ ∤ N` every elliptic curve over `𝔽̄_ℓ`
has full `N`-torsion, hence a point of exact order `N`.  So the degenerate
witness `M = ∅` — the one thing a `∃`-shaped moduli statement has to be
checked against — is excluded by the structure itself rather than by a
side condition. -/
structure IsFineGamma1Moduli (N : ℕ) {M S : Scheme.{0}} (strM : M ⟶ S)
    (dM : Gamma1Datum N M) : Prop where
  /-- every datum over an `S`-scheme is a base change of `dM`, along a
  morphism over `S` -/
  exists_classify : ∀ {T : Scheme.{0}} (g : T ⟶ S) (d : Gamma1Datum N T),
    ∃ m : T ⟶ M, m ≫ strM = g ∧ Nonempty (IsBaseChangeOfGamma1 m d dM)
  /-- and the classifying morphism is determined by the datum -/
  eq_of_isBaseChange : ∀ {T : Scheme.{0}} {d : Gamma1Datum N T} {m₁ m₂ : T ⟶ M},
    Nonempty (IsBaseChangeOfGamma1 m₁ d dM) → Nonempty (IsBaseChangeOfGamma1 m₂ d dM) →
    m₁ = m₂

/-- **`[Γ₁(N)]` is REPRESENTABLE over `𝔽_ℓ` for `N ≥ 4`, `ℓ ∤ N`** (sorry
leaf, NEW 2026-07-28) — the whole mathematical content of
`exists_fineGamma1Atlas` below, with the atlas bookkeeping removed.

TRUE, and classical: Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*,
Cor. 4.7.1 (the moduli problem `[Γ₁(N)]` is RIGID for `N ≥ 4`, and a rigid
representable-relatively-representable problem is representable), together
with 2.7.4 for relative representability of `[Γ₁(N)]` over the modular
stack.  Deligne–Rapoport IV.2 and Diamond–Im §8 state the same fact as
"`Y_1(N)` is a fine moduli scheme for `N ≥ 4`".  The universal family is
the restriction of the universal elliptic curve, and the statement here is
its defining property.

**Each hypothesis is load-bearing, and each fails the conclusion on its
own** (the underscores record only that a `sorry` consumes nothing):

* `_hN` is RIGIDITY, and it is sharp.  At `N ≤ 3` the pair `(E, P)` has a
  nontrivial automorphism — `[-1]` fixes `P` when `2P = 0`, i.e. at
  `N ≤ 2`, and at `N = 3` the curve `j = 0` carries `ζ₃` fixing a chosen
  `3`-torsion point — so a datum can be a base change of `dM` along a
  morphism in more than one way after an étale cover, `eq_of_isBaseChange`
  fails, and no fine moduli scheme exists.  This is the same rigidity that
  `IsCoarseModuliY1`'s own docstring records as the reason `Y_1(N)` is
  fine for `N ≥ 4`.
* `_hℓN` is invertibility of `N` on the base.  At `ℓ ∣ N` the naive
  problem is not even flat and the representable object is the *Drinfeld*
  `[Γ₁(N)]`, whose universal object is a different scheme; the section
  form of `PointOfExactOrder` used here is then not the right moduli
  problem at all.
* `_hℓ` is what makes `ZMod ℓ` a FIELD, hence `SpecF ℓ` the spectrum of a
  residue field.  At composite `ℓ` the base is not reduced-and-regular in
  the way the representability theorem wants; see the FAITHFULNESS AUDIT
  on the parent leaf, where the `ℓ = 0` and composite regimes are worked
  out.

**WHAT THIS DOES NOT CLAIM.**  Nothing about the coarse space `Y_1(N)`
being smooth, affine or geometrically connected, nothing about its
compactification, and nothing about `𝔽_ℓ`-points existing — those are
`exists_isCoarseModuliY1_isSmoothCurve` and its neighbours, and they are
separate leaves.  This is the bare universal property and no more.

**Refuting check** (in the sense the doctrine asks for): the leaf becomes
cheap the moment a functor-valued form of `Gamma1Datum` and a
representability theorem for rigid moduli problems exist in this tree.
`grep -rn "Rigid\|representable\|IsRepresentable" Fermat/FLT/ModularCurve/`
is what would refute the claim that neither exists here today. -/
theorem exists_isFineGamma1Moduli (N ℓ : ℕ) (_hN : 4 ≤ N) (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) :
    ∃ (M : Scheme.{0}) (strM : M ⟶ SpecF ℓ) (dM : Gamma1Datum N M),
      IsFineGamma1Moduli N strM dM :=
  sorry

/-- **A fine moduli scheme IS an atlas, with `M = Y` and `π = 𝟙`**
(PROVEN 2026-07-28) — the packaging half of the atlas cut, and it is
formal: no arithmetic, no geometry, no hypothesis on `N` or on the base.

This is the construction the FALSITY AUDIT below describes in words ("take
`M = Y`, `dM` the universal family, `cover` with `p = 𝟙` … and the trivial
deck group"), carried out.  Field by field:

* `classify` is the classifying morphism supplied by `exists_classify`,
  chosen with `Exists.choose`; the "over `S`" clause is its second
  component, so the value really is a `RelPoint`.
* `classify_natural` is `eq_of_isBaseChange` applied to the two
  presentations of `d'` as a base change of `dM`: directly, and through
  `IsBaseChangeOfGamma1.comp` of the given square with the classifying one.
  This is the only place the composition of base changes is used.
* `cover` is trivial with `p = 𝟙`: no fpqc extension is needed, and *that
  is exactly what representability means*.  The three descent properties
  of `𝟙` are instances.
* `quotient` is `φ` itself, because `classify strM dM = 𝟙` — by
  `eq_of_isBaseChange` against `IsBaseChangeOfGamma1.refl dM` — so the
  factorisation condition reads `𝟙 ≫ ψ = φ`.  The separation hypothesis is
  therefore unused, which is the formal shadow of "the deck group is
  trivial".

Note that `Y` and `M` are the same scheme here but remain *different
fields* of `Gamma1Atlas`, so the two are only definitionally equal; the
consumer below is written to respect that. -/
noncomputable def Gamma1Atlas.ofFineModuli {N : ℕ} {M S : Scheme.{0}} {strM : M ⟶ S}
    {dM : Gamma1Datum N M} (h : IsFineGamma1Moduli N strM dM) : Gamma1Atlas N S where
  Y := M
  str := strM
  classify g d := ⟨(h.exists_classify g d).choose, (h.exists_classify g d).choose_spec.1⟩
  classify_natural := by
    intro T' T hmap g g' hg d' d bc
    refine Subtype.ext ?_
    refine h.eq_of_isBaseChange (h.exists_classify g' d').choose_spec.2 ?_
    exact ⟨bc.comp (h.exists_classify g d).choose_spec.2.some⟩
  M := M
  strM := strM
  dM := dM
  cover := by
    intro T g d
    obtain ⟨m, hm, ⟨bc⟩⟩ := h.exists_classify g d
    exact ⟨T, 𝟙 T, d, m, inferInstance, inferInstance, inferInstance,
      by rw [Category.id_comp, hm], ⟨IsBaseChangeOfGamma1.refl d⟩, ⟨bc⟩⟩
  quotient := by
    intro Y' str' φ hφ _
    have hid : (h.exists_classify strM dM).choose = 𝟙 M :=
      h.eq_of_isBaseChange (h.exists_classify strM dM).choose_spec.2
        ⟨IsBaseChangeOfGamma1.refl dM⟩
    refine ⟨φ, ⟨hφ, ?_⟩, ?_⟩
    · show (h.exists_classify strM dM).choose ≫ φ = φ
      rw [hid, Category.id_comp]
    · rintro ψ ⟨-, hψ⟩
      rw [← hψ]
      show ψ = (h.exists_classify strM dM).choose ≫ ψ
      rw [hid]
      exact (Category.id_comp _).symm

/-- **There is a FINE Katz–Mazur atlas over `𝔽_ℓ`: one whose atlas map
`M ⟶ Y` lifts every `𝔽_ℓ`-point of `Y`** (**PROVEN 2026-07-28 by the
representability cut** — over the single leaf `exists_isFineGamma1Moduli`
above and the formal packaging `Gamma1Atlas.ofFineModuli`; formerly a
`sorry` leaf, and before that the REFUTED `nonempty_relPoint_atlas_of_relPoint`).

**RESTATED 2026-07-28, after the FALSITY AUDIT below refuted the previous
form.**  This leaf used to read

    ∀ A : Gamma1Atlas N (SpecF ℓ), RelPoint A.str (𝟙 _) →
      Nonempty (RelPoint A.strM (𝟙 _))

— "the atlas map is surjective on `𝔽_ℓ`-points, for EVERY atlas" — under the
name `nonempty_relPoint_atlas_of_relPoint`.  That statement is **FALSE**, and
false at the very atlas its own consumer fed it.  The audit is kept in full
because the fallacy is a reusable one.

## FALSITY AUDIT (2026-07-28) — the refuted `∀ A` form

**Counterexample: `N = 5`, `ℓ = 11`, `A` the Katz–Mazur atlas.**  All three
arithmetic hypotheses hold (`4 ≤ 5`, `11` prime, `¬ 11 ∣ 5`), and `A` is the
atlas that `exists_gamma1Rigidification` is *specified* to build and that
`exists_gamma1AffineModel` hands the parent: `M = Spec A = 𝔐([Γ₁(N)], [Γ(n)])`
with deck group `G = GL₂(ℤ/n)` for an auxiliary `n ≥ 3` prime to `N · ℓ` (see
that leaf's docstring, which names both `n ≥ 3` and `GL₂(ℤ/n)` explicitly).

* `A.Y(𝔽₁₁) ≠ ∅`.  Over `𝔽₁₁` the curve `y² = x³ + x + 7` has
  `E(𝔽₁₁) ≅ ℤ/15` (PARI/GP; `y² = x³ + 2x + 9` and `y² = x³ + 3x + 6` are two
  more), so it carries a point of exact order `5`.  That is a `Γ₁(5)`-datum
  over `𝔽₁₁`, and `A.classify` sends it to an `𝔽₁₁`-point of `A.Y`.
* `A.M(𝔽₁₁) = ∅`, **for every admissible auxiliary level `n`**.  An
  `𝔽₁₁`-point of `M` is a triple `(E, P, β)` over `𝔽₁₁` with `P` of exact
  order `5` and `β` a basis of `E[n]`; a rational basis forces
  `(ℤ/n)² ⊆ E(𝔽₁₁)`, hence `n² ∣ #E(𝔽₁₁)`, and `P` forces `5 ∣ #E(𝔽₁₁)`.  If
  `5 ∣ n` then `n² ≥ 25`; otherwise `5n² ∣ #E(𝔽₁₁)` and `5n² ≥ 45`.  Either
  way `#E(𝔽₁₁) ≥ 25`, against Hasse `#E(𝔽₁₁) ≤ 11 + 1 + 2√11 < 18.7`.  So no
  choice of `n ≥ 3` rescues the statement — this is not a "pick a better `n`"
  problem.
* A second, independent obstruction that needs no point count: whenever
  `ζ_n ∉ 𝔽_ℓ` (say `n = 3`, `ℓ ≡ 2 mod 3`, which `ℓ = 11` is), the Weil
  pairing of the universal level-`n` structure is a primitive `n`-th root of
  unity in `Γ(M, 𝒪_M)`, so `𝔽_ℓ(ζ_n) ⊆ Γ(M, 𝒪_M)` and `M` has no `𝔽_ℓ`-point
  whatsoever.  This file already records the fact, in the correction to
  `isDomain_of_gamma0Atlas`'s docstring above: `𝔐([Γ₁(N)], [Γ(n)])` acquires
  `φ(n)` geometric components permuted through the Weil pairing.

**Both routes the old docstring offered are fallacious**, and neither is
repairable:

* *"`M ⟶ Y` is a torsor under a finite étale group scheme and the point lifts
  after no extension at all."*  A torsor under a finite étale group scheme
  need NOT have a rational point — that is precisely what `H¹(𝔽_ℓ, G) ≠ 1`
  means for finite `G`, and the level-`n` cover is the standard example.  What
  rigidity of `[Γ₁(N)]` at `N ≥ 4` gives is that **`Y` is FINE**; it says
  nothing about `M(𝔽_ℓ)`.
* *"Lang: `H¹(𝔽_ℓ, G) = 1` for connected `G`."*  Lang's theorem requires `G`
  CONNECTED.  The deck group here is `GL₂(ℤ/n)`, finite and totally
  disconnected, so Lang does not apply — there is no connected group anywhere
  in this cut.

**Consequence for the fleet, and it is the reason this audit is long.**  The
refuted form and `exists_gamma1Rigidification` were **jointly unprovable in
their intended readings**: a prover who builds Katz–Mazur (8.1.1) as that leaf
specifies thereby constructs the counterexample above.  Neither leaf is wrong
on its own; the pair was.  Anyone auditing the other leaf should read this one.

## The repair, and why it is an `∃` rather than a patched `∀`

Nothing in `Gamma1Atlas` forces the rigidification to be nontrivial.  For
`N ≥ 4` the problem `[Γ₁(N)]` is rigid, hence representable over a base where
`N` is invertible (Katz–Mazur 4.7.0), so `Y_1(N)` **itself** is an atlas: take
`M = Y`, `dM` the universal family, `cover` with `p = 𝟙` (no extension is
needed, which is exactly representability), and the trivial deck group.  For
that atlas the lift of `y` is `y`.  So the true statement is that a fine atlas
EXISTS, and the consumer loses nothing by it: `IsCoarseModuliY1.universal`
transports the given coarse point onto whichever atlas this leaf produces,
which is what the parent already did.

The conclusion additionally pins the lift **over `y`** (`m ≫ π = y`), which
the refuted form deliberately did not.  That costs a prover nothing on the
fine atlas and it is what makes the leaf faithful: a lift landing on an
unrelated component no longer discharges it.

**What has to be built**: representability of `[Γ₁(N)]` over `𝔽_ℓ` for
`N ≥ 4`, packaged as a `Gamma1Atlas` with `π` an isomorphism.  Axis 4 of the
list above — "state representability as a separate leaf" — is therefore the
axis this now takes, and its objection (that a faithful statement needs the
moduli FUNCTOR written out) is answered by `Gamma1Atlas` itself, which is that
functor's data in the form this file already uses.

**NOT VACUOUS.**  A prover cannot dodge the `∀ y` by choosing an atlas whose
`Y` has no `𝔽_ℓ`-point: `cover` and `quotient` pin `A.Y` up to unique
isomorphism over `𝔽_ℓ` (`IsCoarseModuliY1.exists_inverse`), so `A.Y(𝔽_ℓ) = ∅`
holds for one atlas exactly when it holds for all of them, i.e. exactly when
`Y_1(N)(𝔽_ℓ)` is genuinely empty.  At `N = 5`, `ℓ = 11` it is not (the curve
above), so the fine atlas really has to be produced.  Conversely at
`2ℓ + 1 < N` the leaf is at least as hard as "`Y_1(N)` has no `𝔽_ℓ`-point",
which is the whole point of the witness row `(25, 3, 10)`.

**All three arithmetic hypotheses are load-bearing**: `_hN` is rigidity (at
`N ≤ 3` the pair `(E, P)` has extra automorphisms, `[Γ₁(N)]` is not
representable, and no fine atlas exists); `_hℓ` is what makes the base a FIELD
— see the FAITHFULNESS AUDIT on the parent leaf, where the `ℓ = 0` and `ℓ`
composite regimes are worked out — and `_hℓN` is invertibility of `N`, without
which `[Γ₁(N)]` is the Drinfeld problem and the atlas is a different
scheme.

## THE CUT (2026-07-28): the three hypotheses are now consumed ELSEWHERE

All three are passed straight to `exists_isFineGamma1Moduli` and consumed
there, which is the point of the cut: they are hypotheses of
REPRESENTABILITY, and they had nothing to do with the atlas packaging.
That the packaging needs none of them — `Gamma1Atlas.ofFineModuli` is
stated over an arbitrary base with no condition on `N` — is the evidence
that the seam is in the right place, and it is checked by the compiler
rather than asserted here.

The lift itself is then `y` unchanged: on the fine atlas `Y = M` and the
classifying map of the universal family is the identity
(`eq_of_isBaseChange` against `IsBaseChangeOfGamma1.refl dM`), so the
`∀ y ∃ m` clause — the clause that carried "all of the fineness content" —
is discharged by `m := y` and `Category.comp_id`.  That is not a weakening
of the leaf: it is what representability *says*, and the `∃ atlas` form was
restated precisely so that this would be the true statement.  What remains
genuinely open is `exists_isFineGamma1Moduli`, and nothing else. -/
theorem exists_fineGamma1Atlas (N ℓ : ℕ) (hN : 4 ≤ N) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) :
    ∃ A : Gamma1Atlas N (SpecF ℓ),
      ∀ y : RelPoint A.str (𝟙 (SpecF ℓ)),
        ∃ m : RelPoint A.strM (𝟙 (SpecF ℓ)),
          m.1 ≫ (A.classify A.strM A.dM).1 = y.1 := by
  obtain ⟨M, strM, dM, h⟩ := exists_isFineGamma1Moduli N ℓ hN hℓ hℓN
  refine ⟨Gamma1Atlas.ofFineModuli h, fun y => ⟨y, ?_⟩⟩
  have hid : (((Gamma1Atlas.ofFineModuli h).classify (Gamma1Atlas.ofFineModuli h).strM
        (Gamma1Atlas.ofFineModuli h).dM) :
      RelPoint (Gamma1Atlas.ofFineModuli h).strM (Gamma1Atlas.ofFineModuli h).strM).1
      = 𝟙 (Gamma1Atlas.ofFineModuli h).Y :=
    h.eq_of_isBaseChange (h.exists_classify strM dM).choose_spec.2
      ⟨IsBaseChangeOfGamma1.refl dM⟩
  rw [hid]
  exact Category.comp_id _

/-- **An `𝔽_ℓ`-point of `Y_1(N)_{𝔽_ℓ}` comes from a `Γ₁(N)`-datum**
(**PROVEN 2026-07-27 by the atlas cut**, over `exists_fineGamma1Atlas` and
`nonempty_gamma1Datum_baseChange`; formerly a single sorry leaf.  **Reassembled
2026-07-28** when the first of those two was refuted and restated — see its
FALSITY AUDIT; the statement proven here did not change).

The assembly, and it is three citations and no geometry:

1. `exists_fineGamma1Atlas` produces a `Gamma1Atlas` over `𝔽_ℓ` whose atlas map
   lifts `𝔽_ℓ`-points — this is where all three of `hN`, `hℓ` and `hℓN` are
   consumed;
2. `hc.universal` — the initiality clause of the GIVEN coarse space, applied to
   the atlas's own classifying map — produces the comparison morphism
   `u : Y ⟶ A.Y` over the base, and carries `y` across.  (`IsCoarseModuliY1.exists_inverse`
   packages the same step as an inverse PAIR, but it is declared later in this
   file, and only one direction is wanted here.);
3. the atlas leaf lifts that point to `M`, and the base-change leaf pulls the
   universal family `A.dM` back along it.

`hc` is consumed at step 2 and `y` at step 3.  Note that step 1 no longer goes
through `exists_gamma1AffineModel`: quantifying over the atlas is exactly what
the audit on step 1's leaf turned from false into true, so the atlas is now
CHOSEN by that leaf rather than handed to it.  `exists_gamma1AffineModel`
remains consumed by `exists_isCoarseModuliY1_isSmoothCurve`. -/
theorem exists_gamma1Datum_of_relPoint (N ℓ : ℕ) (hN : 4 ≤ N) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N)
    {Y : Scheme.{0}} {strY : Y ⟶ SpecF ℓ} (hc : IsCoarseModuliY1 N strY)
    (y : RelPoint strY (𝟙 (SpecF ℓ))) :
    Nonempty (Gamma1Datum N (SpecF ℓ)) := by
  obtain ⟨A, hA⟩ := exists_fineGamma1Atlas N ℓ hN hℓ hℓN
  obtain ⟨u, ⟨hu, -⟩, -⟩ := hc.universal A.str A.classify A.classify_natural
  obtain ⟨m, -⟩ := hA ⟨y.1 ≫ u, by rw [Category.assoc, hu]; exact y.2⟩
  obtain ⟨d', -⟩ := nonempty_gamma1Datum_baseChange A.dM m.1
  exact ⟨d'⟩

/-! #### The crude Weierstrass point count, and the one thing it needs from geometry

The two halves of "`#E(𝔽_ℓ) ≤ 2ℓ + 1` beats `N`" are separated here, and
the separation is the whole content of this sub-subsection: the COUNT is
elementary and is proved below outright, while the passage from a
`Gamma1Datum` to a plane cubic is a genuine piece of missing geometry and
is the single remaining leaf.

The count is stated for an arbitrary `WeierstrassCurve.Affine F` over a
finite field — no ellipticity, no Hasse bound, no `j`-invariant.  Its
proof is the classical one and nothing more: the fibre of the
`x`-coordinate over each of the `#F` values of `x` has at most two points,
because two affine points with the same `x` have `y`-coordinates related
by `Affine.Y_eq_of_X_eq`, and the point at infinity contributes the
`+ 1`.  Note that the `+ 1` is SHARP in the sense that matters — the
consumer's hypothesis is `2ℓ + 1 < N`, so a bound of `2ℓ + 2`, which is
what one gets by fibring the WHOLE of `Point` over `Option F`, would not
suffice; the point at infinity is therefore split off first. -/

/-- **The `x`-coordinate of an affine point, extended by junk at
infinity** (PROVEN, a definition).

Used only to fibre `Point` over the base field inside
`natCard_weierstrassPoint_le`.  The junk value at `zero` is harmless
there because `zero` is removed from the `Finset` before the fibration. -/
def weierstrassXCoord {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    W.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- **The `y`-coordinate of an affine point, extended by junk at
infinity** (PROVEN, a definition).  Companion of `weierstrassXCoord`;
it is the map along which each `x`-fibre is shown to have at most two
elements. -/
def weierstrassYCoord {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    W.Point → F
  | .zero => 0
  | .some _ y _ => y

/-- **A point of a Weierstrass curve is determined by its affine
coordinates** (PROVEN, a definition): the encoding whose injectivity
below supplies finiteness of `Point` over a finite field.

`Nonsingular` is a `Prop`, so the two constructor arguments `x` and `y`
determine the constructor application outright. -/
def weierstrassPointEnc {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    W.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

/-- **`weierstrassPointEnc` is injective** (PROVEN).

This is what makes `Point` finite over a finite field without any appeal
to properness or to a scheme-theoretic finiteness statement. -/
theorem weierstrassPointEnc_injective {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    Function.Injective (weierstrassPointEnc W) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hEq
  · rfl
  · simp [weierstrassPointEnc] at hEq
  · simp [weierstrassPointEnc] at hEq
  · simp only [weierstrassPointEnc, Option.some.injEq, Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    rfl

/-- **The crude Weierstrass point count `#W(F) ≤ 2·#F + 1`** (PROVEN
2026-07-27, for an ARBITRARY Weierstrass curve over an arbitrary finite
field).

No ellipticity, no Hasse bound, no `√ℓ`: for each of the `#F` values of
`x` the defining equation is a monic quadratic in `y`, so it has at most
two roots, and `Affine.Y_eq_of_X_eq` is exactly that statement in
mathlib's vocabulary (`y₁ = y₂ ∨ y₁ = W.negY x y₂`).  Adding the point at
infinity gives `2·#F + 1`.

Deliberately stated for `WeierstrassCurve.Affine F` and not for an
elliptic curve: singular Weierstrass curves satisfy it too, the proof
never looks at `Δ`, and the weaker hypothesis is what lets
`isEmpty_gamma1Datum_finiteField`'s leaf below get away with producing
any plane cubic at all.

This is NOT `hasse_bound_natCard_affine_point` (`MazurTorsion.lean`,
which is an open leaf with its own owner) and does not depend on it: the
Hasse bound `|ℓ + 1 - #E(𝔽_ℓ)| ≤ 2√ℓ` is strictly sharper and strictly
harder, and nothing in the `Γ₁` cluster needs it. -/
theorem natCard_weierstrassPoint_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    Nat.card W.Point ≤ 2 * Fintype.card F + 1 := by
  classical
  letI : Fintype W.Point :=
    Fintype.ofInjective (weierstrassPointEnc W) (weierstrassPointEnc_injective W)
  have hfib : ∀ b : F,
      (Finset.filter (fun P => weierstrassXCoord W P = b)
        (Finset.univ.erase (WeierstrassCurve.Affine.Point.zero : W.Point))).card ≤ 2 := by
    intro b
    rcases Finset.eq_empty_or_nonempty
        (Finset.filter (fun P => weierstrassXCoord W P = b)
          (Finset.univ.erase (WeierstrassCurve.Affine.Point.zero : W.Point)))
        with he | ⟨P₀, hP₀⟩
    · simp [he]
    · simp only [Finset.mem_filter, Finset.mem_erase] at hP₀
      obtain ⟨⟨hne, -⟩, hxb⟩ := hP₀
      cases P₀ with
      | zero => exact absurd rfl hne
      | some x y h =>
        simp only [weierstrassXCoord] at hxb
        subst hxb
        refine le_trans (Finset.card_le_card_of_injOn (weierstrassYCoord W)
          (t := ({y, W.negY x y} : Finset F)) ?_ ?_) ?_
        · intro P hP
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hP
          obtain ⟨⟨hPne, -⟩, hxP⟩ := hP
          cases P with
          | zero => exact absurd rfl hPne
          | some x' y' h' =>
            simp only [weierstrassXCoord] at hxP
            subst hxP
            simp only [weierstrassYCoord, Finset.mem_coe, Finset.mem_insert,
              Finset.mem_singleton]
            exact WeierstrassCurve.Affine.Y_eq_of_X_eq h'.left h.left rfl
        · intro P hP Q hQ hPQ
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hP hQ
          obtain ⟨⟨hPne, -⟩, hxP⟩ := hP
          obtain ⟨⟨hQne, -⟩, hxQ⟩ := hQ
          cases P with
          | zero => exact absurd rfl hPne
          | some x₁ y₁ h₁ =>
            cases Q with
            | zero => exact absurd rfl hQne
            | some x₂ y₂ h₂ =>
              simp only [weierstrassXCoord] at hxP hxQ
              simp only [weierstrassYCoord] at hPQ
              subst hxP; subst hxQ; subst hPQ; rfl
        · exact (Finset.card_insert_le _ _).trans (by simp)
  have hmain : (Finset.univ.erase (WeierstrassCurve.Affine.Point.zero : W.Point)).card
      ≤ 2 * Fintype.card F := by
    refine le_trans (Finset.card_le_mul_card_image_of_maps_to (f := weierstrassXCoord W)
      (t := (Finset.univ : Finset F)) (fun a _ => Finset.mem_univ _) 2 (fun b _ => hfib b)) ?_
    simp
  have hpos : 0 < Fintype.card W.Point := Fintype.card_pos_iff.mpr ⟨.zero⟩
  have hcard : (Finset.univ.erase (WeierstrassCurve.Affine.Point.zero : W.Point)).card
      = Fintype.card W.Point - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    rfl
  rw [Nat.card_eq_fintype_card]
  omega

/-- **An abelian scheme of relative dimension one over `Spec 𝔽_ℓ` has a
Weierstrass model** (sorry leaf, introduced 2026-07-28 as the GEOMETRY
half of `exists_weierstrassEquiv_of_gamma1Datum` below).  **This leaf IS
Riemann–Roch**; the sibling leaf carries none of it.

TRUE — Silverman *AEC* III.3.1.  `ab.proper`, `ab.smooth` and
`ab.connected` make `f` a proper smooth geometrically connected curve
over `𝔽_ℓ` (`_hdim` supplies the relative dimension), and
`ab.zero (𝟙 (SpecF ℓ))` is an `𝔽_ℓ`-RATIONAL point `O` on it.  A group
scheme has trivial relative tangent bundle, hence arithmetic genus one,
so Riemann–Roch gives `dim L(n[O]) = n` for `n ≥ 1`; picking
`x ∈ L(2[O]) ∖ L([O])` and `y ∈ L(3[O]) ∖ L(2[O])`, the seven monomials
`1, x, y, x², xy, y², x³` lie in the six-dimensional `L(6[O])` and so
satisfy a linear relation in which `y²` and `x³` occur with nonzero
coefficients (they alone have pole order exactly six).  Scaling gives a
Weierstrass equation, `|3·[O]|` embeds the curve in `ℙ²` with
`O ↦ [0 : 1 : 0]`, and deleting `O` leaves the affine chart
`Spec W.toAffine.CoordinateRing` — which is the middle and last
conjuncts.

**THE ℚ-SIDE CHAIN CANNOT BE REUSED, and this was checked rather than
assumed.**  `EllipticScheme.lean` has the same statement over `ℚ`
(`exists_weierstrassModel_of_ellipticScheme`, line 9395), assembled from
`exists_affineComplement_zeroSection`,
`exists_weierstrassRingEquiv_of_affineComplement` and
`isElliptic_of_isOpenImmersion_coordinateRing`.  **All three are
themselves `sorry`, and all four are hardcoded to
`Spec (CommRingCat.of ℚ)`** — not stated over a field variable — so there
is nothing to instantiate at `ZMod ℓ`.  Generalising that chain in place
is NOT the cheap move it looks like: its `≃+` half
(`exists_geomFibreAddEquiv_of_weierstrassModel`) is genuinely PROVEN over
`ℚ` and its proof runs through `hom_ext_spec_rat`, `projGroupLaw` and
`exists_affineChart_projModel`, so widening the base would put a proven
theorem back into the open set.  Hence the deliberate 𝔽_ℓ-local restatement
here.  If that chain is ever made base-generic, THIS leaf and its sibling
are exactly the two declarations that should be deleted in favour of it.

`_hdim` is LOAD-BEARING for truth even though a `sorry` body cannot
consume it: without relative dimension one an abelian scheme is an
abelian variety of higher dimension and has no plane-cubic model at all.
It is underscore-prefixed only to keep the tree warning-clean, matching
the convention of the three ℚ-side leaves named above. -/
theorem exists_weierstrassModel_of_abelianSchemeStruct_finiteField {ℓ : ℕ} [Fact ℓ.Prime]
    {A : Scheme.{0}} {f : A ⟶ SpecF ℓ} (ab : AbelianSchemeStruct f)
    (_hdim : SmoothOfRelativeDimension 1 f) :
    ∃ (W : WeierstrassCurve (ZMod ℓ)) (_ : W.IsElliptic),
      ∃ ι : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ A,
        IsOpenImmersion ι ∧
          ι ≫ f = Spec.map (CommRingCat.ofHom
            (algebraMap (ZMod ℓ) W.toAffine.CoordinateRing)) ∧
          Set.range ι.base = (Set.range (ab.zero (𝟙 (SpecF ℓ))).1.base)ᶜ :=
  sorry

/-- **A Weierstrass model of an abelian scheme over `Spec 𝔽_ℓ` computes
its `𝔽_ℓ`-SECTIONS** (sorry leaf, introduced 2026-07-28 as the TRANSPORT
half of `exists_weierstrassEquiv_of_gamma1Datum` below).  No Riemann–Roch
here: the model is handed over as `_hmodel`.

TRUE, and it is two separate facts glued by the model hypothesis.

*The bijection.*  A section `s : Spec 𝔽_ℓ ⟶ A` of `f` has a single point
in its image, which by the range clause of `_hmodel` lies either in the
image of the zero section or in `Set.range ι.base` — and an open immersion
is a monomorphism through which a morphism factors exactly when its
topological image is contained in the range.  So `s` is either
`ab.zero (𝟙 _)` or factors uniquely through `ι`, and a factorisation
through `ι` over `𝔽_ℓ` is an `𝔽_ℓ`-algebra map
`W.toAffine.CoordinateRing → 𝔽_ℓ`, i.e. a pair `(x, y)` satisfying the
Weierstrass equation.  That is exactly the `zero`/`some x y h` case split
of `WeierstrassCurve.Affine.Point`.

*The additivity.*  This is the real content and it is where a successor
should expect to spend the effort: `ab.add` is the abstract group law of
the abelian scheme and `W.toAffine.Point`'s is the chord-and-tangent law,
and they must be shown to agree.  The argument is RIGIDITY — two algebraic
group structures on the same proper variety sharing an identity coincide —
which is how the ℚ side does it (`relPointPost_add`, consumed by
`exists_geomFibreAddEquiv_of_weierstrassModel`).

**This is STRICTLY EASIER than its ℚ-side counterpart, which is why it is
not stated by base change from it.**  `exists_geomFibreAddEquiv_of_weierstrassModel`
produces a `Γ_ℚ`-EQUIVARIANT `≃+` on `ℚ̄`-points, because the `Γ₀` route
descends a subgroup and so must work on the geometric fibre.  Here the
level structure is already an `𝔽_ℓ`-section, the consumer counts
`𝔽_ℓ`-points, and there is no Galois clause at all — a geometric-fibre
equivalence would only have to be pushed back down again.

`Nonempty` rather than a chosen equivalence because the consumer uses only
`AddEquiv.addOrderOf_eq`, which any additive equivalence supplies; nothing
downstream inspects which one.  `_hmodel` is load-bearing and NOT
droppable: without it `W` is an arbitrary elliptic curve over `𝔽_ℓ` and the
conclusion is plainly false (take `f` with `#RelPoint = 1` and `W` with
`#W(𝔽_ℓ) = 5`). -/
theorem exists_relPointAddEquiv_of_weierstrassModel_finiteField {ℓ : ℕ} [Fact ℓ.Prime]
    (W : WeierstrassCurve (ZMod ℓ)) [W.IsElliptic]
    {A : Scheme.{0}} {f : A ⟶ SpecF ℓ} (ab : AbelianSchemeStruct f)
    (_hmodel : ∃ ι : Spec (CommRingCat.of W.toAffine.CoordinateRing) ⟶ A,
      IsOpenImmersion ι ∧
        ι ≫ f = Spec.map (CommRingCat.ofHom
          (algebraMap (ZMod ℓ) W.toAffine.CoordinateRing)) ∧
        Set.range ι.base = (Set.range (ab.zero (𝟙 (SpecF ℓ))).1.base)ᶜ) :
    letI := ab.addCommGroup (𝟙 (SpecF ℓ))
    Nonempty (RelPoint f (𝟙 (SpecF ℓ)) ≃+ W.toAffine.Point) :=
  sorry

/-- **A `Γ₁(N)`-datum over `𝔽_ℓ` gives a plane cubic over `𝔽_ℓ` carrying
a rational point of exact order `N`** (PROVEN 2026-07-28 over the two
leaves immediately above; a single sorry leaf until then, and the
converse direction of `exists_ellipticScheme_of_weierstrass`).

**Restated 2026-07-28: the ORDER is no longer part of this leaf.**  It
used to conclude `∃ P : W.toAffine.Point, addOrderOf P = N`, bundling
Riemann–Roch together with the transport of `d.pt.geom_order` from the
geometric fibre down to `𝔽_ℓ`.  That transport is ARITHMETIC, not
geometry, and it is now proven outright in
`addOrderOf_relPointOfSection_gamma1Datum` below — over `epi_specAlgClos`
and `relPoint_pre_injective_of_epi` (`X0.lean`, both PROVEN), which say
that `Spec 𝔽̄_ℓ ⟶ Spec 𝔽_ℓ` is an epimorphism and hence that
`RelPoint d.f (𝟙 _) → RelPoint d.f (specAlgClos 𝔽_ℓ)` is injective; being
additive by `pre_add`/`pre_zero` it then preserves `addOrderOf`.  What is
asked for here is the additive equivalence and nothing else, so a
successor faces geometry ONLY — which the paragraph below already claimed
and which, before this split, was not quite true.

TRUE.  An abelian scheme of relative dimension one over `Spec 𝔽_ℓ` with a
zero section IS an elliptic curve over `𝔽_ℓ`, hence has a Weierstrass
model `W` with `W(𝔽_ℓ) ≃+ RelPoint d.f (𝟙 (SpecF ℓ))`, which is literally
the conclusion.

**HOW IT IS PROVEN, and where the content went.**  `X0.lean` builds
`exists_ellipticScheme_of_weierstrass`, which goes from a plane cubic to
an abelian scheme; the direction needed here is the CONVERSE — a
Weierstrass presentation of a given abelian scheme.  That converse is now
split into the two leaves immediately above, along the seam the ℚ-side
chain already uses:

1. `exists_weierstrassModel_of_abelianSchemeStruct_finiteField` — **the
   Riemann–Roch half**, producing the cubic `W` together with the open
   immersion of its affine chart onto the complement of the zero section;
2. `exists_relPointAddEquiv_of_weierstrassModel_finiteField` — **the
   transport half**, reading the `𝔽_ℓ`-sections off that model, whose real
   content is that the abstract group law agrees with the chord-and-tangent
   one (rigidity).

The assembly below carries nothing of its own, which is the point of the
split: neither `N` nor the level structure `d.pt` appears in either leaf,
so both are stated in `AbelianSchemeStruct` vocabulary and are reusable
for any abelian scheme over `Spec 𝔽_ℓ`.  The arithmetic that used to be
bundled here is `addOrderOf_relPointOfSection_gamma1Datum` below and is
PROVEN; the crude point bound is `natCard_weierstrassPoint_le` above and
is PROVEN.

**Faithfulness check performed at the split** (2026-07-28): the statement
is TRUE and not vacuous, and properness is what makes it so.
`AbelianSchemeStruct` carries `proper`, `smooth` and `connected` as
FIELDS, so `𝔾ₐ` and `𝔾ₘ` over `𝔽_ℓ` — which are smooth of relative
dimension one and carry group laws — are excluded, as they must be, since
neither is an elliptic curve.  Had properness been absent the leaf would
have been false rather than merely open.

Classically the converse is Riemann–Roch on the genus-one curve `E`:
`ℒ(3·O)` is three-dimensional and a basis `1, x, y` embeds `E` as a plane
cubic in Weierstrass form.  That is the content of the first of the two
leaves; the second is the group-law comparison.

### ROUTE AUDIT CORRECTION (2026-07-28) — "it exists nowhere in this tree" is FALSE

**STATUS UPDATE (2026-07-29): this node is now PROVEN and the audit below is
retained as the record of WHY the cut was made locally.**  Every factual
claim in it was re-checked and holds — the ℚ-side chain exists, its base is
hard-wired, and all three of its leaves are still `sorry`.  What was NOT
adopted is its recommendation to base-generalize that cut in place, for two
reasons the audit does not weigh:

* the audit's own **STRUCTURAL BLOCKER** (below) is the decisive one — citing
  any `EllipticScheme.lean` name from here needs an import change, i.e. a
  cone-growth decision.  Restating the two leaves locally, in
  `AbelianSchemeStruct` vocabulary, avoids it entirely: this file's build is
  green with no import change at all;
* base-generalizing would also drag in the `≃+` half
  (`exists_geomFibreAddEquiv_of_weierstrassModel`), which is genuinely PROVEN
  over `ℚ` through `hom_ext_spec_rat`, `projGroupLaw` and
  `exists_affineChart_projModel` — widening its base would put a proven
  theorem back into the open set.

The audit's point 1 is nonetheless the right long-term shape, and the two
leaves above say so in their own docstrings: **if that chain is ever made
base-generic, those two leaves are exactly what should be deleted in favour
of it.**  The `𝔽_ℓ` analogue of `hom_ext_spec_rat` the audit predicts would
be needed (`ℤ → ZMod ℓ` is surjective) is not needed by the local route.

The sentence removed above said the converse bridge "exists nowhere in
this tree, in mathlib, or in `~/cs/FLT`".  Two of the three clauses are
right; the first is not, and believing it costs a successor the design of
a decomposition that has already been designed and reviewed.

`Fermat/FLT/ModularCurve/EllipticScheme.lean` carries
**`exists_weierstrassModel_of_ellipticScheme`** — precisely this converse,
an `AbelianSchemeStruct f` with `SmoothOfRelativeDimension 1 f` yielding
`E : WeierstrassCurve _`, `E.IsElliptic`, and an open immersion of
`Spec E.toAffine.CoordinateRing` onto the complement of the zero section
— together with its assembly and its cut into **three named leaves**:
`exists_affineComplement_zeroSection` (affineness),
`exists_weierstrassRingEquiv_of_affineComplement` (the Riemann–Roch
third) and `isElliptic_of_isOpenImmersion_coordinateRing` (the
discriminant third).

So the honest statement of the gap is a CONJUNCTION of two things, and
neither is "design a decomposition":

1. **The base is hard-wired to `ℚ`.**  Every one of those four signatures
   reads `f : A ⟶ Spec (CommRingCat.of ℚ)` and `WeierstrassCurve ℚ`;
   this leaf needs `SpecF ℓ` and `WeierstrassCurve (ZMod ℓ)`.  The work
   is to base-generalize an EXISTING cut, reusing its assembly verbatim.
   One `ℚ`-specific convenience does survive the move: the assembly gets
   its structure-morphism conjunct free from `hom_ext_spec_rat` (any two
   morphisms to `Spec ℚ` agree, because `ℤ → ℚ` is a ring epimorphism);
   the same holds over `ZMod ℓ`, where `ℤ → ZMod ℓ` is surjective, so an
   `𝔽_ℓ` analogue of that lemma is cheap and is the only piece of the
   assembly that has to be re-proven rather than transported.
2. **The Riemann–Roch content is still genuinely OPEN**, so the
   docstring's *conclusion* stands even though its premise does not: all
   three leaves above are `sorry` at the time of writing, i.e.
   `exists_weierstrassModel_of_ellipticScheme` is PROVEN only in the
   ASSEMBLY sense (no direct sorry, transitively sorried).  Nothing here
   can be discharged by citing it, over `ℚ` or over `𝔽_ℓ`.

**A STRUCTURAL BLOCKER a successor must budget for, verified by a
two-way reproduction on 2026-07-28.**  None of those names is visible
from this file: `X0.lean` reaches `EllipticScheme.lean` through a
deliberately NON-`public` `import` (`X0.lean`'s import block; the
intent is recorded on
`exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme`, which
notes that keeping `proj`/`projToSpec` out of its conjuncts is what
"keeps `X0.lean`'s import non-public").  A scratch module importing only
`Fermat.FLT.ModularCurve.X1` and mentioning
`Fermat.exists_weierstrassModel_of_ellipticScheme` fails with
`Unknown identifier`; adding
`public import Fermat.FLT.ModularCurve.EllipticScheme` makes the same
module compile clean, `EXIT=0`.  This is the private-import failure whose
privacy sits in an INTERMEDIATE module, so it bites proof bodies and not
merely signatures.  Closing this leaf therefore requires an import change
here (or a hoist), which is a cone-growth decision, not a local one.

The check that would refute this audit: `grep -n "sorry"` at the three
`EllipticScheme.lean` leaves named above, and re-running the two-way
scratch.  If those leaves have closed and been base-generalized, this
leaf becomes an assembly.

`W.IsElliptic` is asked for even though the count above does not use it,
because it is TRUE of the genuine model and asking for less would let the
leaf be discharged by a degenerate cubic that carries none of the
geometry.  `[Fact ℓ.Prime]` rather than `ℓ.Prime` because the statement
mentions `WeierstrassCurve (ZMod ℓ)`, whose `Field` instance — and hence
the group law on `Point` — is only available under the `Fact`.

Note the equivalence is asked for at the base point `𝟙 (SpecF ℓ)`, i.e.
between `W(𝔽_ℓ)` and the SECTIONS of `d.f`, and NOT on geometric fibres.
That is the difference from `X0.lean`'s ℚ-side
`exists_weierstrassCurve_of_abelianSchemeStruct`, which produces a
`Γ_ℚ`-equivariant `≃+` on `ℚ̄`-points because the `Γ₀` route descends a
SUBGROUP; here the level structure is already a section, so the `𝔽_ℓ`-points
are what the consumer counts and a geometric-fibre equivalence would have
to be pushed back down again.

**`_d` IS LOAD-BEARING — do not "simplify" the statement by dropping it**
(guard inherited at merge from the note that stood on
`exists_weierstrassPointOfOrder_of_gamma1Datum` before this restatement).
Without the datum the statement would read "for every `N` and every prime
`ℓ` there is an elliptic curve over `𝔽_ℓ` with a point of exact order
`N`", which is **FALSE**, and refuted by this module's own
`natCard_weierstrassPoint_le`: at `(N, ℓ) = (25, 3)` any Weierstrass
curve over `𝔽_3` has at most `2·3 + 1 = 7` points, so it has no point of
order `25`.  That is the same inequality `isEmpty_gamma1Datum_finiteField`
below turns into its conclusion — so a successor who dropped the datum would
be deriving `False` from the very bound the cluster exists to exploit.
**That guard is now discharged rather than merely asserted**: the binder is
`d`, not `_d`, because the proof below consumes it (`d.ab` and
`d.relativeDimensionOne`).  Note this is NOT in tension with the two leaves
being stated without `N`: they hand over an *abelian scheme* and claim no
point of any order, so the false statement above — which needs the level
structure to be dropped as well — is not among their consequences. -/
theorem exists_weierstrassEquiv_of_gamma1Datum (N ℓ : ℕ) [Fact ℓ.Prime]
    (d : Gamma1Datum N (SpecF ℓ)) :
    letI := d.ab.addCommGroup (𝟙 (SpecF ℓ))
    ∃ W : WeierstrassCurve (ZMod ℓ), W.IsElliptic ∧
      Nonempty (RelPoint d.f (𝟙 (SpecF ℓ)) ≃+ W.toAffine.Point) := by
  obtain ⟨W, hW, hmodel⟩ :=
    exists_weierstrassModel_of_abelianSchemeStruct_finiteField d.ab d.relativeDimensionOne
  haveI := hW
  exact ⟨W, hW, exists_relPointAddEquiv_of_weierstrassModel_finiteField W d.ab hmodel⟩

/-- **The `Γ₁(N)`-level section has additive order exactly `N` already as
an `𝔽_ℓ`-SECTION**, not merely on the geometric fibre (PROVEN 2026-07-28;
formerly the arithmetic half of
`exists_weierstrassPointOfOrder_of_gamma1Datum`'s leaf).

`PointOfExactOrder.geom_order` states the order at every algebraically
closed `K` and every `K`-point of the base, which is what makes the
condition insensitive to the base; the consumer here needs it at the base
`𝔽_ℓ` itself.  The passage down is three facts, all already in the tree:

* `RelPoint.pre (specAlgClos 𝔽_ℓ) _` carries a section to its value on the
  geometric fibre, and is ADDITIVE by `AbelianSchemeStruct.pre_add` and
  `pre_zero`;
* it is INJECTIVE, because `Spec 𝔽̄_ℓ ⟶ Spec 𝔽_ℓ` is faithfully flat hence
  an epimorphism of schemes (`epi_specAlgClos`, `X0.lean`) and
  `relPoint_pre_injective_of_epi` cancels it;
* an injective additive map preserves `addOrderOf`
  (`addOrderOf_injective`).

Note that BOTH directions are needed and neither is free: additivity alone
gives only `N ∣ addOrderOf (sec)`, since the image of the section has order
`N`; it is injectivity that supplies `N • sec = 0` and hence the reverse
divisibility.  This is the `Γ₁`, `𝔽_ℓ` mirror of the step
`exists_pointOfExactOrder_of_geomPt` performs over `ℚ` — there through
`exists_injective_pre_geomBase`, which is available only because `ℚ` is
initial among rings; here the single base `𝔽̄_ℓ` is fixed, so the plain
epimorphism suffices and no initiality is needed. -/
theorem addOrderOf_relPointOfSection_gamma1Datum (N ℓ : ℕ) [Fact ℓ.Prime]
    (d : Gamma1Datum N (SpecF ℓ)) :
    letI := d.ab.addCommGroup (𝟙 (SpecF ℓ))
    addOrderOf (RelPoint.ofSection d.pt.sec d.pt.sec_comp (𝟙 (SpecF ℓ))) = N := by
  letI := d.ab.addCommGroup (𝟙 (SpecF ℓ))
  have hg : specAlgClos (ZMod ℓ) ≫ 𝟙 (SpecF ℓ) = specAlgClos (ZMod ℓ) := Category.comp_id _
  letI := d.ab.addCommGroup (specAlgClos (ZMod ℓ))
  let Φ : RelPoint d.f (𝟙 (SpecF ℓ)) →+ RelPoint d.f (specAlgClos (ZMod ℓ)) :=
    { toFun := fun w => RelPoint.pre (specAlgClos (ZMod ℓ)) hg w
      map_zero' := d.ab.pre_zero _ hg
      map_add' := fun a b => d.ab.pre_add _ hg a b }
  have hinj : Function.Injective Φ := relPoint_pre_injective_of_epi _ hg
  have hΦ : Φ (RelPoint.ofSection d.pt.sec d.pt.sec_comp (𝟙 (SpecF ℓ)))
      = RelPoint.ofSection d.pt.sec d.pt.sec_comp (specAlgClos (ZMod ℓ)) := by
    apply Subtype.ext
    show specAlgClos (ZMod ℓ) ≫ 𝟙 (SpecF ℓ) ≫ d.pt.sec = specAlgClos (ZMod ℓ) ≫ d.pt.sec
    rw [Category.id_comp]
  rw [← addOrderOf_injective Φ hinj, hΦ]
  exact d.pt.geom_order (AlgebraicClosure (ZMod ℓ)) (specAlgClos (ZMod ℓ))

/-- **A `Γ₁(N)`-datum over `𝔽_ℓ` gives a plane cubic over `𝔽_ℓ` carrying
a rational point of exact order `N`** (PROVEN 2026-07-28 over
`exists_weierstrassEquiv_of_gamma1Datum` and
`addOrderOf_relPointOfSection_gamma1Datum`; a single sorry leaf until
then).

The assembly is two lines and carries no content of its own, which is the
point of the split: the level section is a relative point of order `N`
(the second citation), and the Weierstrass equivalence carries it to a
point of `W(𝔽_ℓ)` of the same order (`AddEquiv.addOrderOf_eq`).  The
statement is unchanged, so `isEmpty_gamma1Datum_finiteField` below is
untouched; the hypothesis binder is now `d` rather than `_d` because the
proof uses it. -/
theorem exists_weierstrassPointOfOrder_of_gamma1Datum (N ℓ : ℕ) [Fact ℓ.Prime]
    (d : Gamma1Datum N (SpecF ℓ)) :
    ∃ W : WeierstrassCurve (ZMod ℓ), W.IsElliptic ∧
      ∃ P : W.toAffine.Point, addOrderOf P = N := by
  letI := d.ab.addCommGroup (𝟙 (SpecF ℓ))
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_weierstrassEquiv_of_gamma1Datum N ℓ d
  refine ⟨W, hW, e (RelPoint.ofSection d.pt.sec d.pt.sec_comp (𝟙 (SpecF ℓ))), ?_⟩
  rw [AddEquiv.addOrderOf_eq]
  exact addOrderOf_relPointOfSection_gamma1Datum N ℓ d

/-- **There is no `Γ₁(N)`-datum over `𝔽_ℓ` once `N` exceeds the crude
point bound `2ℓ + 1`** (PROVEN 2026-07-27 over
`exists_weierstrassPointOfOrder_of_gamma1Datum`; was a sorry leaf).

TRUE, and this is the finding that reshapes the level-`25` budget: a
`Γ₁(N)`-datum over `𝔽_ℓ` is an elliptic curve `E/𝔽_ℓ` together with an
`𝔽_ℓ`-RATIONAL point of exact order `N`, so `N ∣ #E(𝔽_ℓ)` and in
particular `N ≤ #E(𝔽_ℓ)`.  Hasse gives `#E(𝔽_ℓ) ≤ ℓ + 1 + 2√ℓ`, but the
crude Weierstrass count already suffices and is what is stated: at most
two `y` for each of the `ℓ` values of `x`, plus the point at infinity, so
`#E(𝔽_ℓ) ≤ 2ℓ + 1`.  At `(N, ℓ) = (25, 3)` that is `25 > 7`.  **So no
Hasse, no Eichler–Shimura, no Hecke operators.**  Corroborated
numerically: `G₂₅ mod 3` vanishes on `𝔽_3 × 𝔽_3` only at `(0, 0)`, which
has `b = 0`.

WHAT REMAINED, when this was a leaf, was not the arithmetic but the
passage from the scheme-level datum to a Weierstrass model — and that is
now isolated as `exists_weierstrassPointOfOrder_of_gamma1Datum` above,
which is the only `sorry` this theorem consumes.  The arithmetic half is
`natCard_weierstrassPoint_le` and is PROVEN outright.  So the two
sentences of the old docstring have become two declarations, and the
budget assertion above is now mechanically checked: the count really does
cost nothing beyond `Affine.Y_eq_of_X_eq`.

The assembly is three steps and no more: the leaf gives `(W, P)` with
`addOrderOf P = N`; `Point` is finite because `weierstrassPointEnc` is
injective; and `addOrderOf_le_card` together with
`natCard_weierstrassPoint_le` and `ZMod.card` gives
`N ≤ 2ℓ + 1`, against the hypothesis.  Note it is `addOrderOf_le_card`
and not divisibility that is used — `N ∣ #E(𝔽_ℓ)` is true and would also
do, but the inequality needs strictly less.

Note the statement is about `Gamma1Datum` alone — no compactification, no
coarse space, no cusp.  That is deliberate: it is the half a successor
can attack with elliptic-curve theory and nothing else. -/
theorem isEmpty_gamma1Datum_finiteField (N ℓ : ℕ) (hℓ : ℓ.Prime) (hN : 2 * ℓ + 1 < N) :
    IsEmpty (Gamma1Datum N (SpecF ℓ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  refine ⟨fun d => ?_⟩
  obtain ⟨W, -, P, hP⟩ := exists_weierstrassPointOfOrder_of_gamma1Datum N ℓ d
  haveI : Finite W.toAffine.Point :=
    Finite.of_injective (weierstrassPointEnc W.toAffine)
      (weierstrassPointEnc_injective W.toAffine)
  have h1 : addOrderOf P ≤ Nat.card W.toAffine.Point := addOrderOf_le_card
  have h2 : Nat.card W.toAffine.Point ≤ 2 * Fintype.card (ZMod ℓ) + 1 :=
    natCard_weierstrassPoint_le W.toAffine
  rw [ZMod.card] at h2
  omega

/-- **`Y_1(N)` has no `𝔽_ℓ`-point once `2ℓ + 1 < N`** (PROVEN 2026-07-27,
by joining the two halves above).

`X_1(N)` has no non-cuspidal `𝔽_ℓ`-point: a rational point of the coarse
space gives a datum (`exists_gamma1Datum_of_relPoint`), and there is no
datum (`isEmpty_gamma1Datum_finiteField`).  The join is trivial because
the two halves were stated to meet at `Gamma1Datum N (SpecF ℓ)`.

`hℓN : ¬ ℓ ∣ N` is threaded (2026-07-27) purely to supply
`exists_gamma1Datum_of_relPoint`'s repaired hypothesis; see that leaf for why
it belongs there.  It comes free from `x1WitnessTable_spec`, whose third
component this file previously discarded. -/
theorem isEmpty_relPoint_y1_finiteField (N ℓ : ℕ) (hN4 : 4 ≤ N) (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (hN : 2 * ℓ + 1 < N)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    IsEmpty (RelPoint strY (𝟙 (SpecF ℓ))) :=
  ⟨fun y => (isEmpty_gamma1Datum_finiteField N ℓ hℓ hN).elim
    (exists_gamma1Datum_of_relPoint N ℓ hN4 hℓ hℓN h.coarse y).some⟩

/-! ### `𝔽_ℓ`-points as points of residue degree one

The `𝔽_ℓ`-side mirror of the `ℚ`-side residue-field dictionary above, and the
reason `card_cusp_x1_finiteField` no longer has to mention sections at all.
Over the PRIME field `𝔽_ℓ` the dictionary is unusually clean, and both places
where it is cleaner than over a general base are used below:

* every morphism `Spec 𝔽_ℓ ⟶ Spec 𝔽_ℓ` is the identity (`RingHom.ext_zmod`),
  so the `RelPoint` side condition `σ ≫ strX = 𝟙` is automatic and
  `RelPoint strX (𝟙 (SpecF ℓ))` is just the set of morphisms `Spec 𝔽_ℓ ⟶ X`;
* a ring map `κ(x) →+* 𝔽_ℓ` is automatically `𝔽_ℓ`-linear, exists exactly
  when `[κ(x) : 𝔽_ℓ] = 1`, and is then unique — so mathlib's
  `Scheme.SpecToEquivOfField` collapses from a `Σ`-type to a subtype.

Nothing here is `Γ₁`-specific; it is stated in this file only because
`X0.lean` has several concurrent owners. -/

/-- **The `𝔽_ℓ`-algebra structure on the residue field of a point of an
`𝔽_ℓ`-scheme**, the exact analogue of `X0.lean`'s `residueQAlgebra` with `ℚ`
replaced by `ZMod ℓ`, and defined the same way — through `Spec.preimage`, so
that `Spec.map_preimage` discharges the compatibility square by
construction. -/
@[reducible] noncomputable def residueFAlgebra {ℓ : ℕ} {X : Scheme.{0}} (strX : X ⟶ SpecF ℓ)
    (x : X) : Algebra (ZMod ℓ) (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ strX)).hom.toAlgebra

/-- **The residue degree of a point of an `𝔽_ℓ`-scheme over `𝔽_ℓ`**, the
analogue of `X0.lean`'s `residueQDegree`.  `residueFDegree strX x = 1` says
`κ(x) = 𝔽_ℓ`, i.e. that `x` is an `𝔽_ℓ`-rational point. -/
noncomputable def residueFDegree {ℓ : ℕ} {X : Scheme.{0}} (strX : X ⟶ SpecF ℓ) (x : X) : ℕ :=
  letI := residueFAlgebra strX x
  Module.finrank (ZMod ℓ) (X.residueField x)

/-- **Every endomorphism of `Spec 𝔽_ℓ` is the identity** (PROVEN).

`Spec` is fully faithful, and `ZMod ℓ` is generated by `1` as a ring, so
`Subsingleton (ZMod ℓ →+* ZMod ℓ)` (`RingHom.ext_zmod`).  This is what makes
the `RelPoint` side condition vacuous over a prime field. -/
theorem specF_hom_eq_id {ℓ : ℕ} (f : SpecF ℓ ⟶ SpecF ℓ) : f = 𝟙 (SpecF ℓ) := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage (𝟙 (SpecF ℓ))]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_zmod _ _)

/-- **A ring map `κ(x) →+* 𝔽_ℓ` is a section of the structure map** (PROVEN).

`f ∘ algebraMap = id` by `RingHom.ext_zmod`, and `f` is injective because
`κ(x)` is a field; so `algebraMap (f y) = y` for every `y`.  This one identity
carries both of the next two lemmas. -/
theorem algebraMap_residueF {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) (x : X) :
    letI := residueFAlgebra strX x
    ∀ (f : X.residueField x →+* ZMod ℓ) (y : X.residueField x),
      algebraMap (ZMod ℓ) (X.residueField x) (f y) = y := by
  letI := residueFAlgebra strX x
  intro f y
  have hcomp : f.comp (algebraMap (ZMod ℓ) (X.residueField x)) = RingHom.id (ZMod ℓ) :=
    RingHom.ext_zmod _ _
  have hfinj : Function.Injective f := f.injective
  apply hfinj
  have := congrArg (fun r => r (f y)) hcomp
  simpa using this

/-- **There is at most one ring map `κ(x) →+* 𝔽_ℓ`** (PROVEN).

By `algebraMap_residueF` the structure map is a two-sided inverse of any such
`f`, so any two of them agree.  (The statement is in fact true for any field
`κ(x)` whatever, since a ring map into `𝔽_ℓ` forces `κ(x) ≅ 𝔽_ℓ`; the
`𝔽_ℓ`-algebra structure is used only to keep the proof short.) -/
theorem residueF_hom_subsingleton {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) (x : X) :
    Subsingleton (X.residueField x →+* ZMod ℓ) := by
  letI := residueFAlgebra strX x
  refine ⟨fun f g => ?_⟩
  have hcompg : g.comp (algebraMap (ZMod ℓ) (X.residueField x)) = RingHom.id (ZMod ℓ) :=
    RingHom.ext_zmod _ _
  ext y
  have h1 := algebraMap_residueF strX x f y
  have h2 := congrArg (fun r => r (f y)) hcompg
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] at h2
  rw [← h1, h2, h1]

/-- **A ring map `κ(x) →+* 𝔽_ℓ` exists exactly when `x` has residue degree
one** (PROVEN).

Forwards, `algebraMap_residueF` makes the structure map surjective, hence
bijective, and `Module.finrank_of_bijective_algebraMap` gives the degree.
Backwards, `Algebra.finrank_eq_one_iff_bijective_algebraMap` inverts it. -/
theorem nonempty_residueF_hom_iff {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) (x : X) :
    Nonempty (X.residueField x →+* ZMod ℓ) ↔ residueFDegree strX x = 1 := by
  letI := residueFAlgebra strX x
  constructor
  · rintro ⟨f⟩
    have hbij : Function.Bijective (algebraMap (ZMod ℓ) (X.residueField x)) := by
      refine ⟨(algebraMap (ZMod ℓ) (X.residueField x)).injective, fun y => ⟨f y, ?_⟩⟩
      exact algebraMap_residueF strX x f y
    exact Module.finrank_of_bijective_algebraMap hbij
  · intro hd
    have hbij : Function.Bijective (algebraMap (ZMod ℓ) (X.residueField x)) :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd
    exact ⟨(RingEquiv.ofBijective _ hbij).symm.toRingHom⟩

/-- **`X(𝔽_ℓ)` is the set of points of `X` of residue degree one** (PROVEN).

`Equiv.subtypeUnivEquiv` over `specF_hom_eq_id` drops the `RelPoint` side
condition; mathlib's `Scheme.SpecToEquivOfField` turns `Spec 𝔽_ℓ ⟶ X` into a
pair `(x, κ(x) ⟶ 𝔽_ℓ)`; and the two lemmas above collapse the second
component, since it is unique when it exists and exists exactly at residue
degree one.

This is the dictionary that lets `card_cusp_x1_finiteField` be stated about
the finite SET `X ∖ Y` rather than about sections of `strX`. -/
noncomputable def relPointEquivResidueDegreeOne {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) :
    RelPoint strX (𝟙 (SpecF ℓ)) ≃ {x : X // residueFDegree strX x = 1} :=
  (Equiv.subtypeUnivEquiv (fun σ : SpecF ℓ ⟶ X => specF_hom_eq_id (σ ≫ strX))).trans
    (((Scheme.SpecToEquivOfField (ZMod ℓ) X).trans
      { toFun := fun p => ⟨p.1, (nonempty_residueF_hom_iff strX p.1).mp ⟨p.2.hom⟩⟩
        invFun := fun q => ⟨q.1, CommRingCat.ofHom
          ((nonempty_residueF_hom_iff strX q.1).mpr q.2).some⟩
        left_inv := by
          rintro ⟨x, f⟩
          haveI := residueF_hom_subsingleton strX x
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact CommRingCat.hom_ext (Subsingleton.elim _ _)
        right_inv := fun q => rfl }))

/-- **A rational point is a cusp exactly when its support misses `Y`**
(PROVEN).

The `←` direction is immediate: a point coming from `Y` has its support in
the image of `jY`.  The `→` direction is where `isOpen` is used —
`Spec 𝔽_ℓ` is a ONE-POINT space, so a section whose support lies in the open
`Y` has its whole range there, and `IsOpenImmersion.lift` factors it through
`jY`; the resulting `y` is a `RelPoint` of `strY` because `jY ≫ strX = strY`.

This is exactly the step `card_relPoint_x1_finiteField`'s docstring says the
`Γ₀` side would need and the `Γ₁` side escapes — it escapes it in the
ASSEMBLY, because `IsCusp` is negative there; it is needed here, where the
cusps are being counted rather than shown to be everything. -/
theorem isCusp_iff_notMem_range {N ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X Y : Scheme.{0}}
    {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY)
    (x : RelPoint strX (𝟙 (SpecF ℓ))) (p : SpecF ℓ) :
    h.IsCusp x ↔ x.1.base p ∉ Set.range jY.base := by
  haveI := h.isOpen
  haveI : Subsingleton (SpecF ℓ) := inferInstanceAs (Subsingleton (PrimeSpectrum (ZMod ℓ)))
  constructor
  · intro hc hmem
    refine hc ⟨⟨IsOpenImmersion.lift jY x.1 ?_, ?_⟩, ?_⟩
    · rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z p]
      exact hmem
    · rw [← h.comm, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact x.2
    · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  · rintro hn ⟨y, hy⟩
    refine hn ?_
    have hx : x.1 = y.1 ≫ jY := (congrArg Subtype.val hy).symm
    rw [hx]
    exact ⟨y.1.base p, rfl⟩

/-- **The point underlying an `𝔽_ℓ`-rational point is its image point**
(PROVEN, and definitionally so).

`Scheme.SpecToEquivOfField` records the image of `IsLocalRing.closedPoint`;
`Spec 𝔽_ℓ` has only one point, so any `p` will do. -/
theorem relPointEquivResidueDegreeOne_val {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) (x : RelPoint strX (𝟙 (SpecF ℓ))) (p : SpecF ℓ) :
    ((relPointEquivResidueDegreeOne strX x : {x : X // residueFDegree strX x = 1}) : X)
      = x.1.base p := by
  haveI : Subsingleton (SpecF ℓ) := inferInstanceAs (Subsingleton (PrimeSpectrum (ZMod ℓ)))
  show x.1.base _ = x.1.base p
  rw [Subsingleton.elim (IsLocalRing.closedPoint (ZMod ℓ)) p]

/-- **The cusps of `X_1(N)` over `𝔽_ℓ` are the residue-degree-one points of
the cusp locus `X ∖ Y`** (PROVEN; axiom-audited
`[propext, Classical.choice, Quot.sound]`).

The sorry-free half of `card_cusp_x1_finiteField`, and the `𝔽_ℓ` mirror of
`nonempty_cuspLocusX1_of_rationalCuspPoints`: it converts a statement about
SECTIONS of `strX` satisfying a negative predicate into a statement about the
finite set of POINTS `X ∖ Y` and their residue degrees, which is the form
Deligne–Rapoport prove and the form in which `ord_25(3) = 20` can actually be
used.  `relPointEquivResidueDegreeOne` supplies the points, and
`isCusp_iff_notMem_range` the cuspidality. -/
noncomputable def cuspEquivResidueDegreeOne {N ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X Y : Scheme.{0}}
    {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    {x : RelPoint strX (𝟙 (SpecF ℓ)) // h.IsCusp x} ≃
      {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} :=
  haveI : Nonempty (SpecF ℓ) := inferInstanceAs (Nonempty (PrimeSpectrum (ZMod ℓ)))
  let p : SpecF ℓ := Classical.arbitrary _
  (Equiv.subtypeEquiv (relPointEquivResidueDegreeOne strX)
      (q := fun b : {x : X // residueFDegree strX x = 1} => (b : X) ∉ Set.range jY.base)
      (fun x => by
        rw [isCusp_iff_notMem_range h x p, relPointEquivResidueDegreeOne_val strX x p])).trans
    { toFun := fun q => (⟨⟨q.1.1, q.2⟩, q.1.2⟩ :
        {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1})
      invFun := fun c => (⟨⟨c.1.1, c.2⟩, c.1.2⟩ :
        {q : {x : X // residueFDegree strX x = 1} // (q : X) ∉ Set.range jY.base})
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- **`residueDegreeOver (ZMod ℓ)` IS `residueFDegree`** (PROVEN,
definitionally).

The `𝔽_ℓ` half of the bridge whose `ℚ` half is
`residueDegreeOver_eq_residueQDegree`; see the subsection there for why the
base field of the cusp leaf is free, and for the instance diamond this
`rfl` is the compiler's confirmation about. -/
theorem residueDegreeOver_eq_residueFDegree {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {X : Scheme.{0}}
    (strX : X ⟶ SpecF ℓ) (x : X) :
    residueDegreeOver (ZMod ℓ) strX x = residueFDegree strX x := rfl

/-- **The `𝔽_ℓ`-rational points of the cusp locus of `X_1(N)_{𝔽_ℓ}` inject
into the Frobenius-fixed cusp symbols** (sorry leaf — the hard direction of
Ogg's description of the cusps, and after the 2026-07-28 decomposition ALL
that is left of `card_cuspLocusPoints_x1_finiteField`).

TRUE and classical (Ogg 1973; Deligne–Rapoport VI.5; Diamond–Shurman §3.8
for the cusp set and §9.3 for the Galois action).  The content is one
identification and one dictionary:

* `X ∖ Y` with its `Gal(𝔽̄_ℓ/𝔽_ℓ)`-action is the cusp locus of the
  Deligne–Rapoport model of `X_1(N)` over `ℤ[1/N]`, base-changed to `𝔽_ℓ`;
  its geometric points are `Γ_1(N)∖ℙ¹(ℚ)`, i.e. `CuspSymbolX1 N`, and the
  Galois action is through the cyclotomic character, i.e. `cuspFrobX1 N ℓ`
  (see `CuspSymbolX1.lean`'s module docstring for why the character moves
  the coordinate defined mod `gcd(c, N)` and not the other one).
* a CLOSED point of an `𝔽_ℓ`-scheme has residue degree `1` exactly when the
  single geometric point above it is Frobenius-fixed, so
  `residueFDegree strX c = 1` picks out the fixed symbols.

Both directions of the second bullet are true, so the honest statement is a
BIJECTION; only the injection is asked for, because only the upper bound is
consumed and the lower bound is already `exists_rationalCuspPointsX1_field`
at `K = 𝔽_ℓ`.  A prover who has the bijection has this for free.

**What each hypothesis is doing.**  `hℓN : ¬ ℓ ∣ N` is what makes the
`Γ₁(N)`-problem étale at `ℓ` and the cusp locus finite étale — at `ℓ ∣ N`
the reduction is not the Deligne–Rapoport one and no such description is
claimed.  `hN : 5 ≤ N` is the standing hypothesis of the `Γ_1(N)∖ℙ¹(ℚ)`
count: at `N ≤ 4` the `±` identification is not free (`-I ∈ Γ_1(N)` acts
with fixed points on the symbols) and `#cusps ≠ ½ Σ_{d ∣ N} φ(d)φ(N/d)`.
Both are discharged for free at the single witness row, `(25, 3, 10)`.

**No arithmetic is asked for here** — this is the whole point of the cut.
The leaf says nothing about `ord_25(3)`, about `φ(25)/2 = 10`, or about how
many symbols are fixed; that is `card_fixedCuspSymbolX1`, PROVEN.  In
particular the leaf is stated uniformly in `(N, ℓ)` and is TRUE uniformly,
whereas the bound it feeds is false for `ℓ ≡ ±1 (mod N)` — the arithmetic
hypothesis lives entirely on the other factor.

AXES SEARCHED.  The BIJECTION-vs-INJECTION axis is TAKEN (weakened to the
half that is consumed).  The BASE-FIELD axis is NOT available: the statement
is about Frobenius, so it is specific to a finite base field; the `ℚ`-side
analogue is `exists_rationalCuspPointsX1_field`, already separate.  The
SYMBOL-SET axis — replacing `CuspSymbolX1` by the moduli description (Néron
`d`-gons with a point of order `N`) — is available and would be a
REFORMULATION, not a reduction: the two index sets are isomorphic and the
Galois actions correspond, so nothing is bought. -/
theorem exists_cuspSymbolEmbedding_x1_finiteField (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hN : 5 ≤ N)
    (_hℓN : ¬ ℓ ∣ N)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (_h : IsX1Compactification N strX strY jY) :
    ∃ f : {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} →
        CuspSymbolX1 N,
      Function.Injective f ∧
      ∀ x, IsPrimitiveCuspSymbolX1 N (f x) ∧
        cuspFrobX1 N ((ℓ : ℕ) : ZMod N) (f x) = f x :=
  sorry

/-- **AT MOST `m` points of the cusp locus of `X_1(N)_{𝔽_ℓ}` have residue
degree one, at the witness rows** (PROVEN 2026-07-28 over
`exists_cuspSymbolEmbedding_x1_finiteField` and `card_fixedCuspSymbolX1`; a
sorry leaf until then — the ONE genuinely modular half of the `(25, 3, 10)`
row, and all that is left of `card_cusp_x1_finiteField`).

**Restated 2026-07-28 from `=` to `≤`, and the `≥` half is now CLOSED.**
That half is `exists_rationalCuspPointsX1_field` at `K = 𝔽_ℓ`: the `ℚ`-side
cusp leaf with its base field freed, applicable here because
`x1WitnessTable_spec` carries `¬ ℓ ∣ N`, and sufficient because
`numRationalCuspsX1 25 = 10 = m` at the single row.  So what remains is
exactly the HARD direction of Ogg's description — no cusp OUTSIDE the
distinguished `φ(N)/2`-orbit is `𝔽_ℓ`-rational — and the easy direction is
now shared with the `ℚ` side rather than proved twice on two open leaves.

TRUE.  At `(25, 3, 10)`: `ord_25(3) = 20`, so `𝔽_3(ζ₂₅) = 𝔽_{3^20}`; the
`10` cusps of the rational orbit stay rational on the special fibre,
while the `10` cusps defined over `ℚ(ζ₂₅)⁺` (degree `10`) reduce into
`𝔽_{3^10}` and the remaining `8` into `𝔽_{3^4}`, so none of the other
`18` is `𝔽_3`-rational.

**Note this half needs the count EXACTLY**, unlike `exists_rationalCuspsX1`
over `ℚ` where a lower bound suffices — the level-`25` argument compares
`#X_1(25)(𝔽_3)` against the `10` rational cusps of `X_1(25)/ℚ` and needs
them to be the SAME number.  So the hard direction of Ogg's description
IS an obligation here, and only here.

Quantified over every compactification rather than over a chosen one:
`IsX1Compactification` pins `(X, Y, jY)` up to isomorphism and the cusp
locus is an isomorphism invariant, so the count does not depend on
which model is supplied; non-vacuity is supplied by
`exists_x1Compactification_finiteField`.

**Stated about POINTS of `X ∖ Y`, not about sections of `strX`** (2026-07-27;
this is the whole change at this node).  `cuspEquivResidueDegreeOne` is the
dictionary, and it is sorry-free, so nothing is lost; what is gained is that
the statement is now literally the Deligne–Rapoport one — `X ∖ Y` is the
finite set of cusps of the special fibre, `residueFDegree strX c = 1` says the
cusp `c` is `𝔽_ℓ`-rational, and the content is the residue-field computation
`𝔽_3(ζ₂₅) = 𝔽_{3^20}` above.  A prover no longer has to manufacture sections
or reason about the negative predicate `IsCusp`.

`h` is carried but unused: `finite_compl` would give finiteness of the index
type, and a prover will want it, but the statement is meaningful without it
and the leaf is quantified over every model regardless.

**Where the level-`25` weight really sits.**  This leaf and
`exists_rationalCuspPointsX1_field` are both Deligne–Rapoport cusp theory
(VI.5) — since 2026-07-28 the latter covers BOTH bases and this one only the
upper bound; neither is Eichler–Shimura.  `X_1(25)` has genus `12`, so the
Eichler–Shimura count `ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_1(25)))` looks forbidding,
but the answer `10` is exactly `φ(25)/2 = numRationalCuspsX1 25`, so no
Hecke operator is needed anywhere on this route.  Contrast
`X0.lean`'s `card_relPoint_x0_finiteField`, whose counts genuinely ARE
Eichler–Shimura and which is blocked on a module cycle through
`Modularity/Interface.lean`; this leaf inherits none of that.

AXES SEARCHED.  The SECTION-vs-POINT axis is TAKEN (above).  The
INEQUALITY axis is TAKEN (2026-07-28): splitting `=` into `≥` and `≤` is what
freed the base field on the `≥` half.  **The BASE-FIELD axis is available on
`≥` and NOT on `≤`**, and the previous version of this paragraph — "the
BASE-FIELD axis is NOT available: this leaf needs the count EXACTLY, so it
cannot be merged with the `ℚ`-side leaf, which is a lower bound" — was
correct about the leaf as it then stood and wrong as a verdict about the
NODE, which is the mis-pricing this file's doctrine warns about: a lower
bound and an exact count differ by an upper bound, so the merge was blocked
only on the half that is still here.

**The WITNESS-TABLE axis is REFUTED — and refuted more sharply than the
previous version of this paragraph said** (2026-07-28).  It read
"generalising to all `(N, ℓ)` would demand the full `Γ₁` cusp classification
and its reduction behaviour, which is strictly more than the route needs",
i.e. it priced the general statement as TRUE but expensive.  It is not true.
For any prime `ℓ ≡ ±1 (mod N)` the Frobenius acts on the cusps through a
central element and the bound `≤ φ(N)/2` FAILS: at `N = 25` exhaustive
enumeration over `(ℤ/25)²` gives `28` rational cusps at `ℓ ≡ 1` and `20` at
`ℓ ≡ -1`, against `φ(25)/2 = 10`.  So the row is not carrying a cost, it is
carrying the ARITHMETIC HYPOTHESIS `IsUnit (ℓ - 1) ∧ IsUnit (ℓ + 1)` in
`ZMod N` — which `card_fixedCuspSymbolX1` now states explicitly, and which
`(25, 3)` satisfies because `2` and `4` are units mod `25`.

**DECOMPOSED 2026-07-28, into geometry and arithmetic.**  What is proven
below is `le_antisymm`-free: the `𝔽_ℓ`-rational cusp points inject into the
`σ_ℓ`-fixed primitive cusp symbols (`exists_cuspSymbolEmbedding_x1_finiteField`,
the remaining leaf), and those number exactly `φ(N)/2`
(`card_fixedCuspSymbolX1` in `ModularCurve/CuspSymbolX1.lean`, PROVEN).  The
level-`25` arithmetic quoted above — `ord_25(3) = 20` and `ord_5(3) = 4`,
hence residue degrees `10` and `4` on the other `18` cusps — is no longer an
obligation of the remaining leaf; it was verified as the orbit-size multiset
`{1 × 10, 4 × 2, 10 × 1}` of `cuspFrobX1 25 3` on the `28` symbols, and the
whole of it is subsumed by the two unit hypotheses. -/
theorem card_cuspLocusPoints_x1_finiteField_le (N ℓ m : ℕ)
    (htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Nat.card {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} ≤ m := by
  obtain ⟨-, hℓ, hℓN, -⟩ := x1WitnessTable_spec htable
  have hN : 5 ≤ N := by fin_cases htable; norm_num
  haveI : NeZero N := ⟨by omega⟩
  have ht1 : IsUnit (((ℓ : ℕ) : ZMod N) - 1) := by
    fin_cases htable; exact IsUnit.of_mul_eq_one 13 (by decide)
  have ht2 : IsUnit (((ℓ : ℕ) : ZMod N) + 1) := by
    fin_cases htable; exact IsUnit.of_mul_eq_one 19 (by decide)
  have hm : N.totient / 2 = m := by fin_cases htable; exact numRationalCuspsX1_twentyFive
  obtain ⟨f, hinj, hfix⟩ := exists_cuspSymbolEmbedding_x1_finiteField N ℓ hℓ hN hℓN h
  have hcard : Nat.card {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1}
      ≤ Nat.card (FixedCuspSymbolX1 N ((ℓ : ℕ) : ZMod N)) :=
    Nat.card_le_card_of_injective
      (fun x : {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} =>
        (⟨f x, hfix x⟩ : FixedCuspSymbolX1 N ((ℓ : ℕ) : ZMod N)))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  rwa [card_fixedCuspSymbolX1 N (by omega) _ ht1 ht2, hm] at hcard

/-- **The cusp locus of `X_1(N)_{𝔽_ℓ}` has exactly `m` points of residue
degree one, at the witness rows** (PROVEN 2026-07-28 over
`card_cuspLocusPoints_x1_finiteField_le` and
`exists_rationalCuspPointsX1_field`; a single sorry leaf until then).

`le_antisymm` of the two halves.  The `≥` half is the whole content of the
change and is worth spelling out, because it is where the `ℚ` and `𝔽_ℓ`
sides of this cluster stopped being two theorems:

* `x1WitnessTable_spec` gives `ℓ.Prime` and `¬ ℓ ∣ N`, so `(N : ZMod ℓ)` is a
  unit (`ZMod.natCast_eq_zero_iff` in a field) and
  `exists_rationalCuspPointsX1_field` applies at `K = ZMod ℓ`, supplying an
  injection `Fin (numRationalCuspsX1 N) ↪ {c ∈ X ∖ Y | residueFDegree = 1}`;
* `numRationalCuspsX1 N = m` at every row of the table — at the one row this
  is `numRationalCuspsX1 25 = 10`, i.e. `φ(25)/2 = 10`, which is exactly the
  numerical coincidence `exists_x1Compactification_mod_prime`'s docstring
  identifies as the whole reason the `(25, 3, 10)` row is not an
  Eichler–Shimura computation;
* `h.finite_compl` makes the target finite, so `Nat.card_le_card_of_injective`
  turns the injection into `m ≤ Nat.card`.

`_htable` is consumed twice — once for the side conditions and once for
`numRationalCuspsX1 N = m` — so the row is doing arithmetic here rather than
being carried for shape. -/
theorem card_cuspLocusPoints_x1_finiteField (N ℓ m : ℕ)
    (htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Nat.card {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} = m := by
  obtain ⟨-, hℓ, hℓN, -⟩ := x1WitnessTable_spec htable
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  have hm : numRationalCuspsX1 N = m := by
    fin_cases htable
    exact numRationalCuspsX1_twentyFive
  have hunit : IsUnit ((N : ℕ) : ZMod ℓ) :=
    isUnit_iff_ne_zero.mpr fun hz => hℓN ((ZMod.natCast_eq_zero_iff N ℓ).mp hz)
  obtain ⟨ε, hinj, hdeg⟩ := exists_rationalCuspPointsX1_field N (ZMod ℓ) hunit h
  haveI : Finite ((Set.range jY.base)ᶜ : Set X) := h.finite_compl.to_subtype
  have hge : m ≤ Nat.card {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} := by
    have hcard := Nat.card_le_card_of_injective
      (fun i : Fin (numRationalCuspsX1 N) =>
        (⟨ε i, hdeg i⟩ : {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1}))
      (fun a b hab => hinj (congrArg Subtype.val hab))
    simpa [hm] using hcard
  exact le_antisymm (card_cuspLocusPoints_x1_finiteField_le N ℓ m htable h) hge

/-- **The cusps of `X_1(N)` over `𝔽_ℓ` number exactly `m`, at the witness
rows** (PROVEN 2026-07-27 over `card_cuspLocusPoints_x1_finiteField`; formerly
a sorry leaf).

`cuspEquivResidueDegreeOne` identifies the cusp subtype of `X(𝔽_ℓ)` with the
residue-degree-one points of `X ∖ Y`, and the count of the latter is the leaf.
`ℓ.Prime` comes from `x1WitnessTable_spec`, and is what makes `ZMod ℓ` a field
— it is needed for the dictionary, not for the arithmetic. -/
theorem card_cusp_x1_finiteField (N ℓ m : ℕ) (htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Nat.card {x : RelPoint strX (𝟙 (SpecF ℓ)) // h.IsCusp x} = m := by
  obtain ⟨-, hℓ, -, -⟩ := x1WitnessTable_spec htable
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  rw [Nat.card_congr (cuspEquivResidueDegreeOne h)]
  exact card_cuspLocusPoints_x1_finiteField N ℓ m htable h

/-- **`#X_1(N)(𝔽_ℓ) = m` at the witness rows** (PROVEN 2026-07-27, by
decomposition).

The assembly of the two halves the `(25, 3, 10)` docstring names.  It is
short for a reason worth recording: once `Y_1(N)(𝔽_ℓ)` is EMPTY, the
predicate `h.IsCusp` — which is `¬ ∃ y : RelPoint strY (𝟙 _), …` — holds
of EVERY rational point of `X`, so the cusp subtype is all of
`RelPoint strX (𝟙 (SpecF ℓ))` and the split `X(𝔽_ℓ) = Y(𝔽_ℓ) ⊔ cusps`
needs no scheme theory at all.  That is why `Equiv.subtypeUnivEquiv`
suffices where the `Γ₀` side would need `IsOpenImmersion.lift`. -/
theorem card_relPoint_x1_finiteField (N ℓ m : ℕ) (htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m := by
  obtain ⟨hN4, hℓ, hℓN, hNℓ⟩ := x1WitnessTable_spec htable
  have hempty : IsEmpty (RelPoint strY (𝟙 (SpecF ℓ))) :=
    isEmpty_relPoint_y1_finiteField N ℓ hN4 hℓ hℓN hNℓ h
  have hall : ∀ x : RelPoint strX (𝟙 (SpecF ℓ)), h.IsCusp x := fun _ hx =>
    hempty.elim hx.choose
  rw [← Nat.card_congr (Equiv.subtypeUnivEquiv hall)]
  exact card_cusp_x1_finiteField N ℓ m htable h

/-- **The reduction `X_1(N)_{𝔽_ℓ}` and its point count, at the witness
primes** (PROVEN 2026-07-27, by decomposition; formerly a sorry node).

TRUE: for `ℓ ∤ N` the modular curve has good reduction at `ℓ` and its
special fibre is the coarse space of the same `Γ₁(N)`-problem over
`𝔽_ℓ`; being proper over a finite field it has finitely many rational
points.

**THE `(25, 3, 10)` ROW IS NOT AN EICHLER–SHIMURA COMPUTATION**, and this
is the finding that reshapes the level-`25` budget.  `X_1(25)` has genus
`12`, so the Eichler–Shimura count `ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_1(25)))` looks
forbidding; but the answer `10` is exactly `φ(25)/2`, the number of cusps
over `∞`, so the whole content is:

1. **`X_1(25)` has no non-cuspidal `𝔽_3`-point.**  Such a point is a pair
   `(E, P)` over `𝔽_3` with `P` of exact order `25`, so `25 ∣ #E(𝔽_3)`.
   Hasse gives `#E(𝔽_3) ≤ 3 + 1 + 2√3 < 8`, and in fact the crude
   Weierstrass bound `#E(𝔽_q) ≤ 2q + 1 = 7` already suffices — at most
   two `y` for each of the `3` values of `x`, plus the point at infinity.
   So no Hasse, no Eichler–Shimura, no Hecke operators.  (The one real
   step is that an `𝔽_3`-point of the COARSE space comes from a datum
   over `𝔽_3`; over a finite field that is Lang's theorem, and at
   `N = 25 ≥ 4` the space is fine anyway, so it is immediate.)
   Corroborated numerically: `G₂₅ mod 3` vanishes on `𝔽_3 × 𝔽_3` only at
   `(0, 0)`, which has `b = 0`.
2. **`X_1(25)_{𝔽_3}` has exactly `10` rational points, all cusps.**  This
   is the genuinely modular half, and note it needs the count EXACTLY,
   unlike `exists_rationalCuspsX1` over `ℚ` where a lower bound suffices:
   `ord_25(3) = 20`, so `𝔽_3(ζ₂₅) = 𝔽_{3^20}`, the `∞`-cusps stay
   rational and the `0`-cusps (over `ℚ(ζ₂₅)⁺`, degree `10`) reduce into
   `𝔽_{3^10}` and are not rational.

**CORRECTION 2026-07-27 to the paragraph this docstring used to end
with**, which said the two halves "are not stated separately because half
1 alone is not consumed by anything … and because the join needs
`X'(𝔽_3) = Y'(𝔽_3) ⊔ cusps`, which is a fact about this structure rather
than about either half".  Both reasons are wrong, and the halves are now
stated separately and consumed:

* half 1 IS consumed — by `card_relPoint_x1_finiteField`, through
  `isEmpty_relPoint_y1_finiteField`, so it is not free-floating;
* the join needs no `⊔` at all.  `IsCusp` is a NEGATIVE condition, so
  once `Y'(𝔽_3)` is empty every point of `X'` is a cusp and the
  disjoint-union bookkeeping collapses to `Equiv.subtypeUnivEquiv`.

**The three sentences of the paragraph above are three different
theories, and they are now four leaves rather than one**, of which only
one still carries modular content:

* `exists_x1Compactification_finiteField` — the `Γ₁(N)`-problem has a
  smooth compactification over `𝔽_ℓ` (Deligne–Rapoport).  PROVEN as a
  corollary of `exists_x1Compactification_field`, so this half is now
  SHARED with the `ℚ` case and both rest on the single leaf
  `exists_isCoarseModuliY1_isSmoothCurve`;
* `finite_relPoint_of_x1Compactification_finiteField` — a proper scheme
  over a finite field has finitely many rational points.  PROVEN, over
  `X0.lean`'s `finite_relPoint_of_isProper`, with no modular content
  whatsoever;
* `exists_gamma1Datum_of_relPoint` (fineness/Lang) and
  `isEmpty_gamma1Datum_finiteField` (the crude bound `#E(𝔽_ℓ) ≤ 2ℓ + 1`)
  — half 1, two OPEN leaves, neither of which mentions a modular curve.
  Its arithmetic half `natCard_weierstrassPoint_le` is proved outright,
  and what is left under it is `exists_gamma1Datum_of_relPoint` together
  with the single geometric leaf
  `exists_weierstrassEquiv_of_gamma1Datum` (a Weierstrass presentation of
  an abelian scheme of relative dimension one; 2026-07-28 —
  `exists_weierstrassPointOfOrder_of_gamma1Datum` is PROVEN over it and
  `addOrderOf_relPointOfSection_gamma1Datum`);
* `exists_cuspSymbolEmbedding_x1_finiteField` — half 2, the cusp count on the
  special fibre, and the only one of the four that is Deligne-Rapoport at
  this base.  The whole chain above it is now PROVEN:
  `card_cusp_x1_finiteField` through `cuspEquivResidueDegreeOne` and
  `card_cuspLocusPoints_x1_finiteField`, which is `le_antisymm` of
  `exists_rationalCuspPointsX1_field` at `K = 𝔽_ℓ` and
  `card_cuspLocusPoints_x1_finiteField_le`, which is in turn PROVEN
  (2026-07-28) over this leaf and the arithmetic `card_fixedCuspSymbolX1`.
  What is STILL OPEN is therefore only the identification of `X ∖ Y` with
  `Γ_1(N)∖ℙ¹(ℚ)` as a Galois set — no counting, no level, no prime.

Note that no integral model appears in any of them: the special fibre is
obtained as the coarse space of the problem over `𝔽_ℓ` directly, so the
reduction map — which is what would need the model — is never formed.
The previous verdict "IRREDUCIBLE at this pin only through half 2:
neither the integral model of `X_1(N)` nor its reduction exists here" was
therefore wrong twice over: no model is needed, and the leaf splits. -/
theorem exists_x1Compactification_mod_prime (N ℓ m : ℕ)
    (h : (N, ℓ, m) ∈ x1WitnessTable) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) ∧
        Finite (RelPoint strX (𝟙 (SpecF ℓ))) ∧
        Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m := by
  obtain ⟨hN, hℓ, hℓN, -⟩ := x1WitnessTable_spec h
  obtain ⟨X, Y, strX, strY, jY, ⟨hX⟩⟩ :=
    exists_x1Compactification_finiteField N ℓ hN hℓ hℓN
  exact ⟨X, Y, strX, strY, jY, ⟨hX⟩,
    finite_relPoint_of_x1Compactification_finiteField N ℓ hℓ.ne_zero hX,
    card_relPoint_x1_finiteField N ℓ m h hX⟩

/-! ### Uniqueness of `X_1(N)` over `𝔽_ℓ`, and the reduction datum

The two subsections here are what turns the rank-`0` criterion below from
a single `sorry` into an assembly.  They mirror, declaration for
declaration, the chain that PROVES `card_le_of_rankZeroJacobian` in
`X0.lean`:

| `X0.lean` | here |
|---|---|
| `IsCoarseModuliY0.exists_inverse` (PROVEN) | `IsCoarseModuliY1.exists_inverse` (PROVEN) |
| `exists_inverse_of_isX0Compactification` (PROVEN) | `exists_inverse_of_smoothCompactification` (PROVEN 2026-07-27, and it SUBSUMES the `Γ₀` one — both now cite `AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve`) |
| `nonempty_relPointEquiv_of_isX0Compactification` (PROVEN) | `nonempty_relPointEquiv_of_isX1Compactification` (PROVEN) |
| `exists_x0NeronDatum` + `exists_isX0Compactification_specialFibre` + `neronReduction_injective` | `exists_x1ReductionAt` (PROVEN 2026-07-28 over the single leaf `exists_x1CurveModel_of_base` and the moduli-free `NeronReduction.lean`) |

`IsX0ReductionAt`, `IsJacobianOf` and `HasRankZeroJacobian` are REUSED
verbatim from `X0.lean`: none of the three mentions a moduli problem —
they speak only about a curve, its Jacobian and Abel–Jacobi — so there is
no `Γ₁` analogue of any of them to write, and the `Γ₀` naming of
`IsX0ReductionAt` is an accident of where it was first needed.
-/

/-- **Any two coarse moduli spaces for the `Γ₁(N)`-problem over a common
base are isomorphic over it** (PROVEN).

Pure initiality, no geometry, and verbatim the proof of
`IsCoarseModuliY0.exists_inverse`: `h₁.universal` applied to
`(Y₂, h₂.classify)` gives `u : Y₁ ⟶ Y₂` over the base, `h₂.universal`
applied to `(Y₁, h₁.classify)` gives `v`, and both `u ≫ v` and `𝟙 Y₁`
satisfy the property that `h₁.universal` at `(Y₁, h₁.classify)` says
EXACTLY ONE morphism satisfies.

This is what `IsCoarseModuliY1`'s own docstring means by "initiality
alone determines `(Y, classify)` up to unique isomorphism".  Stated with
a raw inverse pair rather than as an `Iso`, matching
`relPointEquivOfInverse`, which is the only consumer. -/
theorem IsCoarseModuliY1.exists_inverse {N : ℕ} {Y₁ Y₂ S : Scheme.{u}}
    {str₁ : Y₁ ⟶ S} {str₂ : Y₂ ⟶ S}
    (h₁ : IsCoarseModuliY1 N str₁) (h₂ : IsCoarseModuliY1 N str₂) :
    ∃ (u : Y₁ ⟶ Y₂) (v : Y₂ ⟶ Y₁),
      u ≫ str₂ = str₁ ∧ v ≫ str₁ = str₂ ∧ u ≫ v = 𝟙 Y₁ ∧ v ≫ u = 𝟙 Y₂ := by
  obtain ⟨u, ⟨hu, hucl⟩, -⟩ := h₁.universal str₂ h₂.classify h₂.classify_natural
  obtain ⟨v, ⟨hv, hvcl⟩, -⟩ := h₂.universal str₁ h₁.classify h₁.classify_natural
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · obtain ⟨w, -, hwuniq⟩ := h₁.universal str₁ h₁.classify h₁.classify_natural
    refine (hwuniq (u ≫ v) ⟨?_, ?_⟩).trans (hwuniq (𝟙 Y₁) ⟨Category.id_comp _, ?_⟩).symm
    · rw [Category.assoc, hv, hu]
    · intro T g dd
      conv_lhs => rw [hvcl g dd, hucl g dd]
      exact Category.assoc _ _ _
    · intro T g dd
      exact (Category.comp_id _).symm
  · obtain ⟨w, -, hwuniq⟩ := h₂.universal str₂ h₂.classify h₂.classify_natural
    refine (hwuniq (v ≫ u) ⟨?_, ?_⟩).trans (hwuniq (𝟙 Y₂) ⟨Category.id_comp _, ?_⟩).symm
    · rw [Category.assoc, hu, hv]
    · intro T g dd
      conv_lhs => rw [hucl g dd, hvcl g dd]
      exact Category.assoc _ _ _
    · intro T g dd
      exact (Category.comp_id _).symm

/-- **A smooth proper geometrically connected curve over `𝔽_ℓ` is
determined by a dense open** (**PROVEN 2026-07-27**, over
`AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve`;
formerly a sorry leaf).

TRUE, and classical: two smooth proper geometrically connected curves
over a field containing a common dense open glue along it.  This is what
`IsX1Compactification`'s docstring means by "`finite_compl` is what pins
`X` as the genuine `X_1(N)`".

**HOW IT IS PROVEN, AND WHY THE GRAPH CLOSURE IS NOT NEEDED.**  The
argument recorded here previously — take the closure of the graph of `u`
in `X₁ ×_k X₂` and show both projections are proper and birational — is
not the cheapest route and is not the one taken.  The whole geometric
content is already available in this tree as
`AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, PROVEN over
three sharper leaves): a morphism from a dense open of a smooth proper
curve over a field into ANY proper scheme extends UNIQUELY.  Applying it
four times finishes the statement with no geometry of its own:

* twice for EXISTENCE — extend `u ≫ jY₂ : Y₁ ⟶ X₂` to `w : X₁ ⟶ X₂` and
  `v ≫ jY₁ : Y₂ ⟶ X₁` to `w' : X₂ ⟶ X₁`, the target being proper in each
  case;
* twice for the ROUND TRIPS — `w ≫ w'` and `𝟙 X₁` are both extensions of
  `jY₁ : Y₁ ⟶ X₁` over the base (`huv` is exactly what makes the first one
  restrict to `jY₁`), so the UNIQUENESS clause of the same theorem, taken
  at the target `Z = X₁`, identifies them; symmetrically for `w' ≫ w` and
  `𝟙 X₂`.

That is the whole proof, and it is why the target of the extension
theorem is only assumed PROPER rather than assumed to be another
compactification: the identity case is what supplies uniqueness of the
round trip.  Note the density of `Y_i` in `X_i` is DERIVED there from
`smooth`, `connected` and `finite_compl` jointly, so `_hf₁`/`_hf₂` are
consumed and not decorative.

**`_hℓ` IS LOAD-BEARING AND IS NOW CONSUMED**: it is what makes `ZMod ℓ`
a field, via `Fact ℓ.Prime`, and the extension theorem is stated over
`Spec` of a field.  It is renamed `hℓ` accordingly.

**WHAT THIS CLOSES ELSEWHERE.**  The leaf still SUBSUMES `X0.lean`'s
`exists_inverse_of_isX0Compactification`, and that one is now PROVEN too,
by the same citation — so the sharing recorded below was real and both
sides have cashed it in.  Nothing in `X0.lean` is edited here.

**HOW IT CLOSED, AND WHY THE OLD VERDICT WAS WRONG.**  The route taken is
NOT the closure of the graph.  It is three applications of ONE proven
theorem — `exists_unique_extension_of_isSmoothProperCurve` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`: *a morphism
from a dense open of a smooth proper geometrically connected curve over a
field into a proper scheme extends UNIQUELY over the base*.  Extend
`u ≫ jY₂` to `w : X₁ ⟶ X₂` and `v ≫ jY₁` to `w' : X₂ ⟶ X₁`; then `w ≫ w'`
and `𝟙 X₁` both extend `jY₁`, so the SAME theorem's uniqueness clause
identifies them, and symmetrically on `X₂`.  Density of `Y` in `X` is
derived inside that theorem from `smooth`, `connected` and `finite_compl`
jointly (`isDominant_of_finite_compl`), which is why all twelve geometric
hypotheses are consumed.

The refuting grep this docstring itself prescribed — "a declaration in
`Mathlib`, `~/cs/FLT` or `Fermat/` producing an isomorphism of smooth
proper curves from an isomorphism of dense opens; as of 2026-07-27 `grep`
over all three finds none" — was **correct as literally posed and useless
as posed**.  No declaration produces the *isomorphism*; one produces the
*extension*, from which the isomorphism is a ten-line corollary.  The
lesson is the one already recorded for `exists_jacobianOf_curve` in this
file: search the INFRASTRUCTURE axis, and grep for what the proof needs
rather than for the statement you want.

**THIS LEAF IS MODULI-FREE, AND THAT IS THE POINT.**  It is stated over
the raw geometric fields — `IsOpenImmersion`, `IsProper`,
`SmoothOfRelativeDimension 1`, `GeometricallyConnected`, finiteness of
the complement — rather than over `IsX1Compactification`, because the
closure-of-the-graph argument uses none of the moduli structure.  So it
SUBSUMES `X0.lean`'s `exists_inverse_of_isX0Compactification`, which is
the same statement with the same fields hidden inside an
`IsX0Compactification` bundle whose `coarse` field its proof may not
touch: a successor proving this one has proven that one, and the two
should close together.  (Nothing in `X0.lean` is edited to say so — that
file has many concurrent owners — so the sharing is recorded here.)

**NOT VACUOUS.**  Every hypothesis is load-bearing for the conclusion,
and every one of them is now consumed by the proof:

* drop properness of `strX₁` and take `X₁ = Y₁` an affine curve, `X₂` its
  smooth compactification — then `Y₁ ≅ Y₂` but `X₁ ≇ X₂`;
* drop smoothness and `X₂` may be any singular curve with the same
  function field, e.g. a nodal model, again not isomorphic to `X₁`;
* drop finiteness of the complements and `Y` need not be dense in `X`, so
  `X₁` may carry a whole extra component that `X₂` lacks;
* drop `hu`/`hv` and the isomorphism `Y₁ ≅ Y₂` is not over the base, so
  no `w` over the base can exist;
* the conclusion's last conjunct `jY₁ ≫ w = u ≫ jY₂` is what says `w`
  EXTENDS `u` rather than being some unrelated isomorphism, and it is
  what a consumer that cares about cusps needs.

`hℓ` is carried because the argument wants a FIELD base: over a
non-normal or non-reduced base the extension theorem fails — the
valuative criterion is applied at `Spec 𝒪_{X,x}`, legitimate exactly
because that is a valuation ring, which over a one-dimensional base fails
at the closed points of the special fibre. -/
theorem exists_inverse_of_smoothCompactification {ℓ : ℕ} (hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (hc₁ : jY₁ ≫ strX₁ = strY₁) (hc₂ : jY₂ ≫ strX₂ = strY₂)
    (ho₁ : IsOpenImmersion jY₁) (ho₂ : IsOpenImmersion jY₂)
    (hp₁ : IsProper strX₁) (hp₂ : IsProper strX₂)
    (hs₁ : SmoothOfRelativeDimension 1 strX₁) (hs₂ : SmoothOfRelativeDimension 1 strX₂)
    (hg₁ : GeometricallyConnected strX₁) (hg₂ : GeometricallyConnected strX₂)
    (hf₁ : (Set.range jY₁.base)ᶜ.Finite) (hf₂ : (Set.range jY₂.base)ᶜ.Finite)
    {u : Y₁ ⟶ Y₂} {v : Y₂ ⟶ Y₁} (hu : u ≫ strY₂ = strY₁) (hv : v ≫ strY₁ = strY₂)
    (huv : u ≫ v = 𝟙 Y₁) (hvu : v ≫ u = 𝟙 Y₂) :
    ∃ (w : X₁ ⟶ X₂) (w' : X₂ ⟶ X₁),
      w ≫ strX₂ = strX₁ ∧ w' ≫ strX₁ = strX₂ ∧
      w ≫ w' = 𝟙 X₁ ∧ w' ≫ w = 𝟙 X₂ ∧ jY₁ ≫ w = u ≫ jY₂ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := ho₁; haveI := ho₂; haveI := hp₁; haveI := hp₂; haveI := hs₁; haveI := hs₂
  obtain ⟨w, ⟨hw, hjw⟩, -⟩ :=
    _root_.AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve
      (strZ := strX₂) hg₁ hf₁ hc₁ (u ≫ jY₂) (by rw [Category.assoc, hc₂, hu])
  obtain ⟨w', ⟨hw', hjw'⟩, -⟩ :=
    _root_.AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve
      (strZ := strX₁) hg₂ hf₂ hc₂ (v ≫ jY₁) (by rw [Category.assoc, hc₁, hv])
  obtain ⟨Φ₁, -, huniq₁⟩ :=
    _root_.AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve
      (strZ := strX₁) hg₁ hf₁ hc₁ jY₁ hc₁
  obtain ⟨Φ₂, -, huniq₂⟩ :=
    _root_.AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve
      (strZ := strX₂) hg₂ hf₂ hc₂ jY₂ hc₂
  refine ⟨w, w', hw, hw', ?_, ?_, hjw⟩
  · refine (huniq₁ (w ≫ w') ⟨by rw [Category.assoc, hw', hw], ?_⟩).trans
      (huniq₁ (𝟙 X₁) ⟨Category.id_comp _, Category.comp_id _⟩).symm
    rw [← Category.assoc, hjw, Category.assoc, hjw', ← Category.assoc, huv, Category.id_comp]
  · refine (huniq₂ (w' ≫ w) ⟨by rw [Category.assoc, hw, hw'], ?_⟩).trans
      (huniq₂ (𝟙 X₂) ⟨Category.id_comp _, Category.comp_id _⟩).symm
    rw [← Category.assoc, hjw', Category.assoc, hjw, ← Category.assoc, hvu, Category.id_comp]

/-- **`X_1(N)` over `𝔽_ℓ` is unique up to isomorphism, hence its rational
points up to bijection** (PROVEN).

Two steps, both already *stated* in this file or in `X0.lean`, which is
why this is bookkeeping rather than a theory:

* `IsCoarseModuliY1` is an INITIALITY property, so it determines
  `(Y, classify)` up to unique isomorphism over the base — that is
  `IsCoarseModuliY1.exists_inverse` above, and it gives `Y₁ ≅ Y₂` over
  `𝔽_ℓ`;
* over a FIELD a smooth curve has a unique smooth proper
  compactification — `exists_inverse_of_smoothCompactification` — so the
  isomorphism extends to `X₁ ≅ X₂`, and `relPointEquivOfInverse`
  (`X0.lean`, moduli-free) turns the inverse pair into a bijection on
  `𝔽_ℓ`-points.

The conclusion is `Nonempty (… ≃ …)` on points rather than an
isomorphism of schemes, for the same reason as in the `Γ₀` case: that is
all any consumer needs, and it avoids committing this file to a transport
of `RelPoint` along an isomorphism that nothing else here uses. -/
theorem nonempty_relPointEquiv_of_isX1Compactification {N ℓ : ℕ} (hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (h₁ : IsX1Compactification N strX₁ strY₁ jY₁)
    (h₂ : IsX1Compactification N strX₂ strY₂ jY₂) :
    Nonempty (RelPoint strX₁ (𝟙 (SpecF ℓ)) ≃ RelPoint strX₂ (𝟙 (SpecF ℓ))) := by
  obtain ⟨u, v, hu, hv, huv, hvu⟩ := IsCoarseModuliY1.exists_inverse h₁.coarse h₂.coarse
  obtain ⟨w, w', hw, hw', hww', hw'w, -⟩ :=
    exists_inverse_of_smoothCompactification hℓ h₁.comm h₂.comm h₁.isOpen h₂.isOpen
      h₁.isProper h₂.isProper h₁.smooth h₂.smooth h₁.connected h₂.connected
      h₁.finite_compl h₂.finite_compl hu hv huv hvu
  exact ⟨relPointEquivOfInverse hw hw' hww' hw'w⟩

/-! #### Deligne–Rapoport and Igusa, separated

The node below cited TWO classical theorems and asked for both at once: a
smooth proper model over `ℤ_(ℓ)` (Deligne–Rapoport, *Les schémas de
modules de courbes elliptiques*, Thm. VI.6.9) and the identification of its
special fibre with the `Γ₁(N)`-moduli curve in characteristic `ℓ` (Igusa
1959; Katz–Mazur 5.1.1, 6.7.2).  They are separated here (2026-07-28), and
the node is PROVEN over the two leaves.

**The recorded reason for bundling them is answered by the `Γ₀` layer
itself.**  That reason was: "bundled in rather than split off because a
producer builds the model and recognises its special fibre in one
construction; splitting them would require naming the model twice."
Naming the model twice is exactly what `X0.lean`'s
`exists_isX0Compactification_specialFibre` does — it takes the
`IsX0NeronDatum` as a hypothesis and produces the compactification of the
special fibre — and that file has had the two split all along.  So the
objection is a style preference that the sibling layer does not honour,
not an obstruction; and the node's own docstring lists the `Γ₀` trio it
mirrors with these two as separate members of it.

What the split buys: the first leaf's conclusion mentions no moduli at all
(only `IsCurveReductionModel`, i.e. a smooth proper relative curve with the
two fibre identifications and the valuative criterion), so a prover of it
needs no modular geometry in the conclusion — the moduli input is confined
to the hypothesis `hX`.  All of the moduli content is in the second.

**AMENDED 2026-07-30: the geometric half is now a PROOF, and the leaf under
it is smaller.**  `exists_x1CurveReductionModel` is PROVEN over the new leaf
`exists_x1SmoothProperCurveModel`, which asks only for the model and the
identification of its GENERIC fibre.  The special fibre, its naturality and
the valuative criterion were the three obligations that needed no modular
geometry at all, and they are discharged in Lean here rather than promised —
`X0.lean`'s `exists_x0CurveModel_of_base` had done exactly this on the `Γ₀`
side since 2026-07-27 and the `Γ₁` side had not caught up.  So the node is
still PROVEN over TWO leaves, and they are now
`exists_x1SmoothProperCurveModel` and
`exists_isX1Compactification_specialFibre`; the leaf COUNT is unchanged and
the first of the two got strictly weaker.
-/

/-- **Deligne–Rapoport: `X_1(N)` has a SMOOTH PROPER MODEL over `ℤ_(ℓ)`
whose GENERIC FIBRE is the given `X`** (sorry leaf, NEW 2026-07-30) — the
whole of the modular content of `exists_x1CurveReductionModel` below, which
is now PROVEN over this leaf alone.

TRUE, and classical: Deligne–Rapoport Thm. VI.6.9, or Katz–Mazur Thm. 5.1.1
plus Cor. 6.7.2.  For `ℓ ∤ N` the level structure is étale over the base,
which is exactly what makes the model SMOOTH rather than merely
semistable; at `ℓ ∣ N` the special fibre acquires the Deligne–Rapoport
singularities and no smooth model exists.

**WHY THIS LEAF EXISTS: THE `Γ₀` SIDE ALREADY DISCHARGED THREE OF THE SEVEN
OBLIGATIONS AND THE `Γ₁` SIDE WAS STILL CARRYING THEM** (2026-07-30).  The
statement below used to ask for a whole `IsCurveReductionModel`, i.e. seven
fields.  `X0.lean`'s `exists_x0CurveModel_of_base` shows that four of them
are FREE once the model and its generic fibre are in hand, and its own
docstring says so in terms ("what a Deligne–Rapoport specialist is now asked
for is the model and its generic fibre, and nothing else"):

* the SPECIAL fibre `X'` is existentially quantified in the conclusion below,
  so it need not be posited — take it to be `Limits.pullback xstr
  (SpecLoc.special toF)`, literally `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`, and then `spX` /
  `spX_nat` are the universal property of that pullback, i.e.
  `fibreIdentPullback`, which is PROVEN;
* `properX`, the valuative criterion, is `bijective_pre_generic_of_isProper`
  applied to `curve.isProper`, and that is PROVEN — mathlib's valuative
  criterion over the observation that `IsReductionBase` makes `R` a
  valuation ring;
* `genX` / `genX_nat` are the two fields of the `IsFibreIdent` this leaf
  returns, so they are field copying.

So this leaf is STRICTLY WEAKER than the statement it replaces, and no leaf
was added: the node below went from `sorry` to a proof, and this is what it
is a proof over.

**No moduli appears in the conclusion**, exactly as before: a smooth proper
geometrically connected curve over `SpecLoc R` together with the
identification of its generic fibre as a FUNCTOR of points.  The modular
input enters solely through `_hX`, which is what says that fibre is `X_1(N)`
rather than an arbitrary curve.

**THE ROUTE, and it is the `Γ₀` one step for step.**  `X0.lean` proves the
corresponding `exists_x0CompactificationModel` by (i) building the model
over `ℤ_(ℓ)` from the local coarse space
(`exists_x0IntegralCompactification`), (ii) comparing the caller's `X` with
the model's generic fibre through the initiality of coarse moduli
(`exists_iso_of_isCoarseModuliY0`, then
`exists_iso_of_isX0Compactification`), and (iii) transporting
`fibreIdentPullback (SpecLoc.generic R) xstr` along that isomorphism with
`IsFibreIdent.congrFibre`.  Only step (i) is irreducible along the moduli
axis; the `Γ₁` analogues of the three `Γ₀` leaves it rests on are

* the `Γ₁(N)`-coarse space exists over `ℤ_(ℓ)` (Katz–Mazur ch. 8) —
  `exists_isCoarseModuliY0_loc`'s twin;
* it has a smooth proper compactification with finite cusp locus there
  (Deligne–Rapoport IV.3, Katz–Mazur 13.11);
* INITIALITY of the generic fibre, i.e. coarse moduli commutes with the flat
  base change `ℤ_(ℓ) → ℚ` (Katz–Mazur 8.1).

They are deliberately NOT cut here: three leaves in place of one buys
nothing until somebody is actually working the moduli axis, and step (ii)'s
`Γ₁` ingredients (`IsCoarseModuliY1.exists_inverse` and
`exists_inverse_of_smoothCompactification`, both PROVEN and used together in
`nonempty_relPointEquiv_of_isX1Compactification` above) are already here.

**Each hypothesis is load-bearing** (the underscores record only that a
`sorry` consumes nothing): `_hℓ` makes `ZMod ℓ` a field, without which
`IsReductionBase` is unsatisfiable; `_hℓN` is good reduction itself,
refuted at `ℓ ∣ N`; `_hbase` pins `(R, toF)` as `ℤ_(ℓ)` with reduction mod
`ℓ`, and since the conclusion is existential a junk base would make the
leaf true and worthless; `_hX` is what makes the statement about `X_1(N)`.

**WHAT IS NOT A ROUTE**, inherited from the node below: discharging the
model with an `IsX0Compactification` at some other level `N'` is dead —
`X_1(N)` is not `X_0(N')` for any `N'` in the range that matters (at
`N = 25`, `X_0(25)` has genus `0` against `X_1(25)`'s `12`), and `N' = 0`
is refuted by `isEmpty_of_gamma0Datum_zero`. -/
theorem exists_x1SmoothProperCurveModel (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (_hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (_hX : IsX1Compactification N strX strY jY) :
    ∃ (XZ : Scheme.{0}) (xstr : XZ ⟶ SpecLoc R),
      IsSmoothProperCurve xstr ∧ Nonempty (IsFibreIdent (SpecLoc.generic R) xstr strX) :=
  sorry

/-- **Deligne–Rapoport: `X_1(N)` has GOOD REDUCTION at every `ℓ ∤ N`**
(**PROVEN 2026-07-30** over the single strictly weaker leaf
`exists_x1SmoothProperCurveModel` immediately above; a sorry leaf from
2026-07-28 until then) — the GEOMETRIC half of the node below.

The statement is UNCHANGED apart from the binders losing their underscores,
and its sole caller `exists_x1CurveModel_of_base` calls it exactly as
before.  What changed is that the four obligations of
`IsCurveReductionModel` that need no modular geometry — the special fibre,
its naturality, and the valuative criterion — are now DISCHARGED here
rather than promised by a `sorry`; see the leaf's docstring for the
accounting, which is `X0.lean`'s `exists_x0CurveModel_of_base` transported
step for step.

`X'` is `𝒳 ×_{ℤ_(ℓ)} 𝔽_ℓ`, which is what makes `spX` free; `exists_isX1Compactification_specialFibre` below is what says that scheme
IS `X_1(N)` over `𝔽_ℓ`, and it remains a separate leaf. -/
theorem exists_x1CurveReductionModel (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX1Compactification N strX strY jY) :
    ∃ (X' XZ : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (xstr : XZ ⟶ SpecLoc R),
      Nonempty (IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) := by
  obtain ⟨XZ, xstr, hcurve, ⟨eGen⟩⟩ :=
    exists_x1SmoothProperCurveModel N ℓ hℓ hℓN R toF hbase hX
  -- the special fibre is not posited: it is the pullback along the closed point
  exact ⟨Limits.pullback xstr (SpecLoc.special toF), XZ,
    Limits.pullback.snd xstr (SpecLoc.special toF), xstr,
    ⟨{ curve := hcurve
       genX := eGen.toEquiv
       spX := (fibreIdentPullback (SpecLoc.special toF) xstr).toEquiv
       genX_nat := eGen.nat
       spX_nat := (fibreIdentPullback (SpecLoc.special toF) xstr).nat
       properX := bijective_pre_generic_of_isProper ℓ R toF hbase xstr hcurve.isProper }⟩⟩

/-- **Igusa: the special fibre of a good model of `X_1(N)` IS `X_1(N)` over
`𝔽_ℓ`** (sorry leaf, NEW 2026-07-28) — the MODULI half of the node below,
and the `Γ₁` analogue of `X0.lean`'s
`exists_isX0Compactification_specialFibre`, which is stated the same way:
the model comes in as a hypothesis.

TRUE, and it is Igusa's theorem (Katz–Mazur 5.1.1, 6.7.2): the reduction
mod `ℓ` of the `Γ₁(N)`-moduli curve is the `Γ₁(N)`-moduli curve mod `ℓ`,
for `ℓ ∤ N`.

## FAITHFULNESS AUDIT — why the `∀ model` shape is safe here

This leaf quantifies over an ARBITRARY `IsCurveReductionModel`, not only
over the one `exists_x1CurveReductionModel` produces.  That is the shape
that made `nonempty_relPoint_atlas_of_relPoint` false (see the FALSITY
AUDIT above), so it is checked rather than assumed.  It is safe because a
smooth proper model over a DVR is DETERMINED by its generic fibre, so
there is only one model to quantify over:

* `_hbase` pins `R` as `ℤ_(ℓ)`, a discrete valuation ring — this is where
  that hypothesis is load-bearing, and dropping it breaks the argument
  rather than merely the packaging;
* at `genus ≥ 1` two smooth proper models of one curve over a DVR are
  isomorphic (Lichtenbaum–Shafarevich: the minimal regular model is
  unique, and a smooth proper model is it);
* at `genus 0` — which happens for `N ≤ 10` and `N = 12`, so it is not an
  empty corner — uniqueness still holds, but by a different argument that
  is worth writing down because it is the one a prover has to supply:
  `X_1(N)` has a rational cusp, `properX` extends it to an integral point,
  so the model has a section and is therefore `ℙ¹` over `R`, whence the
  special fibre is `ℙ¹` over `𝔽_ℓ`.

So the special fibre of an arbitrary model is isomorphic over `𝔽_ℓ` to the
one `exists_x1Compactification_finiteField` builds, and the leaf reduces to
TRANSPORTING an `IsX1Compactification` along an isomorphism of the ambient
curve.  That transport is not in this file yet and is part of the leaf;
`IsCoarseModuliY1` is an initiality property, so it moves along an
isomorphism with no content, and the remaining fields are geometric.

**Refuting check.**  If a successor finds that uniqueness of the smooth
proper model fails in some range of `N` — the place to look is genus `0`
without a rational point, which cannot occur here because the cusps are
rational, so a refutation would have to attack `properX` or the rationality
of a cusp — then the repair is to UN-SPLIT: have
`exists_x1CurveReductionModel` produce the identification too, i.e. restore
the bundled node.  Nothing else downstream would change, the node below
being the only consumer of either leaf.

**Note this leaf does NOT need `4 ≤ N`.**  It might look as though it
could cite `exists_x1Compactification_finiteField` and be done; it cannot,
both because that theorem carries `4 ≤ N` (which the node below does not
have, and which cannot be threaded in without changing the signatures of
`exists_x1ReductionAt` and its consumers) and because the compactification
it produces sits on an unrelated `X''`, whereas `strX'` here is pinned by
the model.  Supplying the isomorphism is exactly the work. -/
theorem exists_isX1Compactification_specialFibre {N ℓ : ℕ} (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    {R : Subring ℚ} {toF : R →+* ZMod ℓ} (_hbase : IsReductionBase ℓ R toF)
    {X Y X' XZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    {strX' : X' ⟶ SpecF ℓ} {xstr : XZ ⟶ SpecLoc R}
    (_hX : IsX1Compactification N strX strY jY)
    (_cm : IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) :
    ∃ (Y' : Scheme.{0}) (strY' : Y' ⟶ SpecF ℓ) (jY' : Y' ⟶ X'),
      Nonempty (IsX1Compactification N strX' strY' jY') :=
  sorry

/-- **Deligne–Rapoport / Igusa for `Γ₁(N)`: `X_1(N)` has good reduction at
every `ℓ ∤ N`** (**PROVEN 2026-07-28** over the two leaves above, which
separate the two classical theorems it cited; formerly a single `sorry`
leaf, and after the hoist below this node is ALL that is left of the
rank-`0` criterion's geometry).

TRUE, and classical.  For `ℓ ∤ N` the coarse space `X_1(N)` over `ℚ`
extends to a smooth proper model `𝒳` over `ℤ_(ℓ)` whose special fibre is
`X_1(N)` over `𝔽_ℓ`.  Deligne–Rapoport, *Les schémas de modules de courbes
elliptiques* (Antwerp II, 1973), Thm. VI.6.9 for the `Γ₀`/`Γ₁` moduli
problems, and Igusa 1959 for the original `Γ₁`-statement; Katz–Mazur,
*Arithmetic Moduli of Elliptic Curves*, Thm. 5.1.1 and Cor. 6.7.2 give the
representability and regularity in the form used here.  `ℓ ∤ N` is exactly
the condition that makes the level structure étale over the base, hence the
model SMOOTH rather than merely semistable — at `ℓ ∣ N` the special fibre
acquires the Deligne–Rapoport singularities and no `IsX1Compactification`
over `𝔽_ℓ` is produced at all.

**WHAT IS ASKED FOR, AND WHY IT IS THE MINIMAL RESIDUE.**  Two conclusions,
and the second is what makes the first `Γ₁`-specific rather than generic:

* `IsCurveReductionModel ℓ R toF xstr` — the integral model, the two fibre
  identifications as functors of points, and the valuative criterion.  Note
  it carries `curve : IsSmoothProperCurve xstr` where `X0.lean`'s
  `IsX0CurveModel` carries `model : IsX0Compactification N xstr ystr jZ`;
  the three geometric fields are all the Jacobian half ever reads off the
  model, which is precisely the observation that made the hoist mechanical.
* `IsX1Compactification N strX' strY' jY'` — the special fibre really is
  `X_1(N)` over `𝔽_ℓ`.  This is the `Γ₁` analogue of `X0.lean`'s
  `exists_isX0Compactification_specialFibre`.  **It is now SPLIT OFF, as
  `exists_isX1Compactification_specialFibre` above** (2026-07-28); the
  sentence that stood here — "bundled in rather than split off because a
  producer builds the model and recognises its special fibre in one
  construction; splitting them would require naming the model twice" — is
  withdrawn, for the reason the subsection comment gives: the `Γ₀` sibling
  names the model twice and has been split all along.

Everything downstream — the relative Jacobian, its two fibres, additivity,
Abel–Jacobi over the base, the Néron mapping property, injectivity of
reduction — is `exists_neronReductionDatum_of_curveModel` plus
`neronReduction_injective`, both PROVEN and both moduli-free.

**Each hypothesis is load-bearing**; the underscore prefixes record only
that a `sorry` consumes nothing.

* `_hℓ` makes `ZMod ℓ` a field, without which `SpecF ℓ` is not the spectrum
  of a residue field and `IsReductionBase` is unsatisfiable.
* `_hℓN` is good reduction, refuted above at `ℓ ∣ N`.
* `_hbase` pins `(R, toF)` as `ℤ_(ℓ)` with reduction mod `ℓ`; a junk base
  would let a junk special fibre in, and since the conclusion is
  existential that would make this leaf true while worthless.
* `_hX` is what makes the statement about `X_1(N)` rather than about an
  arbitrary smooth proper curve over `ℚ` — it is the moduli input to the
  model, and it is what the second conclusion is the special-fibre echo of.

**NOT A ROUTE**, and this is the same dead end the node below records:
discharging the model with an `IsX0Compactification` at some other level
`N'` fails, because `X_1(N)` is not `X_0(N')` for any `N'` in the range
that matters (at `N = 25`, `X_0(25)` has genus `0` against `X_1(25)`'s
genus `12`), and `N' = 0` is refuted by `isEmpty_of_gamma0Datum_zero`. -/
theorem exists_x1CurveModel_of_base (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX1Compactification N strX strY jY) :
    ∃ (X' Y' XZ : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (strY' : Y' ⟶ SpecF ℓ)
      (jY' : Y' ⟶ X') (xstr : XZ ⟶ SpecLoc R),
      Nonempty (IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) ∧
        Nonempty (IsX1Compactification N strX' strY' jY') := by
  obtain ⟨X', XZ, strX', xstr, ⟨cm⟩⟩ :=
    exists_x1CurveReductionModel N ℓ hℓ hℓN R toF hbase hX
  obtain ⟨Y', strY', jY', hX'⟩ :=
    exists_isX1Compactification_specialFibre hℓ hℓN hbase hX cm
  exact ⟨X', Y', XZ, strX', strY', jY', xstr, ⟨cm⟩, hX'⟩

/-- **The Néron reduction datum for `X_1(N)` at a good odd prime**
(**PROVEN 2026-07-28**; formerly a single `sorry`.  The hoist described in
the cut audit below has been EXECUTED, and what is left of this node is the
one genuinely `Γ₁`-specific statement, `exists_x1CurveModel_of_base` above).

TRUE, and classical.  For `ℓ` odd with `ℓ ∤ N` the modular curve `X_1(N)`
has good reduction at `ℓ`: it has a smooth proper model `𝒳` over
`ℤ_(ℓ)` — Deligne–Rapoport / Igusa — whose special fibre is `X_1(N)` over
`𝔽_ℓ`, and whose relative Jacobian `𝒥` is the Néron model of `J_1(N)`.
The Néron mapping property and the valuative criterion of properness turn
rational points into integral ones, restriction to the special fibre then
defines `redX` and `redJ`, and `redJ` is INJECTIVE because `hfin` makes
`J_1(N)(ℚ)` torsion while the kernel of reduction is the group of points
of a formal group over `ℤ_ℓ`, torsion-free for `ℓ` odd.

**THIS IS THE `Γ₁` FORM OF THREE `X0.lean` DECLARATIONS AT ONCE**, and
the correspondence is exact rather than approximate:

* `exists_x0NeronDatum` — the model, its relative Jacobian, and the two
  fibre identifications, packaged there as `IsX0NeronDatum`;
* `exists_isX0Compactification_specialFibre` — that the special fibre of
  the model really is the modular curve over `𝔽_ℓ`;
* `neronReduction_injective` (over `neronKernel_torsionFree`) — the
  formal-group fact, which is what `IsX0NeronDatum.toReduction` consumes
  to produce the `IsX0ReductionAt`.

They were bundled into ONE leaf here rather than mirrored one-for-one
because only the first is `Γ₁`-specific: `IsX0NeronDatum`'s single
moduli-carrying field is `model : IsX0Compactification N xstr ystr jZ`,
and everything else in that 200-line structure — the base, the four fibre
identifications, their naturality, additivity, compatibility with
Abel–Jacobi, the Néron mapping property, the valuative criterion — is
moduli-free and would be copied character for character.

**CUT AUDIT, 2026-07-27, RE-RUN AND EXECUTED 2026-07-28.**  The
load-bearing assertion was "`model` is the only moduli-carrying field, and
nothing in the reduction machinery touches it", and its refutation
criterion was a `d.model` inside `namespace IsX0NeronDatum`.  Re-run:

* the namespace runs from `structure IsX0NeronDatum` to
  `end IsX0NeronDatum` and contains `intJ`, `intX`, `redJ`, `redX`,
  `redJ_def`, `redX_def`, `pre_intJ`, `pre_intX`, `intJ_add`, `intJ_aj`,
  `redJ_add`, `red_aj`, `finite_intPoints` and `toReduction`;
* `grep -n '\.model\b' Fermat/FLT/ModularCurve/X0.lean` gives 67 hits, the
  earliest at line 29571, against a namespace running 26253–26455.  **Zero
  hits inside the range**, so the audit stands and the hoist was mechanical.

**THE HOIST IS DONE**, in `Fermat/FLT/ModularCurve/NeronReduction.lean`:
`IsCurveReductionModel` (the curve half, with `model` replaced by
`curve : IsSmoothProperCurve xstr`), `IsNeronReductionDatum` (the full
datum minus `model`) with its whole namespace and `toReduction`, and the
PROVEN assembly `exists_neronReductionDatum_of_curveModel`.  Two notes on
what actually happened, against what the audit predicted:

* the one apparent counterexample to "moduli-free" is
  `exists_x0JacobianModel_of_curveModel`, whose proof opens
  `⟨cm.model.isProper, cm.model.smooth, cm.model.connected⟩`.  That reads
  the three GEOMETRIC facts the moduli structure happens to bundle, not the
  moduli structure — hence the `curve` field, and hence the hoist survived;
* the audit put the new file under `Fermat/FLT/Mathlib/AlgebraicGeometry/`,
  which is not possible: `SpecQ`, `SpecF`, `SpecLoc`, `IsReductionBase`,
  `IsSmoothProperCurve`, `IsFibreIdent`, `IsJacobianOf`, `IsX0ReductionAt`,
  `exists_relativeJacobian`, `isSmoothProperCurve_of_fibreIdent`,
  `exists_jacobianFibreIdent`, `bijective_pre_generic_of_isProper` and
  `neronReduction_injective` are ALL declared inside `X0.lean`, so an
  upstream module would have to drag them out of a 38 000-line file with
  twenty concurrent owners.  The new module therefore sits DOWNSTREAM of
  `X0.lean` instead, and `X0.lean` is left byte-identical; the one-region
  cleanup that makes `IsX0CurveModel`/`IsX0NeronDatum` extend it is
  recorded in that module's header for whoever next owns those lines.

So the residue of THIS node is exactly one statement, and it is the only
genuinely `Γ₁`-specific one: **`exists_x1CurveModel_of_base` above**,
Deligne–Rapoport / Igusa for `Γ₁(N)`.  Nothing else here is new
mathematics, and the proof below is the assembly.

**WHAT IS NOT A ROUTE.**  Discharging `model` with an `IsX0Compactification`
at some other level `N'` is dead: `X_1(N)` is not `X_0(N')` for any `N'` in
the range that matters (at `N = 25`, `X_0(25)` has genus `0` and `X_1(25)`
genus `12`), and `N' = 0` is refuted by `isEmpty_of_gamma0Datum_zero`, which
forces the coarse space empty while `finite_compl` then makes a smooth
proper curve over a field finite.

**Every hypothesis is load-bearing**, each fails the conclusion on its own,
and now that the node is proven each is consumed at a named site:

* `hfin` is rank `0`.  Without it `J_1(N)(ℚ)` is infinite, hence not
  torsion, and `redJ_inj` is false: the kernel of reduction is exactly
  where the non-torsion points go.  Consumed as `d.finite_intPoints hfin`,
  feeding `neronReduction_injective`.
* `hℓ2` is the formal-group hypothesis.  At `ℓ = 2` the kernel of
  reduction can contain `2`-torsion and `redJ_inj` fails.  Consumed by
  `neronReduction_injective`.
* `hℓN` is good reduction.  At `ℓ ∣ N` the special fibre is not a smooth
  curve, so no `IsX1Compactification` over `𝔽_ℓ` is produced.  Consumed by
  `exists_x1CurveModel_of_base`.
* `hℓ` is what makes `ZMod ℓ` a field and what `exists_isReductionBase`
  needs to build `ℤ_(ℓ)` at all.  Consumed twice.
* `hX` is what makes the statement about `X_1(N)` rather than an
  arbitrary curve, and it is what supplies the moduli input to the
  integral model.  Consumed by `exists_x1CurveModel_of_base`.
* `jac` is EXPLICIT because the conclusion mentions it: without it
  `IsX0ReductionAt` has nothing to be a reduction *of*, and `red_aj`
  would be unstateable.

**Non-vacuity.**  `IsX0ReductionAt jac jac'` carries `redJ_inj` and
`red_aj`, and those two together already force
`#(jac.aj '' X_1(N)(ℚ)) ≤ #J_1(N)(𝔽_ℓ)`; no junk witness discharges it,
because `jac'` pins `J'` as the genuine Jacobian of the produced curve by
its own initiality field.  That implication is not a remark: it is the
proof of `exists_injective_reduction_of_rankZeroJacobian` below, so the
compiler certifies that this node is at least as hard as the criterion it
stands in for. -/
theorem exists_x1ReductionAt (N ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓN : ¬ ℓ ∣ N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (hX : IsX1Compactification N strX strY jY) (jac : IsJacobianOf strX ab o)
    (hfin : Finite (RelPoint jstr (𝟙 SpecQ))) :
    ∃ (X' Y' J' : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (strY' : Y' ⟶ SpecF ℓ)
      (jY' : Y' ⟶ X') (jstr' : J' ⟶ SpecF ℓ) (ab' : AbelianSchemeStruct jstr')
      (o' : RelPoint strX' (𝟙 (SpecF ℓ))) (jac' : IsJacobianOf strX' ab' o'),
      Nonempty (IsX1Compactification N strX' strY' jY') ∧
        Nonempty (IsX0ReductionAt jac jac') := by
  obtain ⟨R, toF, hbase⟩ := exists_isReductionBase ℓ hℓ
  obtain ⟨X', Y', XZ, strX', strY', jY', xstr, ⟨cm⟩, ⟨hX'⟩⟩ :=
    exists_x1CurveModel_of_base N ℓ hℓ hℓN R toF hbase hX
  obtain ⟨J', JZ, jstr', ab', o', jac', jstrZ, abZ, oZ, jacZ, ⟨d⟩⟩ :=
    exists_neronReductionDatum_of_curveModel ℓ R toF hbase cm jac
  exact ⟨X', Y', J', strX', strY', jY', jstr', ab', o', jac', ⟨hX'⟩,
    ⟨d.toReduction
      (neronReduction_injective ℓ R toF hbase hℓ2 abZ (d.finite_intPoints hfin))⟩⟩

/-- **The rank-`0` reduction INJECTION, `X_1(N)(ℚ) ↪ X_1(N)(𝔽_ℓ)`**
(PROVEN 2026-07-27 over `exists_x1ReductionAt` and
`nonempty_relPointEquiv_of_isX1Compactification`; formerly a single
`sorry` node).

TRUE, and classical.  `hJ` makes `J_1(N)(ℚ)` finite, hence torsion; for
`ℓ` an odd prime of good reduction the reduction map on torsion
`J_1(N)(ℚ) → J_1(N)(𝔽_ℓ)` is INJECTIVE, its kernel being the points of a
formal group over `ℤ_ℓ`, which is torsion-free for `ℓ` odd; Abel–Jacobi
based at a rational point embeds `X_1(N)(ℚ)` into `J_1(N)(ℚ)` and
commutes with reduction; so `X_1(N)(ℚ)` injects into `X_1(N)(𝔽_ℓ)`.

**Every hypothesis is load-bearing**, verbatim as in `X0.lean`'s
`card_le_of_rankZeroJacobian`:

* without finiteness in `hJ`, a positive-rank Jacobian gives infinitely
  many rational points already in genus `1`;
* without injectivity of Abel–Jacobi in `hJ`, genus `0` refutes it — a
  rational curve has trivial Jacobian and infinitely many rational
  points;
* without `hℓ2` the formal-group argument fails at `ℓ = 2`, where
  `2`-torsion can die under reduction;
* without `hℓN` there is no good reduction at `ℓ` and the special fibre
  is not a smooth curve.

**RELATION TO `card_le_of_rankZeroJacobian`.**  This is the same theorem
in its injective form, and the injection is the primitive: that
theorem's own proof produces it and then discards it in favour of a
`Finset` bound.  The bound follows here by
`Nat.card_le_card_of_injective`, or on `Finset`s by
`Finset.card_le_card_of_injOn`.  The injective form is stated because a
`Nat.card` hypothesis — which is what `IsX1TwentyFiveDatum` carries — is
not recoverable from the `Finset` form without finiteness input that the
`Finset` form does not supply.  Nothing in `X0.lean` is edited to say
this: the `Γ₀` statement has concurrent owners, and `HasRankZeroJacobian`
is shared as-is.

The three arithmetic theories this needs — Jacobians of genus `> 1`
curves with Abel–Jacobi, Mordell–Weil, and the formal group of an abelian
scheme — are shared VERBATIM with `card_le_of_rankZeroJacobian`; only the
moduli interpretation of the curve differs, and this statement does not
mention it.  So a successor closing either one closes both.

**HOW IT IS PROVEN**, and it is the identical two-line sandwich that
`card_le_of_sieve` and `card_le_of_rankZeroJacobian` both run.
`exists_x1ReductionAt` hands over a reduction datum whose special fibre
`X''` is a copy of `X_1(N)` over `𝔽_ℓ`;
`nonempty_relPointEquiv_of_isX1Compactification` identifies its rational
points with those of the caller's `X'`; and `redX` is injective because
it is sandwiched between two injections — `aj` (positive genus, carried
by `hJ`) on the outside and `redJ` (rank `0`) on the inside, joined by
`red_aj`.  Nothing else in `hJ` is used, and `hℓ`, `hℓ2`, `hℓN` are
consumed exactly where the refutations above say they must be.

Note which shape the conclusion keeps: the INJECTION, not a `Finset`
bound.  A `Nat.card` hypothesis such as `IsX1TwentyFiveDatum.card_ptF3`
is not recoverable from the `Finset` form, so simplifying this to match
`card_le_of_rankZeroJacobian`'s statement would break the level-`25`
assembly. -/
theorem exists_injective_reduction_of_rankZeroJacobian {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX1Compactification N strX strY jY) (hJ : HasRankZeroJacobian strX)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓN : ¬ ℓ ∣ N)
    {X' Y' : Scheme.{0}} {strX' : X' ⟶ SpecF ℓ} {strY' : Y' ⟶ SpecF ℓ}
    {jY' : Y' ⟶ X'} (hX' : IsX1Compactification N strX' strY' jY') :
    ∃ red : RelPoint strX (𝟙 SpecQ) → RelPoint strX' (𝟙 (SpecF ℓ)),
      Function.Injective red := by
  obtain ⟨J, jstr, ab, o, jac, hJfin, hajinj⟩ := hJ
  obtain ⟨X'', Y'', J'', strX'', strY'', jY'', jstr'', ab'', o'', jac'', ⟨hX''⟩, ⟨red⟩⟩ :=
    exists_x1ReductionAt N ℓ hℓ hℓ2 hℓN hX jac hJfin
  obtain ⟨e⟩ := nonempty_relPointEquiv_of_isX1Compactification hℓ hX'' hX'
  refine ⟨fun x => e (red.redX x), ?_⟩
  intro a b hab
  refine hajinj (red.redJ_inj ?_)
  rw [red.red_aj, red.red_aj, e.injective hab]

/-! ### Galois descent of a point to a section

The `Γ₁` counterpart of `X0.lean`'s descent subsection, and it is
strictly smaller: a `Γ₀`-structure is a subgroup SCHEME and has to be
built as the scheme-theoretic image of a family of geometric points
(`spanScheme`), with closure under the group law transported field by
field; a `Γ₁`-structure is a single SECTION, so all that is needed is
that a Galois-invariant `ℚ̄`-point of a `ℚ`-scheme is a `ℚ`-point.
-/

/-! #### Galois descent of a point, over a variable base field

The two declarations below are the whole content of
`exists_section_of_galoisInvariant`, and they are stated over a VARIABLE
perfect base field `F` rather than at the literal `ℚ`.  That is
`isIntegralHom_specAlgClos'`'s discipline (`X0.lean`) applied in a fresh
spot, and it is load-bearing rather than stylistic: at the concrete base
`ℚ` the two `Algebra ℚ (AlgebraicClosure ℚ)` instances
(`DivisionRing.toRatAlgebra` and `AlgebraicClosure.instAlgebra`) form a
DIAMOND, elaboration of `_ ≃ₐ[ℚ] _` picks the former, and
`IsAlgClosure ℚ ℚ̄` — hence `Normal`, `Algebra.IsSeparable`, `IsGalois` —
then fails to synthesise.  With `F` a variable there is one instance and
the proofs are short.  Verified: at the literal `ℚ`,
`inferInstance : IsAlgClosure ℚ (AlgebraicClosure ℚ)` FAILS. -/

/-- **An element of `F̄` fixed by the whole absolute Galois group lies in
`F`** (PROVEN, from `Mathlib` alone).

`F̄/F` is normal (`IsAlgClosure.normal`) and separable (`PerfectField F`
plus algebraicity), hence Galois, and
`InfiniteGalois.mem_range_algebraMap_iff_fixed` is exactly this statement
for an arbitrary infinite Galois extension.  No finiteness anywhere: the
fixed field of the full group is `⊥` in the infinite setting too, which is
the theorem in `Mathlib/FieldTheory/Galois/Infinite.lean`.

`PerfectField F` is what cannot be dropped — over `𝔽_p(t)` the extension
`F̄/F` is not separable and the fixed field of `Aut(F̄/F)` is the perfect
closure, strictly larger than `F`. -/
theorem mem_range_algebraMap_of_absoluteGaloisGroup_fixed {F : Type} [Field F] [PerfectField F]
    (x : AlgebraicClosure F)
    (h : ∀ σ : Field.absoluteGaloisGroup F,
      (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) x = x) :
    x ∈ Set.range (algebraMap F (AlgebraicClosure F)) := by
  haveI : IsGalois F (AlgebraicClosure F) := ⟨⟩
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr h

/-- **Galois descent of a point: a `Γ_F`-invariant `F̄`-point of ANY
scheme comes from an `F`-point** (PROVEN, sorry-free).

This is `A(F) ≃ A(F̄)^{Γ_F}` in the only direction that has content, and
it is stated for an arbitrary `A : Scheme.{0}` with no structure morphism,
no properness and no group law — none of which the argument uses.  That
generality is deliberate: `exists_section_of_galoisInvariant` below is the
one-line specialisation, and a successor wanting descent for a `Γ₀`-style
object can cite this rather than redo it.

**THE PROOF, IN FOUR STEPS.**

1. `Scheme.SpecToEquivOfField` (`Mathlib`) writes `p : Spec F̄ ⟶ A` as a
   point `a : A` together with an embedding `φ : κ(a) ⟶ F̄`, via
   `p = Spec.map φ ≫ A.fromSpecResidueField a`.
2. `specGal σ ≫ p = p` becomes `φ ≫ σ = φ`: compose the factorisation with
   `Spec.map σ`, cancel the MONO `A.fromSpecResidueField a` (it is a
   preimmersion), and use full faithfulness of `Spec` (`Spec.map_inj`).
   So every value of `φ` is `Γ_F`-fixed.
3. `mem_range_algebraMap_of_absoluteGaloisGroup_fixed` puts the image of
   `φ` inside the range of `algebraMap F F̄`, which is a subring on which
   `algebraMap` is a bijection onto its range (it is injective, `F` being a
   field), so `φ` factors as `algebraMap F F̄ ∘ ψ` for a ring map
   `ψ : κ(a) ⟶ F`.
4. `Spec.map ψ ≫ A.fromSpecResidueField a` is the descended point, and
   `specAlgClos F ≫ (-) = p` is step 1 read backwards.

**No separatedness is used, and the conclusion is correspondingly only
EXISTENCE.**  Uniqueness of the descended section is what would need `A`
separated over `F`; nothing downstream asks for it, so it is not claimed.
The docstring of `exists_section_of_galoisInvariant` previously said
properness (through `ab.proper`) was needed — that is true of uniqueness
and false of existence, and the corrected version below records it. -/
theorem exists_specSection_of_specGal_invariant {F : Type} [Field F] [PerfectField F]
    {A : Scheme.{0}} (p : Spec (CommRingCat.of (AlgebraicClosure F)) ⟶ A)
    (hinv : ∀ σ : Field.absoluteGaloisGroup F, specGal σ ≫ p = p) :
    ∃ s : Spec (CommRingCat.of F) ⟶ A, specAlgClos F ≫ s = p := by
  set d := Scheme.SpecToEquivOfField (AlgebraicClosure F) A p with hd
  have hp : Spec.map d.2 ≫ A.fromSpecResidueField d.1 = p :=
    (Scheme.SpecToEquivOfField (AlgebraicClosure F) A).symm_apply_apply p
  have hfix : ∀ (σ : Field.absoluteGaloisGroup F) (t : A.residueField d.1),
      (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (d.2.hom t) = d.2.hom t := by
    intro σ t
    have h1 : Spec.map (d.2 ≫ CommRingCat.ofHom
        ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toAlgHom.toRingHom))
        ≫ A.fromSpecResidueField d.1 = Spec.map d.2 ≫ A.fromSpecResidueField d.1 := by
      rw [Spec.map_comp, Category.assoc, hp, ← specGal, hinv σ]
    have h3 := Spec.map_inj.mp ((cancel_mono (A.fromSpecResidueField d.1)).mp h1)
    exact congrArg (fun (m : A.residueField d.1 ⟶ _) => m.hom t) h3
  have hmem : ∀ t : A.residueField d.1,
      d.2.hom t ∈ (algebraMap F (AlgebraicClosure F)).range := fun t =>
    mem_range_algebraMap_of_absoluteGaloisGroup_fixed _ (fun σ => hfix σ t)
  set ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F) with hιdef
  have hιinj : Function.Injective ι := ι.injective
  let eR : F ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun x y hxy => hιinj (congrArg Subtype.val hxy), ι.rangeRestrict_surjective⟩
  let ψ : A.residueField d.1 →+* F :=
    (eR.symm : ι.range →+* F).comp (d.2.hom.codRestrict ι.range hmem)
  have hψ : ∀ t, ι (ψ t) = d.2.hom t := fun t =>
    congrArg Subtype.val (eR.apply_symm_apply ⟨d.2.hom t, hmem t⟩)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ A.fromSpecResidueField d.1, ?_⟩
  rw [specAlgClos, ← Category.assoc, ← Spec.map_comp]
  refine Eq.trans ?_ hp
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hψ)

/-- **Every endomorphism of `Spec ℚ` is the identity** (PROVEN).

`Spec` is fully faithful and `ℚ` is initial in `CommRing`
(`Rat.subsingleton_ringHom`), so `Spec ℚ ⟶ Spec ℚ` is a singleton.  The
`Γ₁` mirror of `specF_hom_eq_id` above, and what makes the `RelPoint` side
condition of a descended section automatic. -/
theorem specQ_hom_eq_id (f : SpecQ ⟶ SpecQ) : f = 𝟙 SpecQ := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage (𝟙 SpecQ)]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **A Galois-invariant geometric point of an abelian scheme over `ℚ` is
a section** (**PROVEN 2026-07-27**, sorry-free, over
`exists_specSection_of_specGal_invariant`; formerly a sorry leaf).

TRUE, and it is Galois descent for points in its most basic form: for any
scheme `A` over a field `k` with separable closure `k^s`, the natural map
`A(k) → A(k^s)^{Γ_k}` is a bijection.  A `Γ_ℚ`-fixed `ℚ̄`-point has image
a point of `A` whose residue field embeds in `ℚ̄` with `Γ_ℚ`-fixed image,
hence lands in `ℚ`, so the point is already defined over `ℚ`.

**CORRECTION to what this docstring used to claim.**  It said separatedness
of `A` over `ℚ` (through `ab.proper`) was needed "so the descended morphism
is unique".  That is right about UNIQUENESS and irrelevant here: the
conclusion is an existence statement, and the proof uses no property of `f`
at all.  `ab` survives in the signature only because `_hinv` is phrased with
`ab.galSMul`; the abelian-scheme structure contributes nothing else, which is
why the general form above is stated for a bare `Scheme`.

**The `RelPoint` side condition is free.**  `sec ≫ f` is an endomorphism of
`Spec ℚ`, and `specQ_hom_eq_id` makes every such endomorphism the identity —
`ℚ` is initial in `CommRing`.  So the descended morphism is automatically a
SECTION and no compatibility has to be checked.

**WHAT IS AND IS NOT SHARED WITH `X0.lean`.**  The `Γ₀` side never
descends a POINT: `exists_cyclicSubgroupOfOrder_of_galoisStable` descends
a finite Galois-STABLE set to a closed subgroup SCHEME, through
`spanScheme`, and the two directions of `ratPoint_liesIn_spanScheme` and
`exists_geomPt_factor_span` both take a rational point as INPUT.  So this
leaf is genuinely new rather than a restatement — but it is also the
easier half of what that subsection does, exactly as
`nonempty_gamma1Datum_of_ratPoint`'s docstring predicts: no closure under
the group law has to be transported, and the descent is of one morphism
rather than of an ideal sheaf.

**THE `spanScheme` ROUTE WAS NOT NEEDED, and this corrects the plan this
docstring used to record.**  It proposed building the descent through
scheme-theoretic images and a comparison of kernel ideal sheaves, in the
style of `ratPoint_liesIn_spanScheme`.  That is a correct but much heavier
route: the residue field of the image point is already the whole of the
"scheme-theoretic image finite over `ℚ`" idea, and `Mathlib`'s
`Scheme.SpecToEquivOfField` hands it over directly, so no ideal sheaf and
no `app_injective_specAlgClos` appear in the proof.  A successor who wants
descent of something LARGER than a point (a subscheme, a subgroup) will
still want that apparatus; for a point it is not needed.

**`hinv` is INVARIANCE, not stability, and the difference is the whole
`Γ₀`/`Γ₁` distinction.**  `exists_cyclicSubgroupOfOrder_of_galoisStable`
asks only `galSMul σ y ∈ zmultiples y`, which is what a rational
SUBGROUP needs; asking only that here would make the statement FALSE —
take `y` a `ℚ̄`-point of order `3` on a curve with no rational `3`-torsion
whose subgroup `⟨y⟩` is `Γ_ℚ`-stable (`X_0(3)` has rational points, so
such curves exist), and no section of `A` over `ℚ` restricts to it.

Note that no hypothesis on the ORDER of `y` appears: descent of a point
has nothing to do with torsion, and the order is transported separately
by `exists_pointOfExactOrder_of_geomPt` below.  `ab` is taken because the
consumer has it and because `hinv` is phrased with `ab.galSMul`; the proof
uses none of its fields. -/
theorem exists_section_of_galoisInvariant {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (y : GeomFibrePt f (𝟙 SpecQ))
    (hinv : ∀ σ : Field.absoluteGaloisGroup ℚ, ab.galSMul (𝟙 SpecQ) σ y = y) :
    ∃ (sec : SpecQ ⟶ A) (hsec : sec ≫ f = 𝟙 SpecQ),
      RelPoint.ofSection sec hsec (specAlgClos ℚ ≫ 𝟙 SpecQ) = y := by
  obtain ⟨s, hs⟩ := exists_specSection_of_specGal_invariant (F := ℚ) y.1
    (fun σ => congrArg Subtype.val (hinv σ))
  refine ⟨s, specQ_hom_eq_id (s ≫ f), Subtype.ext ?_⟩
  refine Eq.trans ?_ hs
  rw [Category.comp_id]
  rfl

/-- **A Galois-invariant geometric point of exact order `N` is a
`Γ₁(N)`-level structure** (PROVEN over the descent leaf above).

The content is the reduction of `PointOfExactOrder.geom_order` — stated
at EVERY algebraically closed `K` and every `K`-point of the base — to
the single base `ℚ̄`.  `exists_injective_pre_geomBase` (`X0.lean`,
PROVEN) supplies, for each such `(K, t)`, an embedding
`e : Spec K ⟶ Spec ℚ̄` over `Spec ℚ` such that `RelPoint.pre e` is
injective; that map is additive by `ab.pre_add`/`ab.pre_zero`, so it
preserves `addOrderOf`, and the value of the section at `t` is the image
under it of the value at `ℚ̄`.  So `geom_order` at an arbitrary `K` is
`geom_order` at `ℚ̄`, which is `hy`.

This is the `Γ₁` analogue of the step that `geom_cyclic_zmulPts` performs
for `CyclicSubgroupOfOrder.geom_cyclic`, and it is where the docstring of
`PointOfExactOrder` cashes in its claim that testing on geometric fibres
"is insensitive to the base": `ℚ` is initial among rings, so a
`K`-point of `Spec ℚ` is unique, and the algebraic closure of `ℚ` inside
`K` is a copy of `ℚ̄` over which the section is already split. -/
theorem exists_pointOfExactOrder_of_geomPt {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) {N : ℕ} (y : GeomFibrePt f (𝟙 SpecQ))
    (hy : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
          addOrderOf y = N)
    (hinv : ∀ σ : Field.absoluteGaloisGroup ℚ, ab.galSMul (𝟙 SpecQ) σ y = y) :
    Nonempty (PointOfExactOrder ab N) := by
  obtain ⟨sec, hsec, hval⟩ := exists_section_of_galoisInvariant ab y hinv
  refine ⟨{ sec := sec, sec_comp := hsec, geom_order := ?_ }⟩
  intro K _ _ t
  letI := ab.addCommGroup t
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  obtain ⟨eK, heK, hinjK⟩ := exists_injective_pre_geomBase (f := f) K t
  -- `RelPoint.pre eK` is additive, hence order-preserving, and injective
  let Φ : GeomFibrePt f (𝟙 SpecQ) →+ RelPoint f t :=
    { toFun := fun w => RelPoint.pre eK heK w
      map_zero' := ab.pre_zero eK heK
      map_add' := fun a b => ab.pre_add eK heK a b }
  have hΦ : Φ (RelPoint.ofSection sec hsec (specAlgClos ℚ ≫ 𝟙 SpecQ))
      = RelPoint.ofSection sec hsec t := by
    apply Subtype.ext
    show eK ≫ (specAlgClos ℚ ≫ 𝟙 SpecQ) ≫ sec = t ≫ sec
    rw [← Category.assoc, heK]
  rw [← hΦ, addOrderOf_injective Φ hinjK, hval]
  exact hy

/-- **A rational point of exact order `N` on an elliptic curve over `ℚ`
gives a `Γ₁(N)`-structure over `Spec ℚ`** (PROVEN 2026-07-27 over
`exists_section_of_galoisInvariant`; formerly a single `sorry` node).

TRUE.  This is the `Γ₁` analogue of `nonempty_gamma0Datum_of_stable`, and
it is where the elliptic-curve side and the moduli side meet.

WHAT IT NEEDS, in dependency order — and all three steps are now written,
with only step 2 still open.

1. `exists_ellipticScheme_of_weierstrass` — PROVEN in `X0.lean` (over
   the five leaves of `EllipticScheme.lean`) — gives an abelian scheme
   `f : A ⟶ Spec ℚ` of relative dimension `1` together with a
   Galois-equivariant `≃+` from `(E⁄ℚ̄).Point` to the geometric fibre.
2. **Galois descent of the point to a SECTION**, which is the leaf
   `exists_section_of_galoisInvariant` above, consumed through
   `exists_pointOfExactOrder_of_geomPt`.  `P` is `ℚ`-rational, so its
   image in the geometric fibre is FIXED by `Γ_ℚ`; and for a scheme
   separated over `ℚ` the `ℚ`-points are the Galois-fixed `ℚ̄`-points, so
   the fixed geometric point is a section `Spec ℚ ⟶ A`.  This is the only
   genuinely missing step; see that leaf's docstring for the route and
   for what is and is not shared with the `Γ₀` descent.
3. Order transport, PROVEN here.  `Affine.Point.map` along `ℚ → ℚ̄` is an
   injective additive map, so `addOrderOf P` is unchanged
   (`addOrderOf_injective` over `Point.map_injective`); the `≃+` of step
   1 preserves it by `AddEquiv.addOrderOf_eq`; and `Γ_ℚ`-invariance of
   the base-changed point is `Point.map_map` plus
   `Subsingleton (ℚ →ₐ[ℚ] ℚ̄)`, since `σ ∘ (ℚ ↪ ℚ̄) = (ℚ ↪ ℚ̄)`.

   *Elaboration note, paid for once.*  `Point.map_map` cannot be used as
   a `rw` here: at the concrete base `ℚ` the two spellings
   `E.toAffine.Point` and `(E⁄ℚ).Point` carry different `CommRing ℚ`
   instance paths (`Rat.commRing` versus `Rat.instField.toCommRing`), so
   the rewritten goal is rejected at `instances` transparency.  Applying
   it as a TERM inside a `calc` elaborates fine, because unification is
   free to see through the diamond.  This is the "duplicate instances
   that print identically" trap in a fresh spot.

**`hN : N ≠ 0` IS NOT LOAD-BEARING, and the previous version of this
paragraph was WRONG** (corrected 2026-07-27, by writing the proof: it
does not use `hN`, and the compiler agrees).  The claim was inherited by
analogy from the FALSITY AUDIT of
`exists_cyclicSubgroupOfOrder_of_galoisStable`, where `N = 0` really does
refute the statement — but the analogy fails, and precisely at the
`Γ₀`/`Γ₁` difference this file exists to record.  `CyclicSubgroupOfOrder`
carries an `isFinite` field, so a subgroup scheme "of order `0`" is a
contradiction and `isEmpty_of_gamma0Datum_zero` holds.
`PointOfExactOrder` carries no finiteness at all: its only condition is
`addOrderOf (section) = N` on geometric fibres.  At `N = 0` that asks for
a section of infinite order, and an elliptic curve over `ℚ` of positive
Mordell–Weil rank supplies one — `E(ℚ̄)` is divisible with infinite rank,
so `addOrderOf` really is `0` there.  Hence `Gamma1Datum 0 SpecQ` is
INHABITED and this statement is true at `N = 0` as well.

The hypothesis is kept because every call site already has it and
dropping it would change the signature for no gain; it is
underscore-prefixed so that the emptiness is mechanically visible.
**Consequence for a sibling:** the docstring of `exists_x1Compactification`
asserts that "at `N = 0` the problem is empty over a nonempty base,
exactly as `isEmpty_of_gamma0Datum_zero` records on the `Γ₀` side".  That
is false for the same reason; that leaf has its own owner, and its
`hN : 4 ≤ N` makes the point moot for its own statement, but the
justification should be corrected there.

**Stated over a point of `E.toAffine.Point` — the curve over `ℚ` itself —
rather than over a Galois-fixed point of `(E⁄ℚ̄).Point`**, deliberately,
and this is the one place the interface differs from its `Γ₀` sibling.
The `Γ₀` bridge must take a geometric point because a Galois-stable
cyclic SUBGROUP need not be generated by a rational point (that is the
whole difference between `X_0` and `X_1`).  The `Γ₁` bridge has no such
need, and taking the rational point directly moves the base-change
bookkeeping — which `TorsionCard.smul_some_eq_zero_iff` would otherwise
have to be run over `ℚ̄` — out of every call site and into this single
proof, where it belongs. -/
theorem nonempty_gamma1Datum_of_ratPoint (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} (_hN : N ≠ 0) (P : E.toAffine.Point) (hP : addOrderOf P = N) :
    Nonempty (Gamma1Datum N SpecQ) := by
  classical
  obtain ⟨A, f, ab, hdim, e, he⟩ := exists_ellipticScheme_of_weierstrass E
  letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
  set φ : ℚ →ₐ[ℚ] AlgebraicClosure ℚ := Algebra.ofId ℚ (AlgebraicClosure ℚ) with hφ
  set Pbar := WeierstrassCurve.Affine.Point.map (W' := E) φ P with hPbar
  -- the base change of `P` to `ℚ̄` has the same order, `Point.map` being injective
  have hordbar : addOrderOf Pbar = N := by
    rw [hPbar, addOrderOf_injective (WeierstrassCurve.Affine.Point.map (W' := E) φ)
      (WeierstrassCurve.Affine.Point.map_injective _) P]
    exact hP
  -- and is `Γ_ℚ`-INVARIANT, because `σ ∘ (ℚ ↪ ℚ̄) = (ℚ ↪ ℚ̄)`
  have hgal : ∀ σ : Field.absoluteGaloisGroup ℚ,
      WeierstrassCurve.Affine.Point.map (W' := E)
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pbar = Pbar := by
    intro σ
    have hcomp : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.comp φ = φ :=
      Subsingleton.elim _ _
    calc WeierstrassCurve.Affine.Point.map (W' := E)
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pbar
        = WeierstrassCurve.Affine.Point.map (W' := E)
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.comp φ) P :=
          WeierstrassCurve.Affine.Point.map_map (W' := E) _ _ P
      _ = Pbar := by rw [hcomp]; exact hPbar.symm
  -- transport both along the equivariant identification of the geometric fibre
  have hord : letI := ab.addCommGroup (specAlgClos ℚ ≫ 𝟙 SpecQ)
      addOrderOf (e Pbar) = N := by
    rw [AddEquiv.addOrderOf_eq]
    exact hordbar
  have hinv : ∀ σ : Field.absoluteGaloisGroup ℚ,
      ab.galSMul (𝟙 SpecQ) σ (e Pbar) = e Pbar := by
    intro σ
    rw [← he σ Pbar, hgal σ]
  obtain ⟨pt⟩ := exists_pointOfExactOrder_of_geomPt ab _ hord hinv
  exact ⟨{ E := A, f := f, ab := ab, relativeDimensionOne := hdim, pt := pt }⟩

/-! ### The consumption rule

The single theorem the level nodes of `FreyCurve/MazurTorsion.lean` call:
a rational point of order `N` on an elliptic curve over `ℚ` produces a
NON-CUSPIDAL rational point of `X_1(N)`.  This is the `Γ₁` analogue of
`false_of_stable_of_y0HasNoRationalPoint`, except that it *produces* a
point rather than deriving `False` — at level `25` the contradiction is
reached by counting against the cusps, not by an emptiness statement, so
the point itself is what the consumer needs. -/

/-- **A rational point of exact order `N` gives a non-cuspidal rational
point of `X_1(N)`** (PROVEN over `nonempty_gamma1Datum_of_ratPoint`).

The classifying map of the coarse space sends the `Γ₁(N)`-datum to a
rational point of `Y_1(N)`; pushing it forward along the open immersion
gives a rational point of `X_1(N)` which is, by the definition of
`IsCusp`, not a cusp.  All the content is in the two inputs; this is the
bookkeeping that joins them, and it is written here rather than at the
call site so that `MazurTorsion.lean` never has to mention
`IsCoarseModuliY1.classify`. -/
theorem exists_notCusp_of_ratPoint {N : ℕ} (hN : N ≠ 0) {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (P : E.toAffine.Point) (hP : addOrderOf P = N) :
    ∃ p : RelPoint strX (𝟙 SpecQ), ¬ h.IsCusp p := by
  obtain ⟨d⟩ := nonempty_gamma1Datum_of_ratPoint E hN P hP
  refine ⟨sectionAlong jY h.comm (h.coarse.classify (𝟙 SpecQ) d), ?_⟩
  exact fun hcusp => hcusp ⟨h.coarse.classify (𝟙 SpecQ) d, rfl⟩

/-! ### The genus of `X_1(N)`, computed

The `Γ₁` mirror of `X0.lean`'s `x0Genus` block, and it exists for the
same reason: the genus half of `HasRankZeroJacobian` is *arithmetic*, so
it can be PROVEN by `decide` from the classical formula rather than
asserted in a docstring.  What is left over — the bridge from the number
to the scheme — is a separate, honest leaf.

Two simplifications relative to the `Γ₀` case, both genuine: for `N ≥ 4`
the group `Γ₁(N)` is torsion-free, so `ν₂ = ν₃ = 0` and no elliptic-point
counts are needed; and `−I ∉ Γ₁(N)` for `N ≥ 3`, which is where the
factor `½` in the index comes from. -/

/-- **The index `μ₁(N) = [PSL₂(ℤ) : Γ̄₁(N)] = ½ N² ∏_{p ∣ N} (1 − 1/p²)`.**

Written as `½ (N / rad N)² ∏_{p ∣ N} (p² − 1)` so that the only `ℕ`
divisions are by `rad N = ∏_{p ∣ N} p`, which always divides `N`, and by
`2`, which is exact for `N ≥ 3` because `−I ∉ Γ₁(N)` there makes the
`PSL₂` index half the `SL₂` index `N² ∏ (1 − 1/p²)`.  The product is over
`N.divisors.filter Nat.Prime`, exactly the primes dividing `N` when
`N ≠ 0`.

`μ₁(25) = ½ · 5² · 24 = 300`, independently reproduced with PARI/GP. -/
def gammaOneIndex (N : ℕ) : ℕ :=
  (N / (N.divisors.filter Nat.Prime).prod id) ^ 2 *
    (N.divisors.filter Nat.Prime).prod (fun p => p ^ 2 - 1) / 2

/-- **The number of cusps of `X_1(N)`**, `ν_∞ = ½ Σ_{d ∣ N} φ(d) φ(N/d)`.

The sibling of `numRationalCuspsX1`, which counts only the `φ(N)/2` cusps
that are individually `ℚ`-rational.  The two genuinely differ, and by a
lot: `X_1(25)` has `28` cusps of which only `10` are rational (the other
`18` are the `0`-cusps, defined over `ℚ(ζ₂₅)⁺`, and their Galois
conjugates).  It is `ν_∞`, the total, that enters the genus formula —
`numRationalCuspsX1` would give the wrong answer.

`ν_∞(25) = ½(φ(1)φ(25) + φ(5)φ(5) + φ(25)φ(1)) = ½(20 + 16 + 20) = 28`,
independently reproduced with PARI/GP. -/
def numCuspsX1 (N : ℕ) : ℕ :=
  (∑ d ∈ N.divisors, d.totient * (N / d).totient) / 2

/-- **The genus of `X_1(N)`, by the classical formula**

`g = 1 + μ₁/12 − ν₂/4 − ν₃/3 − ν_∞/2`

(Diamond–Shurman, Theorem 3.1.1) with `ν₂ = ν₃ = 0`, cleared of
denominators and divided back: `(12 + μ₁ − 6ν_∞) / 12`.

**VALIDITY RANGE — this is `genus X_1(N)` exactly for `N ≥ 5`, and the
range is load-bearing rather than pedantic.**  `Γ₁(N)` is torsion-free
only for `N ≥ 4`, so the dropped `ν₂, ν₃` terms are genuinely zero only
there, and `−I ∉ Γ₁(N)` needs `N ≥ 3`.  Outside the range the definition
still evaluates, and it evaluates WRONG in a direction that matters:

* `x1Genus 0 = x1Genus 1 = 1`, while `X_1(1) = ℙ¹` has genus `0` and a
  TRIVIAL Jacobian.

That is why `hasNoFibreAffineLine_of_one_le_x1Genus` below — and
`hasNonconstantAbelianMap_of_one_le_x1Genus` and
`not_isIso_jacobian_of_one_le_x1Genus` proven over it — carry `5 ≤ N`:
without it the leaf would be FALSE at `N = 1`, since `1 ≤ x1Genus 1`
holds while `X_1(1) = ℙ¹` contains `𝔸¹` in its one fibre, receives only
constant maps to abelian varieties, and has `¬ IsIso jstr` fail.  (The
`Γ₀` analogue of this note was NOT propagated to
`hasNoFibreAffineLine_of_one_le_x0Genus`, which carries no `hN` and is
exposed at `x0Genus 0 = 1`; the `Γ₁` chain is guarded throughout.)
Inside the range the
definition is faithful; `x1Genus N` for `5 ≤ N ≤ 30` reproduces the
classical table `0,0,0,0,0,0,1,0,2,1,1,2,5,2,7,3,5,6,12,5,12,10,13,10,22,9`
(PARI/GP), with the first positive value at `N = 11` and `x1Genus 25 = 12`.

**THE `Γ₀` SIDE HAS THE SAME TRAP AND NOW CARRIES THE SAME NOTE**
(2026-07-28).  `x0Genus 0 = 1` as well (`decide`), so `1 ≤ x0Genus N`
and `x0Genus N = 1` are both satisfiable at `N = 0`; only `N = 1`
differs, `x0Genus 1 = 0` there against `x1Genus 1 = 1` here.  This note
was not propagated across for a long time and one `Γ₀` consumer was
FALSE at `N = 0` because of it, so read `x0Genus`'s VALIDITY RANGE note
in `ModularCurve/X0.lean` alongside this one — it records the full sweep
of every `x0Genus`-in-hypothesis site and which plug each one uses.

**What this is and is not.**  `x1Genus` is a purely arithmetic,
computable function of `N`, evaluated by `decide` in
`x1Genus_twentyFive`.  It is NOT defined as the genus of the scheme `X`:
no genus of a scheme, and no Riemann–Roch, exists at this pin.  The
bridge from this number to the geometry of `X` is
`not_birationalOver_affineLine_of_one_le_x1Genus_algClosed`, and that is
the sorry node.  (`hasNonconstantAbelianMap_of_one_le_x1Genus` was that
node until 2026-07-28, then `hasNoFibreAffineLine_of_one_le_x1Genus` was,
then `exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` was, and all
three are now PROVEN over it — the bridge moved down three levels in three
days.  Since 2026-07-30 the bridge is stated over an ALGEBRAICALLY CLOSED
field, which is all its consumer needs and is where the genus argument is
free of arithmetic.)
Exactly the split `X0.lean` makes between `x0Genus` and
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus`. -/
def x1Genus (N : ℕ) : ℤ :=
  (12 + (gammaOneIndex N : ℤ) - 6 * numCuspsX1 N) / 12

/-- **`genus X_1(25) = 12`** (PROVEN, by computation).

`decide` evaluates the classical formula — index, cusps and all — from
`N = 25` alone: `μ₁(25) = 300`, `ν_∞(25) = 28`, so
`(12 + 300 − 168)/12 = 12`.  No table lookup and no assertion.

This is the number the module docstring quotes, and it is now a theorem
rather than prose.  It is also the dimension of `S_2(Γ_1(25))`, which
PARI/GP confirms independently: summing `dim S_2(25, χ)` over all `20`
Dirichlet characters mod `25` gives `12`, distributed over the eight even
characters as `2, 1, 2, 1, 1, 2, 1, 2`. -/
theorem x1Genus_twentyFive : x1Genus 25 = 12 := by decide

/-- **`genus X_1(25) ≥ 1`** (PROVEN, from the computed value).

The genus half of `HasRankZeroJacobian` at level `25`, and it is CLOSED:
this is what supplies `not_isIso_jacobian_of_one_le_x1Genus` with its
hypothesis in `hasRankZeroJacobian_x1TwentyFive`.  Genus `0` would make
that node FALSE — see `HasRankZeroJacobian` in `X0.lean`, where `X_0(1) =
ℙ¹` has trivial Jacobian and infinitely many rational points — so this is
exactly the condition that rules that out.  `12 ≥ 1` is generous. -/
theorem one_le_x1Genus_twentyFive : 1 ≤ x1Genus 25 := by
  rw [x1Genus_twentyFive]; decide

/-! ### Level `25`, packaged for `FreyCurve/MazurTorsion.lean` -/

/-- **The Jacobian of a smooth proper geometrically connected curve over
`ℚ` with a rational point exists** (PROVEN 2026-07-27, over `X0.lean`'s
two relative-Picard leaves) — LEVEL-FREE, and MODULI-FREE: no `N`, no
`IsX1Compactification`, no `IsX0Compactification`.

TRUE and classical: such an `X` has an Albanese — equivalently `Pic⁰` —
which is an abelian variety over `ℚ`, and the Abel–Jacobi map based at
`o` is initial among maps to abelian varieties killing `o`.  That is
exactly `IsJacobianOf`.

All three geometric hypotheses are load-bearing: without properness and
smoothness of relative dimension `1` there is no abelian Albanese, and
without geometric connectedness `Pic⁰` is not connected.

**HOW IT IS PROVEN, and what that retires.**  `X0.lean` now carries the
same statement cut into its two classical halves, both of them equally
level-free and both taking exactly the three geometric hypotheses of this
theorem:

* `exists_relPicZeroOf` — *representability*: `Pic⁰_{X/ℚ}` is an abelian
  scheme (Grothendieck, FGA 232; BLR 8.2/1 and 9.4/4);
* `isJacobianOf_of_isRelPicZeroOf` — *autoduality*: a representing object
  for `Pic⁰` is the Albanese, i.e. its Abel–Jacobi map is initial among
  pointed maps to abelian schemes.

Composing them is the whole proof, so this theorem is now a genuine
*wrapper* rather than a duplicate frontier node, and all of the weight it
used to carry sits in those two leaves — which the `Γ₀` side needs
anyway.

**The `Γ₀` sibling is ALREADY CLOSED, and not by this theorem.**  An
earlier version of this docstring recorded that `exists_jacobianOf_x0`
would be retired by

    exists_jacobianOf_x0 N h o = exists_jacobianOf_curve h.isProper h.smooth h.connected o

since it takes an `IsX0Compactification N strX strY j` and uses it *only*
through `h.isProper`, `h.smooth` and `h.connected`.  That reading was
right about the dependency and is now moot: `exists_jacobianOf_x0` was
itself proven on 2026-07-27 over the very same two leaves, directly.  It
could not have been routed through here in any case — `X1.lean` imports
`X0.lean`, not the other way round — so the shared factoring had to live
on the `Γ₀` side, and it does.

FAITHFULNESS AUDIT (carried over verbatim from `exists_jacobianOf_x0`,
where both checks were run on 2026-07-27 and both passed; nothing in the
generalisation touches either argument).

*Not vacuous.*  The obvious junk witness is the trivial abelian scheme
`J = Spec ℚ`, `jstr = 𝟙`, for which `RelPoint jstr g` is a singleton.  It
does **not** discharge the leaf: `universal` would then force every
natural pointed `c : X(−) ⟶ A(−)` to be constant, which fails for any
curve of positive genus — `X_1(25)` among them.

*The `∃!` in `IsJacobianOf.universal` is not too strong.*  `u` is asked to
be a bare morphism of `ℚ`-schemes, not a homomorphism, and for `g ≥ 2`
the image of `X` in `J` is nowhere dense; uniqueness nevertheless holds by
rigidity — any morphism of abelian varieties over a field is a
homomorphism followed by a translation, and one vanishing on `aj(X)`
kills the subgroup `aj(X)` generates, which is all of `J`.  A prover must
not weaken `∃!` to `∃`.

**THE RETIRED IRREDUCIBILITY VERDICT, kept because how it fell is the
lesson.**  This docstring used to close with "IRREDUCIBLE at this pin",
having searched — as `exists_jacobianOf_x0`'s audit did — *cuts along the
universal property*, all of which really do fail: the "existence plus
initiality" split is discharged by the trivial `J = Spec ℚ`, and the
"`aj` generates `J`" split is UNSOUND, because points of `J` are sums of
differences of points of `X` only fppf-locally and never as a functor.
The verdict named its own way out and then dismissed it — the honest cut
is *representability of `Pic⁰`* plus *autoduality*, gated on a relative
Picard functor "which exists in none of `Mathlib`, `~/cs/FLT` or this
project".  The axis it did not search was not another universal property
but the **infrastructure** axis, where a theory has only to be STATED for
the cut to become available.  That functor is now written
(`ModularCurve/RelativePicard.lean`: `modTensor`, `IsInvertibleSheaf`,
`RelPicEquiv`, `IsRelPicZeroOf`), so the verdict is retired.  Its own
refuting check is the one that now fails for it:
`grep -rn "PicardFunctor\|Pic⁰\|Albanese" Fermat/`. -/
theorem exists_jacobianOf_curve {X : Scheme.{0}} {strX : X ⟶ SpecQ}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 SpecQ)) :
    ∃ (J : Scheme.{0}) (jstr : J ⟶ SpecQ) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsJacobianOf strX ab o) := by
  obtain ⟨J, jstr, ab, ⟨P⟩⟩ := exists_relPicZeroOf hproper hcurve hconn o
  exact ⟨J, jstr, ab, isJacobianOf_of_isRelPicZeroOf hproper hcurve hconn P⟩

/-! ### Kolyvagin–Logachev, stated ONCE for `Γ₀` and `Γ₁` together

`isTorsion_jacobian_x1TwentyFive` below is the `Γ₁` sibling of `X0.lean`'s
`isTorsion_jacobian_of_lFunction_ne_zero`, and the obvious route to it is
to write a SECOND Kolyvagin–Logachev, for `Γ₁`.  Making that unnecessary
is the whole point of this subsection.

The two statements differ in exactly two places — which congruence
subgroup the weight-two forms live on, and which moduli problem pins the
curve — so they are ONE theorem quantified over a two-element datum,
`ModularLevelShape`.
`isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` is that theorem:
the `Γ₁(25)` statement is its instance at `.gamma1` with `N = 25`, and
`X0.lean`'s leaf is its instance at `.gamma0`.  **The development carries
ONE Kolyvagin–Logachev sorry, not two**, and the same holds for Hecke's
analytic continuation.

**The nebentypus is what makes the abstraction non-trivial**, and getting
it wrong would have made the `Γ₁` statement FALSE.  On `Γ₀(N)` the Hecke
recursion at `p ∤ N` reads `a_{np} + p·a_{n/p} = a_p a_n`; on `Γ₁(N)` it
reads `a_{np} + χ(p)·p·a_{n/p} = a_p a_n` with `χ` the nebentypus, and
`S_2(Γ_1(25))` is a sum over EIGHT characters mod `25`, six of them
non-trivial with non-trivial contribution (see the reconnaissance on
`lFunction_apply_one_ne_zero_x1TwentyFive`).  Had `IsWeightTwoEigenformOn`
been written with the `Γ₀` recursion, essentially no `Γ₁(25)` eigenform
would satisfy it, the analytic hypothesis `hL` would be VACUOUSLY
satisfiable at `.gamma1 25`, and the leaf would assert that `J_1(25)(ℚ)`
is torsion on no arithmetic input at all — a false leaf of exactly the
kind the doctrine warns is worse than an open one.  So
`IsWeightTwoEigenformOn` carries a `DirichletCharacter ℂ N`, and
`ModularLevelShape.IsNebentypus` records which characters each shape
admits: only the trivial one for `Γ₀`, all of them for `Γ₁`.  That last
clause is what keeps the `.gamma0` instance no STRONGER than `X0.lean`'s
leaf, so the subsumption below is real and not an aspiration.

**THE SUBSUMPTION RUNS THE OTHER WAY — REVERSED 2026-07-27, and the
reversal is the whole content of this note.**

An earlier version of this docstring recorded the two shape-free
statements below as SUBSUMING `X0.lean`'s
`isTorsion_jacobian_of_lFunction_ne_zero` and
`WeightTwoEigenform.lean`'s
`exists_isLFunctionOf_of_isWeightTwoEigenform`, and prescribed the
disposal: relocate this subsection into `X0.lean` and replace those two
bodies by an application of the shape-free leaf.  **Carrying that out
would have been a REGRESSION**, and the compiler is what says so.

Both of those `Γ₀` statements are **PROVEN**, and were already proven
when this subsection was written — 22 and 9 minutes earlier respectively,
on branches this one did not have.  `exists_isLFunctionOf_of_isWeightTwoEigenform`
is an assembly over four analytic leaves (`cuspFEPair`,
`isStrongFEPair_cuspFEPair`, `mellin_axisRestrict`, and the summability
input); `isTorsion_jacobian_of_lFunction_ne_zero` is an assembly over
`exists_heckeIsotypicDecomposition` (Eichler–Shimura),
`isTorsion_factor_of_heckeIsotypic` (Kolyvagin–Logachev) and the PROVEN
`isTorsion_of_finite_jointKer` (isogeny invariance).  Replacing either
body by an application of a still-open shape-free `sorry` would have
thrown away a finer decomposition and re-opened a closed node — the sorry
count would not even have improved, since the shape-free statements were
themselves the sorries.

So the direction is inverted: **the shape-free statements CONSUME the
`Γ₀` theorems** rather than subsuming them.  Each is proven at `.gamma0`
by citation and left open only at `.gamma1`, so what the development
carries is the `Γ₀` theorems (proven, finely cut) plus exactly one
genuinely `Γ₁` Hecke leaf and one genuinely `Γ₁` Kolyvagin leaf.  That is
the same "no duplicated theory" outcome the original cut wanted, obtained
without touching `X0.lean` at all — which also disposes of the
relocation: nothing needs to move, because `X1.lean` `public import`s
`X0.lean` and citation runs downstream.

Two hypotheses had to be added to make the `.gamma0` citation possible,
and both are genuine faithfulness repairs rather than bookkeeping:

```
theorem isWeightTwoEigenformOn_gamma0_iff (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) :
    IsWeightTwoEigenformOn (Gamma0GL N) N 1 f a ↔ IsWeightTwoEigenform N f a := by
  have key : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (1 : DirichletCharacter ℂ N) (p : ZMod N) = 1 :=
    fun p hp hpN => MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hp).2 hpN)
  constructor
  · intro h
    exact ⟨h.qExpansion, h.qExpansionSummable, h.zero, h.one, fun p hp hpN n hn => by
      have := h.hecke p hp hpN n hn; rwa [key p hp hpN, one_mul] at this, h.atkin⟩
  · intro h
    exact ⟨h.qExpansion, h.qExpansionSummable, h.zero, h.one, fun p hp hpN n hn => by
      rw [key p hp hpN, one_mul]; exact h.hecke p hp hpN n hn, h.atkin⟩
```

**The `qExpansionSummable` entries in those two anonymous constructors
were ADDED on 2026-07-27 and the snippet was BROKEN without them** — a
worked example that no longer compiled, of exactly the shape the doctrine
warns about.  `IsWeightTwoEigenform` gained a `qExpansionSummable` field
the same day this subsection was written (see its `SOUNDNESS AUDIT`), and
this file's copy of the structure did not follow; the `→` direction of the
bridge was therefore not merely unverified but UNPROVABLE, because nothing
on the left produced the summability the right demands.  Adding the field
to `IsWeightTwoEigenformOn` restores the field-for-field match, which is
what makes "on the nose" true rather than aspirational.
-/

section KolyvaginLogachev

open _root_.Matrix
open scoped MatrixGroups

/-- **`Γ₁(N)`, viewed inside `GL(2, ℝ)`**, which is where mathlib's
`CuspForm` wants its group.

Verbatim the recipe of `X0.lean`'s `Gamma0GL`: the coercion is
`Subgroup.map (mapGL ℝ)` and is injective, so nothing is lost.  `Γ₁(N)`
rather than `Γ₀(N)` is what the level-`25` argument needs, because
`X_1(25)` is the moduli space of PAIRS `(E, P)` with `P` of exact order
`25` — see this module's opening docstring for why the `Γ₀` route is not
merely unavailable at `N = 25` but refuted. -/
abbrev Gamma1GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- **`a` is the `q`-expansion of the normalized Hecke eigenform `f` in
`S_2(G)` with nebentypus `χ`**, for an arbitrary congruence subgroup
`G ≤ GL(2, ℝ)` of level `N`.

This is `X0.lean`'s `IsWeightTwoEigenform` with two changes, and both are
forced.

* **`G` is a parameter**, so the interface serves `Γ₀(N)` and `Γ₁(N)`
  alike.  That is what lets Kolyvagin–Logachev be stated once.
* **A nebentypus `χ : DirichletCharacter ℂ N` is carried**, because the
  `T_p`-recursion on `Γ₁(N)` is `a_{np} + χ(p)·p·a_{n/p} = a_p a_n`.
  Dropping `χ` (equivalently, hardwiring it to `1`) is not a
  simplification but a falsification: it would make this predicate
  essentially uninhabited on `Γ₁(25)` and every hypothesis quantified
  over it vacuous.  See the subsection docstring.

`f` itself is carried, exactly as in `X0.lean`, and for the same reason:
an interface on bare sequences `a : ℕ → ℂ` is junk-satisfiable (take
`a p = 0` at every prime and extend by the recursions), which makes a
universally quantified leaf false and a hypothesis vacuous.  `qExpansion`
is what rules that out and may not be dropped.

**SOUNDNESS REPAIR (2026-07-27): `qExpansion` ALONE IS NOT ENOUGH, and
its absence made `lFunction_apply_one_ne_zero_x1TwentyFive` FALSE AS
STATED.**  This structure was written as a copy of `X0.lean`'s
`IsWeightTwoEigenform` *before* that structure gained its
`qExpansionSummable` field, and the copy was never updated.  The junk
witness is exactly the one recorded under `SOUNDNESS AUDIT` in
`ModularCurve/WeightTwoEigenform.lean`'s module docstring, and it
transfers verbatim because nothing in it is `Γ₀`-specific: `tsum` of a
NON-summable family is `0`, so

> `f := 0`, together with the multiplicative `a` with `a p := 2 ^ (p ^ 2)`
> at every prime `p ∤ N` (extended over prime powers by the very
> recursions below, which constrain the SIZE of `a p` not at all),

satisfies `qExpansion` with both sides `0`, satisfies `zero`, `one`,
`hecke` and `atkin` by construction, and is the `q`-expansion of no
modular form whatsoever.  See the `FALSITY AUDIT` on
`lFunction_apply_one_ne_zero_x1TwentyFive` below for what that junk then
does to the `L`-value leaf, and to the analytic hypothesis `hL` of
`isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape`.

Adding a field only STRENGTHENS the predicate, so every occurrence in
this file — all three take it as a hypothesis and none constructs one —
is unaffected except that it becomes easier to discharge.

At `G = Gamma0GL N` and `χ = 1` this is `IsWeightTwoEigenform N f a` on
the nose; the machine-checked bridge is recorded in the subsection
docstring, and **the field is what keeps that bridge provable in the
`→` direction**, since the `Γ₀` structure demands summability. -/
structure IsWeightTwoEigenformOn (G : Subgroup (GL (Fin 2) ℝ)) (N : ℕ)
    (χ : DirichletCharacter ℂ N) (f : CuspForm G 2) (a : ℕ → ℂ) : Prop where
  /-- `a` is the Fourier expansion of `f`; the constant term is `0`
  because `f` is a cusp form, so the sum starts at `n = 1`. -/
  qExpansion : ∀ τ : UpperHalfPlane,
    f τ = ∑' n : ℕ, a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))
  /-- The `q`-expansion CONVERGES.  Without this field the previous one
  is junk-satisfiable through the junk value of `tsum`, and the interface
  is unsound — see the `SOUNDNESS REPAIR` heading above, and the
  identical field on `X0.lean`'s `IsWeightTwoEigenform`. -/
  qExpansionSummable : ∀ τ : UpperHalfPlane,
    Summable fun n : ℕ => a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))
  /-- The `0`-th coefficient is `0`; `f` is a cusp form. -/
  zero : a 0 = 0
  /-- `f` is normalized. -/
  one : a 1 = 1
  /-- `f` is a `T_p`-eigenform for every prime `p ∤ N`, with eigenvalue
  `a p`.  For weight two and nebentypus `χ`, `T_p` acts on
  `q`-expansions by `(T_p f)_n = a_{np} + χ(p)·p·a_{n/p}`. -/
  hecke : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, 0 < n →
    a (n * p) + χ (p : ZMod N) * (p : ℂ) * (if p ∣ n then a (n / p) else 0) = a p * a n
  /-- `f` is a `U_p`-eigenform for every prime `p ∣ N`, with eigenvalue
  `a p`.  `U_p` acts by `(U_p f)_n = a_{np}`, with no nebentypus factor:
  `χ(p) = 0` for `p ∣ N`. -/
  atkin : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, 0 < n → a (n * p) = a p * a n

/-- **Which of the two level structures a modular curve carries**, `Γ₀`
or `Γ₁`.

Deliberately a two-element `inductive` and not an abstract "congruence
subgroup with a moduli problem": the moduli problem is what pins the
curve, and pinning it by an unconstrained `Prop`-valued parameter would
make the Kolyvagin–Logachev leaf FALSE (instantiate the parameter at
`fun _ => True` and at a `G` with `S_2(G) = 0`, and the analytic
hypothesis becomes vacuous while the conclusion still asserts rank `0`
for an arbitrary curve).  Enumerating the shapes this development
actually has keeps every branch pinned by a real moduli problem, and a
third shape can be added the day a third moduli tower is written. -/
inductive ModularLevelShape where
  /-- the `Γ₀(N)`-problem: a cyclic subgroup of order `N` -/
  | gamma0 : ModularLevelShape
  /-- the `Γ₁(N)`-problem: a point of exact order `N` -/
  | gamma1 : ModularLevelShape

/-- **The congruence subgroup of level `N` of the given shape**, inside
`GL(2, ℝ)` where `CuspForm` wants it. -/
def ModularLevelShape.group : ModularLevelShape → ℕ → Subgroup (GL (Fin 2) ℝ)
  | .gamma0 => Gamma0GL
  | .gamma1 => Gamma1GL

/-- **`strX` is the compactified coarse moduli space of the moduli
problem of level `N` and the given shape** — `X_0(N)` or `X_1(N)`.

Wrapped in `Nonempty` because `IsX0Compactification` and
`IsX1Compactification` carry the classifying-map DATA of their coarse
moduli spaces and so live in `Type`, while a hypothesis of a theorem
about rational points wants a `Prop`.  No consumer below inspects the
datum. -/
def ModularLevelShape.IsCompactification (S : ModularLevelShape) (N : ℕ) {X Y : Scheme.{0}}
    (strX : X ⟶ SpecQ) (strY : Y ⟶ SpecQ) (jY : Y ⟶ X) : Prop :=
  match S with
  | .gamma0 => Nonempty (IsX0Compactification N strX strY jY)
  | .gamma1 => Nonempty (IsX1Compactification N strX strY jY)

/-- **Which nebentypus characters occur on forms of the given shape.**

`Γ₀(N)` contains `-I` and every `γ` acts trivially on the level
structure, so a form on `Γ₀(N)` has trivial nebentypus; on `Γ₁(N)` the
quotient `Γ₀(N)/Γ₁(N) ≅ (ℤ/N)ˣ` acts, and every character mod `N` occurs.

This field is the reason the `.gamma0` instance of the
Kolyvagin–Logachev leaf below is exactly as strong as `X0.lean`'s leaf
and no stronger: without it, `hL` would demand `L(f, 1) ≠ 0` for
`χ`-twisted "eigenforms" on `Γ₀(N)` as well, an obligation nothing in
`X0.lean` discharges. -/
def ModularLevelShape.IsNebentypus : (S : ModularLevelShape) → (N : ℕ) →
    DirichletCharacter ℂ N → Prop
  | .gamma0 => fun _ χ => χ = 1
  | .gamma1 => fun _ _ => True

/-- **At `Γ₀(N)` with trivial nebentypus this is exactly
`IsWeightTwoEigenform`** (PROVEN; one `MulChar.one_apply` rewrite in each
direction).

The hypothesis `¬ p ∣ N` on a prime `p` is exactly what makes `p` a unit
mod `N`, so the nebentypus factor `χ(p)` in this module's `hecke` field
is `1` and the recursion collapses to `X0.lean`'s.  Every other field is
shared verbatim, `qExpansionSummable` included — that field was added to
`IsWeightTwoEigenformOn` precisely so that this really is an `Iff` and
not merely an implication.

This is the bridge that makes both shape-free statements below provable
at `.gamma0` by citing the `Γ₀` theorems, which is what keeps the
development free of a second copy of Hecke's continuation and of
Kolyvagin–Logachev. -/
theorem isWeightTwoEigenformOn_gamma0_iff (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) :
    IsWeightTwoEigenformOn (Gamma0GL N) N 1 f a ↔ IsWeightTwoEigenform N f a := by
  have key : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (1 : DirichletCharacter ℂ N) (p : ZMod N) = 1 :=
    fun p hp hpN => MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hp).2 hpN)
  constructor
  · intro h
    exact ⟨h.qExpansion, h.qExpansionSummable, h.zero, h.one, fun p hp hpN n hn => by
      have := h.hecke p hp hpN n hn; rwa [key p hp hpN, one_mul] at this, h.atkin⟩
  · intro h
    exact ⟨h.qExpansion, h.qExpansionSummable, h.zero, h.one, fun p hp hpN n hn => by
      rw [key p hp hpN, one_mul]; exact h.hecke p hp hpN n hn, h.atkin⟩

/-!
#### Hecke's continuation, cut ONCE for every group between `Γ₁(N)` and `Γ₀(N)`

`WeightTwoEigenform.lean` cuts Hecke's continuation for `Γ₀(N)` into four
analytic leaves — `exists_frickeInvolution`, `isBigO_atTop_axisRestrict`,
`locallyIntegrableOn_axisRestrict`, `isBigO_atTop_coeff` — and PROVES the
assembly `exists_isLFunctionOf_of_isWeightTwoEigenform` over them, using
mathlib's group-free packaging of the analysis (`WeakFEPair`,
`IsStrongFEPair.differentiable_Λ`, `hasSum_mellin`).

Those four leaves are typed at `CuspForm (Gamma0GL N) 2`, and **a cusp
form on `Γ₁(N)` is not a cusp form on `Γ₀(N)`** — the whole point of the
nebentypus is that `Γ₀(N)/Γ₁(N) ≅ (ℤ/N)ˣ` acts by `χ` rather than
trivially.  So the `Γ₁` half of
`exists_isLFunctionOf_of_isWeightTwoEigenformOn` cannot cite them, and it
is not a corollary of the `Γ₀` theorem by any route: the two statements
are parallel, not nested.

What IS shared is the *argument*, and it is shared exactly:

> restrict `f` to the rescaled imaginary axis `y ↦ f(iy/√N)`, Mellin
> transform it, recognise the transform as `Γ(s) (2π/√N)^{-s} L(f, s)` by
> termwise integration, and get the continuation from the Fricke
> involution `W_N`, which converts the behaviour at `y → 0` into the
> behaviour at `y → ∞`.

Not one step of that mentions which congruence subgroup `f` lives on.
So this subsection restates the four leaves ONCE, for an arbitrary
`G` with `Γ₁(N) ≤ G ≤ Γ₀(N)`, reproves the assembly over them, and
obtains the `Γ₁` half by citation at `G = Γ₁(N)`.  The four leaves in
`WeightTwoEigenform.lean` are the `G = Γ₀(N)` instances of the four
below.

**All four are PROVEN, 2026-07-28** — the `Γ₀` quartet there landed
first, and this quartet was proven by generalizing its proofs rather
than by rewriting them.  What is genuinely new here is exactly one
lemma, `frickeMatrix_conj_mem_of_le`: `frickeMatrix` and its slash
machinery are group-free and reused verbatim, and the analysis
(`CuspFormClass.exp_decay_atImInfty`, `CuspFormClass.qExpansion_isBigO`)
is mathlib's, indexed by `G.strictPeriods` / `G.strictWidthInfty` /
`G.IsArithmetic`, all three of which are supplied here for the abstract
`G` by `strictPeriodsOn`, `strictWidthInftyOn` and `isArithmeticOn`.

**The residual duplication is now removable in exactly one direction,
and the module order blocks it.**  With this quartet proven, the four
`Γ₀` statements in `WeightTwoEigenform.lean` are its `G = Γ₀(N)`
instances and could be one-line citations — but `X1.lean` imports
`WeightTwoEigenform.lean`, not the other way round, so discharging them
that way would require hoisting this subsection upstream.  That is pure
cleanup with both sides green, not a frontier item; it is recorded here
so that nobody re-derives it as an open question.

**FAITHFULNESS AUDIT — both bounds on `G` are load-bearing.**

*Why `Γ₁(N) ≤ G` may not be dropped.*  The argument needs `f` to be
`T`-periodic (that is what gives it a `q`-expansion, hence exponential
decay at `i∞` and a Dirichlet series at all), and it needs `G` to be
normalised by `W_N = ![![0, -1], ![N, 0]]`.  `Γ(N)` is a counterexample
to the second: conjugation sends `![![a, b], ![c, d]]` to
`![![d, -c/N], ![-bN, a]]`, and `c ≡ 0 [N]` does NOT give `c/N ≡ 0 [N]`,
so `W_N` does not normalise `Γ(N)` and `f ∣ W_N` need not lie in
`S₂(Γ(N))`.

*Why `G ≤ Γ₀(N)` may not be dropped either*, and this one has an explicit
witness.  With only the lower bound, `G := Γ₀(M)` for a PROPER divisor
`M ∣ N` is admissible (`Γ₁(N) ≤ Γ₀(M)`, since `N ∣ c` gives `M ∣ c`), and
`exists_frickeInvolutionOn` is then FALSE.  Take `N = 22`, `M = 11`, and
`f` the newform of level `11`, spanning `S₂(Γ₀(11))`.  Writing
`z = iy/√22` and using the level-`11` Fricke identity
`f(-1/(11w)) = ε · 11 w² f(w)` at `w = 2z`,

> `f(i/(√22 y)) = ε · 11 · (2z)² f(2z) = -2ε y² f(2z)`,

so the required partner would have to satisfy `g(τ) = 2ε f(2τ)` on the
imaginary axis, hence everywhere by the identity theorem.  But `f(2τ)` is
an OLDFORM of level `22` and is not in `S₂(Γ₀(11))` — comparing
`q`-expansions, `f(2τ) = q² + …` is not a multiple of `f = q - 2q² + …`
in the one-dimensional space `S₂(Γ₀(11))`.  So no `g : CuspForm (Γ₀(11)) 2`
works, and the leaf without the upper bound is false.

*Why the two bounds together are the right hypothesis.*  A `G` with
`Γ₁(N) ≤ G ≤ Γ₀(N)` is exactly the preimage `Γ_H(N)` of a subgroup
`H ≤ (ℤ/N)ˣ` under `![![a, b], ![c, d]] ↦ d mod N`.  Conjugation by `W_N`
preserves `Γ₀(N)` and sends the class `d` to `d⁻¹`, so it preserves every
such preimage — `H` being a subgroup is precisely closure under
inversion.  Both `Γ₀(N)` (`H = (ℤ/N)ˣ`) and `Γ₁(N)` (`H = 1`) are of this
form, which is what makes ONE statement serve both layers.
-/

section HeckeOn

open Filter Asymptotics MeasureTheory

open scoped ModularForm

/-- **`Γ₁(N) ≤ Γ₀(N)` inside `GL(2, ℝ)`** (PROVEN) — mathlib's
`CongruenceSubgroup.Gamma1_in_Gamma0` pushed along `mapGL ℝ`, which is
the map both `Gamma1GL` and `Gamma0GL` are images under. -/
theorem gamma1GL_le_gamma0GL (N : ℕ) : Gamma1GL N ≤ Gamma0GL N := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := hx
  exact ⟨γ, CongruenceSubgroup.Gamma1_in_Gamma0 N hγ, rfl⟩

/-- `f` restricted to the rescaled imaginary axis: `y ↦ f (i y / √N)` for
`y > 0`, and `0` elsewhere — `WeightTwoEigenform.lean`'s `axisRestrict`
with the group left free.  The `√N` rescaling is what turns the level-`N`
Fricke involution `z ↦ -1/(Nz)` into the level-free inversion `y ↦ 1/y`
that `WeakFEPair` asks for; `axisPoint` is shared verbatim, since it does
not mention a group at all. -/
noncomputable def axisRestrictOn (G : Subgroup (GL (Fin 2) ℝ)) (N : ℕ)
    (f : CuspForm G 2) (y : ℝ) : ℂ :=
  if h : 0 < y ∧ N ≠ 0 then f (axisPoint N y h) else 0

lemma axisRestrictOn_of_pos {G : Subgroup (GL (Fin 2) ℝ)} {N : ℕ} (hN : N ≠ 0)
    (f : CuspForm G 2) {y : ℝ} (hy : 0 < y) :
    axisRestrictOn G N f y = f (axisPoint N y ⟨hy, hN⟩) := dif_pos ⟨hy, hN⟩

/-! #### What `Γ₁(N) ≤ G ≤ Γ₀(N)` buys, in mathlib's vocabulary

Three facts, and between them they carry three of the four leaves.  Each
is stated for the abstract `G` rather than for a named congruence
subgroup, which is the whole point of this subsection.
-/

/-- At level `N = 0` the axis restriction is identically `0`, because
`axisPoint` — and with it `axisRestrictOn` — is gated on `N ≠ 0`
(`Real.sqrt 0 = 0` would put the point on the real axis).  This is what
makes the two analytic leaves below true without a level hypothesis;
`WeightTwoEigenform.lean`'s `axisRestrict_zero_level` is the `Γ₀`
instance. -/
@[simp] lemma axisRestrictOn_zero_level (G : Subgroup (GL (Fin 2) ℝ)) (f : CuspForm G 2) :
    axisRestrictOn G 0 f = fun _ : ℝ => (0 : ℂ) := by
  funext y
  simp [axisRestrictOn]

/-- **`strictPeriods` is monotone** (PROVEN) — `x` is a strict period of
`𝒢` exactly when `![![1, x], ![0, 1]] ∈ 𝒢`, and that condition only gets
easier as `𝒢` grows. -/
lemma strictPeriods_mono {G G' : Subgroup (GL (Fin 2) ℝ)} (h : G ≤ G') :
    G.strictPeriods ≤ G'.strictPeriods := fun _ hx =>
  Subgroup.mem_strictPeriods_iff.mpr (h (Subgroup.mem_strictPeriods_iff.mp hx))

/-- **`1` is a strict period of every `G ⊇ Γ₁(N)`** (PROVEN) — the
translation `T = ![![1, 1], ![0, 1]]` lies in `Γ₁(N)` already, so it lies
in `G`.  This is the hypothesis mathlib's `q`-expansion API takes in
place of "the width of the cusp `∞` is `1`", and it is what lets
`CuspFormClass.exp_decay_atImInfty` and
`ModularFormClass.qExpansion_coeff_unique` be applied at `h = 1`.

Only the LOWER bound on `G` is used. -/
lemma one_mem_strictPeriodsOn (N : ℕ) {G : Subgroup (GL (Fin 2) ℝ)} (h1 : Gamma1GL N ≤ G) :
    (1 : ℝ) ∈ G.strictPeriods := by
  refine strictPeriods_mono h1 ?_
  rw [show (Gamma1GL N).strictPeriods = AddSubgroup.zmultiples (1 : ℝ) from
    CongruenceSubgroup.strictPeriods_Gamma1 N]
  exact AddSubgroup.mem_zmultiples 1

/-- **Every `G` between `Γ₁(N)` and `Γ₀(N)` has strict periods exactly
`ℤ`** (PROVEN) — a sandwich, since both ends have `zmultiples 1`. -/
lemma strictPeriodsOn (N : ℕ) {G : Subgroup (GL (Fin 2) ℝ)} (h1 : Gamma1GL N ≤ G)
    (h0 : G ≤ Gamma0GL N) : G.strictPeriods = AddSubgroup.zmultiples (1 : ℝ) := by
  have e0 : (Gamma0GL N).strictPeriods = AddSubgroup.zmultiples (1 : ℝ) :=
    CongruenceSubgroup.strictPeriods_Gamma0 N
  have e1 : (Gamma1GL N).strictPeriods = AddSubgroup.zmultiples (1 : ℝ) :=
    CongruenceSubgroup.strictPeriods_Gamma1 N
  exact le_antisymm (e0 ▸ strictPeriods_mono h0) (e1 ▸ strictPeriods_mono h1)

/-- **The cusp `∞` of such a `G` has strict width `1`** (PROVEN) — the
`strictWidthInfty` normalisation of the previous lemma, by mathlib's
`strictPeriods_eq_zmultiples_strictWidthInfty` and the fact that a
generator of `zmultiples 1` is `±1`.  This is the `h` that
`CuspFormClass.qExpansion_isBigO` indexes its coefficients by. -/
lemma strictWidthInftyOn (N : ℕ) {G : Subgroup (GL (Fin 2) ℝ)} (h1 : Gamma1GL N ≤ G)
    (h0 : G ≤ Gamma0GL N) : G.strictWidthInfty = 1 := by
  have hsp := strictPeriodsOn N h1 h0
  have : DiscreteTopology G.strictPeriods := by rw [hsp]; infer_instance
  rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, Eq.comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)] at hsp
  grind [Subgroup.strictWidthInfty_nonneg]

/-- **Every `G` between `Γ₁(N)` and `Γ₀(N)` is arithmetic**, for `N ≠ 0`
(PROVEN) — and **BOTH bounds are used**, which is worth stating plainly
because the `Γ₁(N) ≤ G` half alone does NOT give it: `G = ⊤` contains
`Γ₁(N)` and is not commensurable with `SL(2, ℤ)`.

The upper bound puts `G` inside the image of `SL(2, ℤ)`, so `G` is the
image of `Γ := G ∩ SL(2, ℤ)` (`Subgroup.map_comap_eq_self`); the lower
bound puts the finite-index `Γ₁(N)` inside `Γ`, so `Γ` has finite index
too, and `Subgroup.isArithmetic_iff_finiteIndex` converts.

This is what feeds `CuspFormClass.qExpansion_isBigO`, i.e. Hecke's
coefficient bound. -/
lemma isArithmeticOn (N : ℕ) [NeZero N] {G : Subgroup (GL (Fin 2) ℝ)} (h1 : Gamma1GL N ≤ G)
    (h0 : G ≤ Gamma0GL N) : G.IsArithmetic := by
  have hrange : G ≤ (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range :=
    h0.trans (Subgroup.map_le_range _ _)
  have hG : ((G.comap (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ) :
      Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = G := Subgroup.map_comap_eq_self hrange
  rw [← hG]
  refine Subgroup.isArithmetic_iff_finiteIndex.mpr ⟨fun hz => ?_⟩
  have hle : CongruenceSubgroup.Gamma1 N ≤
      G.comap (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ) :=
    fun γ hγ => h1 (Subgroup.mem_map_of_mem _ hγ)
  exact (CongruenceSubgroup.instFiniteIndexGamma1 (N := N)).index_ne_zero
    (Nat.eq_zero_of_zero_dvd (hz ▸ Subgroup.index_dvd_of_le hle))

/-! #### Restricting a cusp form to a smaller group

`CuspForm` is CONTRAVARIANT in its group in both of its conditions:
slash-invariance under a bigger group is a stronger demand, and — since
`IsCusp c 𝒢` asks only for SOME parabolic element of `𝒢` fixing `c` — the
cusp set grows with the group, so vanishing at the cusps of the bigger
group is stronger too.  Hence a `CuspForm G 2` restricts to a
`CuspForm G' 2` for any `G' ≤ G`, with the same underlying function.

This is what lets `isBigO_atTop_coeffOn` be stated with the lower bound
`Γ₁(N) ≤ G` ALONE: the leaf is proven for `G` between the two bounds and
then transported down to `G' = Γ₁(N)`, where both bounds hold trivially.
Without it the coefficient leaf would have to carry `G ≤ Γ₀(N)` as well —
see `isArithmeticOn`, whose proof genuinely needs the upper bound.
-/

/-- **A cusp of a subgroup is a cusp of the group** (PROVEN) —
`IsCusp c 𝒢 = ∃ g ∈ 𝒢, g.IsParabolic ∧ g • c = c`, and the witness
transports along the inclusion. -/
lemma isCusp_of_le {c : OnePoint ℝ} {G G' : Subgroup (GL (Fin 2) ℝ)} (h : G' ≤ G)
    (hc : IsCusp c G') : IsCusp c G := by
  obtain ⟨g, hg, hpar, hgc⟩ := hc
  exact ⟨g, h hg, hpar, hgc⟩

/-- **A cusp form on `G` is a cusp form on any subgroup `G' ≤ G`**, with
the same underlying function (PROVEN). -/
def restrictCuspForm {G G' : Subgroup (GL (Fin 2) ℝ)} (h : G' ≤ G) (f : CuspForm G 2) :
    CuspForm G' 2 where
  toFun := (f : UpperHalfPlane → ℂ)
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq (Γ := G) (k := 2) f γ (h hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (isCusp_of_le h hc)

@[simp] lemma coe_restrictCuspForm {G G' : Subgroup (GL (Fin 2) ℝ)} (h : G' ≤ G)
    (f : CuspForm G 2) :
    (restrictCuspForm h f : UpperHalfPlane → ℂ) = (f : UpperHalfPlane → ℂ) := rfl

/-- **Being a weight-two eigenform is inherited by restriction** (PROVEN)
— every field of `IsWeightTwoEigenformOn` is a statement about `f` AS A
FUNCTION and about `a`, and `restrictCuspForm` changes neither, so the
proof term is the six fields passed through unchanged. -/
lemma IsWeightTwoEigenformOn.restrict {N : ℕ} {G G' : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h : G' ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) :
    IsWeightTwoEigenformOn G' N χ (restrictCuspForm h f) a :=
  ⟨hf.qExpansion, hf.qExpansionSummable, hf.zero, hf.one, hf.hecke, hf.atkin⟩

/-! #### The Fricke involution normalises every intermediate `G`

`WeightTwoEigenform.lean` builds `W_N = ![![0, -1], ![N, 0]]` as an
element of `GL(2, ℝ)` (`frickeMatrix`) and proves it normalises `Γ₀(N)`.
That matrix is group-free and is reused verbatim; what has to be
redone is the normalisation, for the abstract `G`.

**The argument, and where each bound on `G` enters.**  Let `γ ∈ G` and
write `γ = ![![a, b], ![c, d]]` with `c = N c'` — the upper bound is what
gives `N ∣ c`.  Then the Γ₀-computation gives
`W γ W⁻¹ = δ := ![![d, -c'], ![-N b, a]]`, and the product

> `δ γ = ![![ad - N c'², db - c'd], ![N a (c' - b), ad - N b²]]`

is congruent mod `N` to `![![1, *], ![0, 1]]`, because `ad - bc = 1` with
`N ∣ c` forces `ad ≡ 1`.  So `δ γ ∈ Γ₁(N) ≤ G` — the lower bound — and
therefore `δ = (δ γ) γ⁻¹ ∈ G`.

Conceptually this is the classical statement that `W_N` acts on
`Γ₀(N)/Γ₁(N) ≅ (ℤ/N)ˣ` by `d ↦ d⁻¹`, so it preserves the preimage `Γ_H(N)`
of every SUBGROUP `H`; the computation above is that statement with the
group-theoretic bookkeeping replaced by one explicit product, which is
cheaper in Lean and needs no `Γ_H` classification.  Note it also shows
why `Γ(N)` — which is NOT of the form `Γ_H(N)` — is a genuine
counterexample to dropping the lower bound.
-/

/-- **`W_N` normalises every `G` with `Γ₁(N) ≤ G ≤ Γ₀(N)`** (PROVEN) —
see the subsection docstring for the computation.  The `Γ₀` instance is
`WeightTwoEigenform.lean`'s `frickeMatrix_conj_mem`.

Only this ONE inclusion is needed downstream — never the reverse
inclusion, and never the equality of subgroups — because both consumers
(`frickeSlashOn`'s slash-invariance and `isCusp_frickeMatrix_smul_of_le`)
push forward along `γ ↦ W_N γ W_N⁻¹`. -/
lemma frickeMatrix_conj_mem_of_le (N : ℕ) (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) {g : GL (Fin 2) ℝ} (hg : g ∈ G) :
    frickeMatrix N hN * g * (frickeMatrix N hN)⁻¹ ∈ G := by
  obtain ⟨γ, hγ, rfl⟩ := h0 hg
  obtain ⟨c', hc'⟩ : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  obtain ⟨δ, hδ⟩ : ∃ δ : SL(2, ℤ), (δ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -c';
        -((N : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1),
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] :=
    ⟨⟨_, by
      rw [Matrix.det_fin_two_of]
      linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'⟩, rfl⟩
  have hconj : frickeMatrix N hN * (Matrix.SpecialLinearGroup.mapGL ℝ γ) *
      (frickeMatrix N hN)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ δ := by
    rw [mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hδ, Matrix.mul_apply, Fin.sum_univ_two, hc'] <;> ring
  rw [hconj]
  have hmem : δ * γ ∈ CongruenceSubgroup.Gamma1 N := by
    have key1 : ∀ x k : ℤ, x - 1 = (N : ℤ) * k → ((x : ZMod N)) = 1 := by
      intro x k hx
      have h0 : ((x - 1 : ℤ) : ZMod N) = 0 := by rw [hx]; push_cast; simp
      push_cast at h0
      exact sub_eq_zero.mp h0
    have key0 : ∀ x k : ℤ, x = (N : ℤ) * k → ((x : ZMod N)) = 0 := by
      intro x k hx; rw [hx]; push_cast; simp
    have e00 : ((δ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1
        = (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c' - c' * c') := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hδ]
      linear_combination hdet + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 - c') * hc'
    have e11 : ((δ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1
        = (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c'
            - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hδ]
      linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'
    have e10 : ((δ * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
        = (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * c'
            - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hδ]
      linear_combination (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hc'
    exact (CongruenceSubgroup.Gamma1_mem N _).mpr
      ⟨key1 _ _ e00, key1 _ _ e11, key0 _ _ e10⟩
  have hmemG : Matrix.SpecialLinearGroup.mapGL ℝ δ * Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ G := by
    rw [← map_mul]
    exact h1 (Subgroup.mem_map_of_mem _ hmem)
  simpa using mul_mem hmemG (inv_mem hg)

/-- **`W_N` permutes the cusps of `G`** (PROVEN) — the witness for
`W_N • c` is `W_N p W_N⁻¹`, which lies in `G` by
`frickeMatrix_conj_mem_of_le`, is parabolic because parabolicity is a
conjugation invariant, and fixes `W_N • c` by the group action. -/
lemma isCusp_frickeMatrix_smul_of_le (N : ℕ) (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) {c : OnePoint ℝ} (hc : IsCusp c G) :
    IsCusp (frickeMatrix N hN • c) G := by
  obtain ⟨p, hpΓ, hpar, hpc⟩ := hc
  refine ⟨frickeMatrix N hN * p * (frickeMatrix N hN)⁻¹,
    frickeMatrix_conj_mem_of_le N hN h1 h0 hpΓ, by simpa using hpar, ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, hpc]

/-- **The Fricke transform `f ∣[2] W_N` of a cusp form on `G` is again a
cusp form on `G`** (PROVEN).

Slash-invariance: `(f ∣ W_N) ∣ γ = f ∣ (W_N γ) = f ∣ ((W_N γ W_N⁻¹) W_N)
= (f ∣ (W_N γ W_N⁻¹)) ∣ W_N = f ∣ W_N`.
Holomorphy: `MDifferentiable.slash`, which holds for the full `GL(2, ℝ)`
slash action.
Vanishing at the cusps: `OnePoint.IsZeroAt.smul_iff` says
`IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k` for EVERY
`g : GL(2, ℝ)`, so the obligation reduces to
`isCusp_frickeMatrix_smul_of_le` and nothing has to be expanded at a
cusp — in particular no Hermite normal form is needed.  (That is the
same simplification `WeightTwoEigenform.lean` records for the `Γ₀`
instance `frickeSlash`.) -/
noncomputable def frickeSlashOn (N : ℕ) (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) : CuspForm G 2 where
  toFun := (f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] frickeMatrix N hN
  slash_action_eq' γ hγ := by
    have key : frickeMatrix N hN * γ
        = frickeMatrix N hN * γ * (frickeMatrix N hN)⁻¹ * frickeMatrix N hN := by
      group
    rw [← SlashAction.slash_mul, key, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq (Γ := G) (k := 2) f _
        (frickeMatrix_conj_mem_of_le N hN h1 h0 hγ)]
  holo' := (CuspFormClass.holo f).slash 2 (frickeMatrix N hN)
  zero_at_cusps' hc := by
    rw [← OnePoint.IsZeroAt.smul_iff]
    exact CuspFormClass.zero_at_cusps f (isCusp_frickeMatrix_smul_of_le N hN h1 h0 hc)

@[simp] lemma coe_frickeSlashOn (N : ℕ) (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) :
    (frickeSlashOn N hN h1 h0 f : UpperHalfPlane → ℂ)
      = (f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] frickeMatrix N hN := rfl

/-- **The Fricke involution `W_N` on a group between `Γ₁(N)` and `Γ₀(N)`**
(PROVEN 2026-07-28) — the ONE piece of modular input that carries the
continuation, and the only one of the four that uses the upper bound on
`G`.

TRUE and classical (Atkin–Lehner; Diamond–Shurman §5.2).
`W_N = ![![0, -1], ![N, 0]]` normalises `Γ₀(N)` and acts on
`Γ₀(N)/Γ₁(N) ≅ (ℤ/N)ˣ` by `d ↦ d⁻¹`, so it normalises every intermediate
`G = Γ_H(N)`; hence `f ∣[2] W_N` is again a cusp form on `G`.  Writing
`g` for it, the slash identity `f(-1/(Nz)) = N z² g z` at `z = i y/√N` —
where `-1/(Nz) = i/(√N y)` and `N z² = -y²` — is exactly the displayed
statement.  On `Γ₁(N)` the involution moves the nebentypus,
`S₂(N, χ) → S₂(N, χ̄)`, which changes which form appears on the other side
of the functional equation and changes NOTHING about this statement,
because `g` is quantified existentially and `χ` does not occur.

The witness is `frickeSlashOn N hN h1 h0 f`; the sign `-1` and the weight
`y²` come out of `|det W_N|^{k-1} · denom(W_N, z)^{-k} = N (i y √N)^{-2}
= -1/y²`.  This is the root number `ε = -1` of `cuspFEPairOn`, and it is
what makes `Λ` entire, hence `L(f, ·)` entire.

**An earlier version of this docstring said `W_N` had to be built from
scratch — "none of which exists at this pin" — and listed a Hermite
normal form for the cusp condition.  All of that is now stale.**
`WeightTwoEigenform.lean` built `frickeMatrix` and proved the `Γ₀`
instance `exists_frickeInvolution` on 2026-07-28; the only genuinely new
work here is `frickeMatrix_conj_mem_of_le` (normalisation of the abstract
`G`, three lines of `linear_combination` mod `N`), and the Hermite step
is not needed at this pin because mathlib's `CuspForm` quantifies its
vanishing condition over ALL cusps and `OnePoint.IsZeroAt.smul_iff`
converts it into a statement about `W_N`-translates. -/
theorem exists_frickeInvolutionOn (N : ℕ) (hN : N ≠ 0) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) :
    ∃ g : CuspForm G 2, ∀ y : ℝ, 0 < y →
      axisRestrictOn G N f (1 / y) = -((y ^ (2 : ℝ) : ℝ) : ℂ) * axisRestrictOn G N g y := by
  refine ⟨frickeSlashOn N hN h1 h0 f, fun y hy => ?_⟩
  have hy' : (0 : ℝ) < 1 / y := by positivity
  rw [axisRestrictOn_of_pos hN f hy', axisRestrictOn_of_pos hN _ hy]
  simp only [coe_frickeSlashOn, ModularForm.slash_apply, frickeMatrix_smul_axisPoint N hN hy,
    UpperHalfPlane.σ, UpperHalfPlane.denom, frickeMatrix_coe, frickeMatrix_det, coe_axisPoint]
  norm_num
  rw [if_pos (Nat.pos_of_ne_zero hN), ContinuousAlgEquiv.refl_apply]
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hsC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hyC : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hs2 : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  rw [← hs2]
  field_simp
  rw [Complex.I_sq]
  ring

/-- **A cusp form decays faster than every power at `i∞`** (PROVEN
2026-07-28).

TRUE and elementary given the `q`-expansion, which is what `h1` supplies:
`Γ₁(N) ≤ G` puts `T = ![![1, 1], ![0, 1]]` in `G`, so `f` is `1`-periodic,
and `CuspForm`'s zero-at-`∞` condition then makes the expansion start at
`n = 1`; hence `f(i y/√N) = O(e^{-2πy/√N})`, which beats `y ^ r` for every
real `r`.  Stated for an arbitrary cusp form rather than for an eigenform
because the Fricke partner `g` above needs it too and is not known to be
an eigenform.

**The exponential decay is mathlib's**, not new modular input:
`CuspFormClass.exp_decay_atImInfty` gives
`f =O[atImInfty] fun τ ↦ exp (-2π (im τ)/h)` from nothing but `0 < h` and
`h ∈ G.strictPeriods`; here `h = 1` by `one_mem_strictPeriodsOn`, which is
exactly where `h1` is consumed and is the ONLY place it is.  The rest is
transport along `y ↦ i y/√N` (whose imaginary part is `y/√N`, so `atTop`
pushes forward into `atImInfty`) followed by
`isLittleO_exp_neg_mul_rpow_atTop`.

No level hypothesis is needed: at `N = 0` the left-hand side is
identically `0` by `axisRestrictOn_zero_level`. -/
theorem isBigO_atTop_axisRestrictOn (N : ℕ) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (f : CuspForm G 2) (r : ℝ) :
    axisRestrictOn G N f =O[atTop] fun y : ℝ => y ^ r := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [axisRestrictOn_zero_level]
    exact isBigO_zero _ _
  · have hsq : (0 : ℝ) < Real.sqrt N :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
    have hdecay : (f : UpperHalfPlane → ℂ) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-2 * Real.pi * τ.im / 1) :=
      CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos (one_mem_strictPeriodsOn N h1)
    rw [Asymptotics.isBigO_iff] at hdecay
    obtain ⟨c, hc⟩ := hdecay
    rw [UpperHalfPlane.atImInfty, Filter.eventually_comap, Filter.eventually_atTop] at hc
    obtain ⟨A, hA⟩ := hc
    have hexp : axisRestrictOn G N f =O[atTop]
        fun y : ℝ => Real.exp (-(2 * Real.pi / Real.sqrt N) * y) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨c, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (max 1 (A * Real.sqrt N))] with y hy
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hy)
      have hyA : A ≤ y / Real.sqrt N :=
        (le_div_iff₀ hsq).mpr ((le_max_right _ _).trans hy)
      have him : (axisPoint N y ⟨hy0, hN⟩).im = y / Real.sqrt N := im_axisPoint N y _
      have hb := hA (y / Real.sqrt N) hyA (axisPoint N y ⟨hy0, hN⟩) him
      rw [him] at hb
      rw [axisRestrictOn_of_pos hN f hy0]
      refine hb.trans_eq ?_
      rw [show -2 * Real.pi * (y / Real.sqrt N) / 1
        = -(2 * Real.pi / Real.sqrt N) * y from by ring]
    exact hexp.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- **`f` restricted to the imaginary axis is locally integrable on
`(0, ∞)`** (PROVEN 2026-07-28) — it is continuous there, `f` being
holomorphic; the only content is transporting continuity through the
`ℍ`-coercion, which is an `IsEmbedding` (`UpperHalfPlane.isEmbedding_coe`),
so continuity into `ℍ` is continuity of the `ℂ`-valued composite.  No
hypothesis on `G` is used, and none is needed.

No level hypothesis is needed either: at `N = 0` the function is
identically `0` by `axisRestrictOn_zero_level`. -/
theorem locallyIntegrableOn_axisRestrictOn (N : ℕ) (G : Subgroup (GL (Fin 2) ℝ))
    (f : CuspForm G 2) :
    LocallyIntegrableOn (axisRestrictOn G N f) (Set.Ioi 0) := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [axisRestrictOn_zero_level]
    exact (locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _
  · refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Ioi (0 : ℝ)) (axisRestrictOn G N f)
        = fun y : Set.Ioi (0 : ℝ) => f (axisPoint N y.1 ⟨y.2, hN⟩) :=
      funext fun y => axisRestrictOn_of_pos hN f y.2
    rw [heq]
    refine (ModularFormClass.continuous f).comp ?_
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    simp only [Function.comp_def, coe_axisPoint]
    fun_prop

/-- The strong FE-pair attached to `f`: the pair `(f, f ∣ W_N)` read along
the rescaled imaginary axis, with weight `k = 2` and root number `ε = -1`. -/
noncomputable def cuspFEPairOn (N : ℕ) (hN : N ≠ 0) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) : WeakFEPair ℂ where
  f := axisRestrictOn G N f
  g := axisRestrictOn G N (exists_frickeInvolutionOn N hN G h1 h0 f).choose
  k := 2
  ε := -1
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_axisRestrictOn N G f
  hg_int := locallyIntegrableOn_axisRestrictOn N G _
  hk := two_pos
  hε := by norm_num
  h_feq := fun x hx => by
    simpa [smul_eq_mul] using (exists_frickeInvolutionOn N hN G h1 h0 f).choose_spec x hx
  hf_top := fun r => by simpa using isBigO_atTop_axisRestrictOn N G h1 f r
  hg_top := fun r => by simpa using isBigO_atTop_axisRestrictOn N G h1 _ r

lemma isStrongFEPair_cuspFEPairOn (N : ℕ) (hN : N ≠ 0) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) :
    IsStrongFEPair (cuspFEPairOn N hN G h1 h0 f) := ⟨rfl, rfl⟩

/-- **`a` is the `q`-expansion coefficient sequence of `f` in mathlib's
sense** (PROVEN 2026-07-28) — the bridge between this module's
`IsWeightTwoEigenformOn` packaging and `UpperHalfPlane.qExpansion`, and
the `G`-generic form of `WeightTwoEigenform.lean`'s
`coeff_eq_qExpansion_coeff`.

The two `qExpansion` fields say exactly that `∑_{n ≥ 1} aₙ qⁿ` converges
to `f τ` at every `τ ∈ ℍ` with `q = e^{2πiτ}`; adding the vanishing
constant term `a 0 = 0` turns that into a `HasSum` over all of `ℕ`, and
`ModularFormClass.qExpansion_coeff_unique` (the Taylor coefficients of a
holomorphic function on the punctured disc are unique) identifies it with
mathlib's `qExpansion 1 f`.  `h = 1` is legitimate by
`one_mem_strictPeriodsOn`, which is the only use of `h1`. -/
theorem coeff_eq_qExpansion_coeffOn {N : ℕ} {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) (m : ℕ) :
    a m = (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)).coeff m := by
  refine ModularFormClass.qExpansion_coeff_unique (k := 2) (h := 1) one_pos
    (one_mem_strictPeriodsOn N h1) (fun τ => ?_) m
  have h0 : HasSum (fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)))
      ((f : UpperHalfPlane → ℂ) τ) := by
    rw [hf.qExpansion τ]
    exact (hf.qExpansionSummable τ).hasSum
  have hfun : (fun n : ℕ => a (n + 1) • Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))
      = fun n : ℕ => a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)) := by
    funext n
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  refine (hasSum_nat_add_iff' (f := fun m : ℕ =>
    a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) 1).mp ?_
  have hzero : ∑ i ∈ Finset.range 1, a i • Function.Periodic.qParam 1 (τ : ℂ) ^ i = 0 := by
    simp [hf.zero]
  rw [hzero, sub_zero]
  simpa only [hfun] using h0

/-- **Hecke's bound `|aₙ| = O(n)`, for `G` between the two bounds**
(PROVEN 2026-07-28) — the working form of `isBigO_atTop_coeffOn` below,
which is this statement transported down to `G = Γ₁(N)`.

All of the analysis is mathlib's: `Mathlib/NumberTheory/ModularForms/
Bounds.lean` proves `CuspFormClass.petersson_bounded_left`,
`CuspFormClass.exists_bound` and finally `CuspFormClass.qExpansion_isBigO`,
which IS Hecke's bound `O(n^{k/2})` for any ARITHMETIC `Γ`.  What this
subsection has to supply is the two facts about the abstract `G` that
those need — `isArithmeticOn` and `strictWidthInftyOn`, both of which use
BOTH bounds — plus the identification of `a` with mathlib's coefficients
(`coeff_eq_qExpansion_coeffOn`) and `(2 : ℤ)/2 = 2 - 1`.

Deligne's `|aₙ| ≤ d(n) √n` is *not* needed, which is why the half plane in
`IsLFunctionOf` is `Re s > 2` rather than `Re s > 3/2`. -/
theorem isBigO_atTop_coeffOn_of_le {N : ℕ} (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (h0 : G ≤ Gamma0GL N) (hf : IsWeightTwoEigenformOn G N χ f a) :
    a =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 - 1 : ℝ) := by
  haveI : NeZero N := ⟨hN⟩
  haveI : G.IsArithmetic := isArithmeticOn N h1 h0
  have hbig := CuspFormClass.qExpansion_isBigO (Γ := G) (k := 2) f
  rw [strictWidthInftyOn N h1 h0, show ((2 : ℤ) : ℝ) / 2 = (2 - 1 : ℝ) from by norm_num] at hbig
  rw [show a = fun m : ℕ => (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)).coeff m from
    funext (coeff_eq_qExpansion_coeffOn h1 hf)]
  exact hbig

/-- **Hecke's bound `|aₙ| = O(n)`** (PROVEN 2026-07-28, after a FALSITY
REPAIR — see below).

TRUE for every weight-two cusp form on a genuine level.  Proven by
restricting `f` to `Γ₁(N)` (`IsWeightTwoEigenformOn.restrict`, which is
legitimate because `CuspForm` is contravariant in its group) and citing
`isBigO_atTop_coeffOn_of_le` there, where both bounds hold by `le_rfl`
and `gamma1GL_le_gamma0GL`.  That is what keeps this leaf stated with
the LOWER bound alone, as it was written; `isArithmeticOn` genuinely
needs the upper bound, and without the restriction step this statement
would have had to carry `G ≤ Γ₀(N)` too.

**An earlier version of this docstring claimed "mathlib has `petersson`
but not its boundedness" and that `h1` supplies finite index directly.
Both were wrong.**  Mathlib does have the boundedness — see
`isBigO_atTop_coeffOn_of_le` — and `Γ₁(N) ≤ G` does NOT by itself give
`G` finite index in `SL(2, ℤ)`, since `G` is an arbitrary subgroup of
`GL(2, ℝ)` and `G = ⊤` satisfies the hypothesis.  Arithmeticity comes
from the sandwich, and reaches this statement through the restriction.

### FALSITY AUDIT (2026-07-28): `hN : N ≠ 0` is NOT decoration

The statement used to be quantified over every `N : ℕ`, and **at `N = 0`
it is FALSE**.  The refutation is a one-line reduction to the audit
already recorded on `WeightTwoEigenform.lean`'s `isBigO_atTop_coeff`:
instantiate at `G = Γ₀(0)` and `χ = 1`, where
`isWeightTwoEigenformOn_gamma0_iff` turns the hypothesis into
`IsWeightTwoEigenform 0 f a` on the nose, so an `hN`-free version here
would give an `hN`-free version there — which that audit refutes with an
explicit witness.  For the record, the witness transfers verbatim, and it
lands equally at `G = Γ₁(0) = ⟨T⟩` (the only cusp of `⟨T⟩` is `∞`, so a
`CuspForm (Gamma1GL 0) 2` is precisely a holomorphic, `1`-periodic `f`
tending to `0` at `i∞`):

> `a n := n ^ 10` for `n ≥ 1`, `a 0 := 0`, and
> `f τ := ∑_{n ≥ 1} n^10 e^{2πinτ}`.

`f` is holomorphic (the series is dominated by a geometric series),
`1`-periodic, and `→ 0` at `i∞`; `qExpansion` and `qExpansionSummable`
hold by construction, `a 0 = 0` and `a 1 = 1`, `hecke` is **vacuous**
(`p ∣ 0` for every `p`, so `¬ p ∣ N` is never satisfied), and `atkin`
asks exactly that `a` be completely multiplicative, which `n ↦ n^10` is.
But `a p = p^10` is not `O(p)`.

The defect is that `Γ₀(N)` — and `Γ₁(N)` — has finite index in
`SL(2, ℤ)` exactly for `N ≥ 1`; at `N = 0` the quotient has infinite
volume and every polynomial coefficient bound fails.  Mechanically,
`isArithmeticOn` requires `[NeZero N]`.  The repair is the hypothesis
`hN`; the one consumer,
`lSeriesSummable_of_isWeightTwoEigenformOn`, is used only from
`mellin_axisRestrictOn`, which already carries `hN`, so nothing
downstream changes. -/
theorem isBigO_atTop_coeffOn {N : ℕ} (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) :
    a =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 - 1 : ℝ) :=
  isBigO_atTop_coeffOn_of_le hN (G := Gamma1GL N) le_rfl (gamma1GL_le_gamma0GL N)
    (hf.restrict h1)

/-- The Dirichlet series of a weight-two cusp form converges absolutely on
`Re s > 2` (PROVEN, from `isBigO_atTop_coeffOn`).

`hN` is inherited from `isBigO_atTop_coeffOn`'s FALSITY REPAIR; the sole
consumer `mellin_axisRestrictOn` already carries it. -/
theorem lSeriesSummable_of_isWeightTwoEigenformOn {N : ℕ} (hN : N ≠ 0)
    {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable a s :=
  LSeriesSummable_of_isBigO_rpow hs (isBigO_atTop_coeffOn hN h1 hf)

/-- Along the rescaled imaginary axis the `q`-expansion is a genuine
convergent sum of real exponentials — the shape `hasSum_mellin` wants
(PROVEN, from the two `qExpansion` fields).  This is where
`qExpansionSummable` earns its place in `IsWeightTwoEigenformOn`. -/
theorem hasSum_axisRestrictOn {N : ℕ} (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ}
    (hf : IsWeightTwoEigenformOn G N χ f a) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ =>
        a (n + 1) * ((Real.exp (-(2 * Real.pi / Real.sqrt N * (n + 1)) * y) : ℝ) : ℂ))
      (axisRestrictOn G N f y) := by
  have h := (hf.qExpansionSummable (axisPoint N y ⟨hy, hN⟩)).hasSum
  rw [← hf.qExpansion] at h
  rw [axisRestrictOn_of_pos hN f hy]
  have hEq : (fun n : ℕ =>
        a (n + 1) * ((Real.exp (-(2 * Real.pi / Real.sqrt N * (n + 1)) * y) : ℝ) : ℂ))
      = fun n : ℕ => a (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * (n + 1) *
          ((axisPoint N y ⟨hy, hN⟩ : UpperHalfPlane) : ℂ)) := by
    funext n
    congr 1
    rw [Complex.ofReal_exp, coe_axisPoint]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (y : ℂ)) /
      ((Real.sqrt N : ℝ) : ℂ)) * Complex.I_sq
  rw [hEq]
  exact h

/-- **The Mellin transform of `f` on the axis is
`Γ(s) (2π/√N)^{-s} L(f, s)`** (PROVEN) — termwise integration of the
`q`-expansion, i.e. mathlib's `hasSum_mellin`. -/
theorem mellin_axisRestrictOn {N : ℕ} (hN : N ≠ 0) {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) {s : ℂ} (hs : 2 < s.re) :
    mellin (axisRestrictOn G N f) s =
      Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  set c : ℝ := 2 * Real.pi / Real.sqrt N with hcdef
  have hcpos : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hsummable : LSeriesSummable a s := lSeriesSummable_of_isWeightTwoEigenformOn hN h1 hf hs
  -- the four hypotheses of `hasSum_mellin`
  have hp : ∀ n : ℕ, a (n + 1) = 0 ∨ 0 < c * (n + 1) := fun n => Or.inr (by positivity)
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum
      (fun n : ℕ => a (n + 1) * ((Real.exp (-(c * (n + 1)) * t) : ℝ) : ℂ))
      (axisRestrictOn G N f t) :=
    fun t ht => hasSum_axisRestrictOn hN hf ht
  have hnorm : ∀ n : ℕ, ‖LSeries.term a s (n + 1)‖ = ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ s.re := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
    push_cast
    ring_nf
  have hsum : Summable fun n : ℕ => ‖a (n + 1)‖ / (c * ((n : ℝ) + 1)) ^ s.re := by
    have hterm : Summable fun n : ℕ => ‖LSeries.term a s (n + 1)‖ :=
      (summable_nat_add_iff 1).mpr (summable_norm_iff.mpr hsummable)
    refine (hterm.mul_left (c ^ s.re)⁻¹).congr fun n => ?_
    rw [hnorm n, Real.mul_rpow hcpos.le (by positivity)]
    field_simp
  have H := hasSum_mellin hp hs0 hF hsum
  -- rewrite the summand as `(Γ s * c^{-s}) * term a s (n+1)`
  have Hterm : HasSum (fun n : ℕ => LSeries.term a s (n + 1)) (LSeries a s) := by
    have h0 : HasSum (LSeries.term a s) (LSeries a s) := hsummable.hasSum
    have h0' := (hasSum_nat_add_iff' (f := LSeries.term a s) 1).mpr h0
    rwa [Finset.sum_range_one, LSeries.term_zero, sub_zero] at h0'
  have H2 := Hterm.mul_left (Complex.Gamma s * ((c : ℝ) : ℂ) ^ (-s))
  have hcs : ((c : ℝ) : ℂ) ^ s ≠ 0 := fun h => hcC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hEq : (fun n : ℕ =>
        Complex.Gamma s * a (n + 1) / ((c * ((n : ℝ) + 1) : ℝ) : ℂ) ^ s)
      = fun n : ℕ =>
        Complex.Gamma s * ((c : ℝ) : ℂ) ^ (-s) * LSeries.term a s (n + 1) := by
    funext n
    have hn0 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hns : (((n : ℝ) + 1 : ℝ) : ℂ) ^ s ≠ 0 :=
      fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hcpos.le (by positivity),
      LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg]
    rw [show (((n : ℕ) + 1 : ℕ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [hEq] at H
  exact H.unique H2

/-- **Hecke: the `L`-function of a weight-two eigenform on any group
between `Γ₁(N)` and `Γ₀(N)` exists** (PROVEN 2026-07-28, over the four
analytic leaves above) — the `Γ₁` half of
`exists_isLFunctionOf_of_isWeightTwoEigenformOn` is the instance
`G = Γ₁(N)`, and `WeightTwoEigenform.lean`'s
`exists_isLFunctionOf_of_isWeightTwoEigenform` is the instance
`G = Γ₀(N)`.

The proof is `WeightTwoEigenform.lean`'s assembly with the group left
free: `cuspFEPairOn` packages `(f, f ∣ W_N)` as a `WeakFEPair`,
`IsStrongFEPair.differentiable_Λ` makes its `Λ` entire, and
`mellin_axisRestrictOn` identifies `Λ` with `Γ(s) (2π/√N)^{-s} L(f, s)` on
`Re s > 2`; dividing by the two elementary factors gives an entire `L`
agreeing with the Dirichlet series there, which is `IsLFunctionOf`.

`hN : N ≠ 0` is NOT decoration — see the FALSITY AUDIT on
`exists_isLFunctionOf_of_isWeightTwoEigenform`, whose counterexample
(`a ≡ 1`, `L = ζ`, pole at `s = 1`) applies to every shape.  Here it is
also what makes `√N > 0`, hence the rescaling legitimate.

The eigenform conditions are not used by Hecke's argument at all: `hf` is
consumed only through `qExpansion`, `qExpansionSummable` (in
`hasSum_axisRestrictOn`) and `isBigO_atTop_coeffOn`, all of which are
statements about `f` being a genuine cusp form with `a` its CONVERGENT
expansion. -/
theorem exists_isLFunctionOf_of_isWeightTwoEigenformOn_of_le (N : ℕ) (hN : N ≠ 0)
    (G : Subgroup (GL (Fin 2) ℝ)) (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N)
    (χ : DirichletCharacter ℂ N) (f : CuspForm G 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn G N χ f a) :
    ∃ L : ℂ → ℂ, IsLFunctionOf a L := by
  have hstrong : IsStrongFEPair (cuspFEPairOn N hN G h1 h0 f) :=
    isStrongFEPair_cuspFEPairOn N hN G h1 h0 f
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hcpos : (0 : ℝ) < 2 * Real.pi / Real.sqrt N := by positivity
  have hcC : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcpos.ne'
  refine ⟨fun s => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
    (cuspFEPairOn N hN G h1 h0 f).Λ s * (Complex.Gamma s)⁻¹, ?_, ?_⟩
  · -- entirety: a product of three entire functions
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact ((differentiable_id.const_cpow (Or.inl hcC)).mul
      hstrong.differentiable_Λ).mul Complex.differentiable_one_div_Gamma
  · -- agreement with the Dirichlet series on `Re s > 2`
    intro s hs
    have hΛ : (cuspFEPairOn N hN G h1 h0 f).Λ s =
        Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
      rw [congr_fun hstrong.Λ_eq s]
      exact mellin_axisRestrictOn hN h1 hf hs
    have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcancel : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hcC, add_neg_cancel, Complex.cpow_zero]
    show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s * (cuspFEPairOn N hN G h1 h0 f).Λ s *
      (Complex.Gamma s)⁻¹ = LSeries a s
    rw [hΛ, show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s) *
        (Complex.Gamma s)⁻¹
      = (((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
          ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) * LSeries a s from by ring,
      hcancel, mul_inv_cancel₀ hΓ, one_mul, one_mul]

/-- **Hecke's Mellin transform at `s = 1`, on any group between `Γ₁(N)`
and `Γ₀(N)`: `L(f, 1) = 2π ∫₀^∞ f(iy) dy`** (PROVEN 2026-07-30) — the
group-generic form of `WeightTwoEigenform.lean`'s
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod`, and the theorem
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` below is its
instance at `G = Γ₁(N)`.

**THIS IS THE HOIST THE `Γ₁` LEAF'S DOCSTRING ASKED FOR, and it cost a
citation rather than a theory build.**  That docstring diagnosed the
situation exactly — "`X0.lean`'s theorem is proven, and its proof uses
nothing about `Γ₀(N)` beyond the TYPE of `f`" — and prescribed replacing
`Gamma0GL N` by a variable `G` in `axisRestrict`, `cuspFEPair` and the
four analytic leaves.  **That work had already been done**, on
2026-07-28, in the `HeckeOn` subsection above: `axisRestrictOn`,
`exists_frickeInvolutionOn`, `cuspFEPairOn`,
`isStrongFEPair_cuspFEPairOn`, `hasSum_axisRestrictOn` and
`mellin_axisRestrictOn` are all group-generic and all PROVEN, because
`exists_isLFunctionOf_of_isWeightTwoEigenformOn_of_le` immediately above
needed exactly the same generalisation.  So the only thing missing was
this second consumer of that machinery, and its proof is the `Γ₀` one
with `axisRestrict N f ↦ axisRestrictOn G N f` and
`cuspFEPair N hN f ↦ cuspFEPairOn N hN G h1 h0 f` — no step of the
argument changes.

The four ingredients, in the order the proof uses them:

* `isStrongFEPair_cuspFEPairOn` makes `Λ` of the pair `(f, f ∣ W_N)`
  entire (`IsStrongFEPair.differentiable_Λ`), so
  `s ↦ (2π/√N)^s Λ(s) / Γ(s)` is entire — `1/Γ` being entire;
* `mellin_axisRestrictOn` identifies `Λ(s) = Γ(s)(2π/√N)^{-s} L(f, s)` on
  `Re s > 2`, so that function IS the Dirichlet series there;
* `IsLFunctionOf` says `L` is entire and agrees with the Dirichlet series
  on `Re s > 2`, so the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the
  preconnected `Set.univ`, seeded at `s = 3`) forces
  `L 1 = (2π/√N)·Λ(1)`, using `Γ(1) = 1`;
* `hasSum_axisRestrictOn` turns `Λ(1) = ∫₀^∞ f(iy/√N) dy` into
  `√N · cuspPeriod a` by the change of variables `y ↦ y/√N`
  (`integral_comp_mul_left_Ioi`), which is where `cuspPeriod`'s own
  normalisation — a sum of `exp (-2π(n+1)y)`, no `√N` — is matched.

`hN : N ≠ 0` is load-bearing twice: it is what makes `√N > 0`, hence the
rescaling legitimate, and it is inherited from `mellin_axisRestrictOn`
(through `isBigO_atTop_coeffOn`'s FALSITY REPAIR — `Γ₁(0)` has infinite
index in `SL(2, ℤ)` and no polynomial coefficient bound holds).

`χ` and the eigenform fields `hecke`/`atkin` are inert: `hf` is consumed
only through `qExpansion`, `qExpansionSummable` (inside
`hasSum_axisRestrictOn`) and `isBigO_atTop_coeffOn`. -/
theorem lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn_of_le (N : ℕ) (hN : N ≠ 0)
    (G : Subgroup (GL (Fin 2) ℝ)) (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N)
    (χ : DirichletCharacter ℂ N) (f : CuspForm G 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn G N χ f a)
    (L : ℂ → ℂ) (hL : IsLFunctionOf a L) :
    L 1 = 2 * (Real.pi : ℂ) * cuspPeriod a := by
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hcpos : (0 : ℝ) < 2 * Real.pi / Real.sqrt N := by positivity
  have hcC : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hstrong : IsStrongFEPair (cuspFEPairOn N hN G h1 h0 f) :=
    isStrongFEPair_cuspFEPairOn N hN G h1 h0 f
  -- `s ↦ c^s Λ(s) / Γ(s)` is entire: `Λ` is entire and `1/Γ` is entire.
  have hFentire : AnalyticOnNhd ℂ
      (fun s : ℂ => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (cuspFEPairOn N hN G h1 h0 f).Λ s * (Complex.Gamma s)⁻¹) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact ((differentiable_id.const_cpow (Or.inl hcC)).mul
      hstrong.differentiable_Λ).mul Complex.differentiable_one_div_Gamma
  -- and it is the Dirichlet series on `Re s > 2`
  have hFeq : ∀ s : ℂ, 2 < s.re →
      ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s * (cuspFEPairOn N hN G h1 h0 f).Λ s *
        (Complex.Gamma s)⁻¹ = LSeries a s := by
    intro s hs
    have hΛ : (cuspFEPairOn N hN G h1 h0 f).Λ s =
        Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
      rw [congr_fun hstrong.Λ_eq s]
      exact mellin_axisRestrictOn hN h1 hf hs
    have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcancel : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hcC, add_neg_cancel, Complex.cpow_zero]
    rw [hΛ, show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s) *
        (Complex.Gamma s)⁻¹
      = (((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
          ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) * LSeries a s from by ring,
      hcancel, mul_inv_cancel₀ hΓ, one_mul, one_mul]
  -- identity theorem: two entire functions agreeing on `Re s > 2` agree at `s = 1`
  have hL1 : L 1 = ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) *
      (cuspFEPairOn N hN G h1 h0 f).Λ 1 := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (3 : ℂ) ∈ {z : ℂ | 2 < z.re} := by norm_num
    have key : Set.EqOn L (fun s : ℂ => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (cuspFEPairOn N hN G h1 h0 f).Λ s * (Complex.Gamma s)⁻¹) Set.univ := by
      refine hL.entire.eqOn_of_preconnected_of_eventuallyEq hFentire isPreconnected_univ
        (Set.mem_univ (3 : ℂ)) ?_
      filter_upwards [hopen.mem_nhds hmem] with z hz
      rw [hL.eq_lseries z hz, hFeq z hz]
    have := key (Set.mem_univ (1 : ℂ))
    simpa [Complex.cpow_one, Complex.Gamma_one] using this
  -- the completed transform at `s = 1` is `√N` times the period
  have hΛ1 : (cuspFEPairOn N hN G h1 h0 f).Λ 1 =
      ((Real.sqrt N : ℝ) : ℂ) * cuspPeriod a := by
    have hmel : (cuspFEPairOn N hN G h1 h0 f).Λ 1
        = ∫ y in Set.Ioi (0 : ℝ), axisRestrictOn G N f y := by
      rw [congr_fun hstrong.Λ_eq 1]
      simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
      rfl
    have hpt : ∀ y ∈ Set.Ioi (0 : ℝ), axisRestrictOn G N f y =
        (fun u : ℝ => ∑' n : ℕ,
            a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ))))
          ((Real.sqrt N)⁻¹ * y) := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      have h := (hasSum_axisRestrictOn hN hf hy').tsum_eq
      rw [← h]
      refine tsum_congr fun n => ?_
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hint : (∫ y in Set.Ioi (0 : ℝ), axisRestrictOn G N f y)
        = ∫ y in Set.Ioi (0 : ℝ), (fun u : ℝ => ∑' n : ℕ,
            a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ))))
          ((Real.sqrt N)⁻¹ * y) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt
    rw [hmel, hint,
      MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => ∑' n : ℕ,
        a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ)))) 0
        (inv_pos.mpr hsq)]
    rw [cuspPeriod]
    rw [mul_zero, inv_inv, Complex.real_smul]
  rw [hL1, hΛ1]
  have hsqC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
  push_cast
  field_simp

end HeckeOn

/-- **Hecke: the `L`-function of a weight-two eigenform on `Γ₁(N)`
exists** (PROVEN 2026-07-28, by citation) — the genuinely `Γ₁` half of
Hecke's continuation.

**This is now an ASSEMBLY, not a leaf.**  It is
`exists_isLFunctionOf_of_isWeightTwoEigenformOn_of_le` at `G = Γ₁(N)`,
where the two side conditions are `le_rfl` and `gamma1GL_le_gamma0GL`.
What it used to assert directly now lives in the four analytic leaves of
the subsection above, each stated once for every group between `Γ₁(N)`
and `Γ₀(N)` rather than twice.

The `Γ₀` half is `exists_isLFunctionOf_of_isWeightTwoEigenform`, PROVEN
in `WeightTwoEigenform.lean` over the `G = Γ₀(N)` instances of the same
four leaves; the shape-free wrapper below cites that at `.gamma0` and
this at `.gamma1`.  **The duplication is in the leaves only, and both
sides are now PROVEN** (2026-07-28) — see the subsection docstring for
why collapsing them would need a hoist rather than a citation.

TRUE and classical (Hecke, 1936).  The Mellin transform
`Λ(s) = ∫₀^∞ f(iy) y^{s-1} dy` converges for `Re s` large because a cusp
form decays exponentially at `i∞`, equals `(2π)^{-s} Γ(s) L(f, s)` there
by termwise integration of the `q`-expansion, and continues to an entire
function by splitting the integral at `y = 1/√N` and applying the Fricke
involution to the piece near `0`.  On `Γ₁(N)` the involution `W_N` sends
`S_2(N, χ)` to `S_2(N, χ̄)` rather than back to the same space, which
changes which form appears on the other side of the functional equation
and changes NOTHING about the convergence argument that yields entirety —
that is the one point at which a reader should check the generalization
is honest, and it passes, because `exists_frickeInvolutionOn` quantifies
the partner existentially and never mentions `χ`.

`hN : N ≠ 0` is NOT decoration; see the subsection docstring and the
FALSITY AUDIT of the `Γ₀` leaf.  `Γ₁(0)` has infinite index in
`SL(2, ℤ)`, `hecke` is vacuous there, and `a ≡ 1` gives `ζ`, which has a
pole at `s = 1`.

`hf` is load-bearing in only one direction — `f` must be a genuine cusp
form and `a` its CONVERGENT expansion.  The eigenform conditions are not
used by Hecke's argument at all. -/
theorem exists_isLFunctionOf_of_isWeightTwoEigenformOn_gamma1 (N : ℕ) (hN : N ≠ 0)
    (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (Gamma1GL N) N χ f a) :
    ∃ L : ℂ → ℂ, IsLFunctionOf a L :=
  exists_isLFunctionOf_of_isWeightTwoEigenformOn_of_le N hN (Gamma1GL N) le_rfl
    (gamma1GL_le_gamma0GL N) χ f a hf

/-- **Hecke: the `L`-function of a weight-two eigenform exists** (PROVEN
2026-07-27) — LEVEL-FREE and SHAPE-FREE.

**This is an ASSEMBLY, not a leaf.**  At `.gamma0` it is
`exists_isLFunctionOf_of_isWeightTwoEigenform` (PROVEN in
`WeightTwoEigenform.lean`) through `isWeightTwoEigenformOn_gamma0_iff`;
at `.gamma1` it is
`exists_isLFunctionOf_of_isWeightTwoEigenformOn_gamma1`.  The earlier
version of this declaration was a `sorry` asserting the `Γ₀` case as
well, which was already proven — see the subsection docstring for why
that direction was inverted.

TRUE and classical (Hecke, 1936), and the argument is insensitive to
which of `Γ₀(N)`, `Γ₁(N)` the form lives on — the proof recorded on the
`Γ₀` leaf transfers verbatim.  The Mellin transform
`Λ(s) = ∫₀^∞ f(iy) y^{s-1} dy` converges for `Re s` large because a cusp
form decays exponentially at `i∞`, equals `(2π)^{-s} Γ(s) L(f, s)` there
by termwise integration of the `q`-expansion, and continues to an entire
function by splitting the integral at `y = 1/√N` and applying the Fricke
involution to the piece near `0`.  On `Γ₁(N)` the involution `W_N` sends
`S_2(N, χ)` to `S_2(N, χ̄)` rather than back to the same space, which
changes which form appears on the other side of the functional equation
and changes NOTHING about the convergence argument that yields
entirety — that is the only point at which a reader should check that the
generalization is honest, and it passes.

Absolute convergence on `Re s > 2` is the trivial bound `|aₙ| = O(n)`
for a weight-two cusp form; Deligne is not needed.

`hf` is load-bearing in only one direction — `f` must be a genuine cusp
form.  The eigenform conditions are not used by Hecke's argument at all
and a prover may `omit` them.

WHY THE `Γ₀` HALF IS NO LONGER A LEAF: the check this docstring used to
record — "mathlib continues no cusp-form `L`-series" — was true and was
scoped to the wrong axis.  `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`
packages Hecke's argument in group-free form and
`MellinEqDirichlet.lean`'s `hasSum_mellin` is the termwise integration;
between them the analysis is done, and that is what closed the `Γ₀`
half.  What remains at `.gamma1` is modular input, isolated in
`exists_isLFunctionOf_of_isWeightTwoEigenformOn_gamma1` above. -/
theorem exists_isLFunctionOf_of_isWeightTwoEigenformOn (S : ModularLevelShape) (N : ℕ)
    (hN : N ≠ 0) (χ : DirichletCharacter ℂ N) (hχ : S.IsNebentypus N χ)
    (f : CuspForm (S.group N) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (S.group N) N χ f a) :
    ∃ L : ℂ → ℂ, IsLFunctionOf a L := by
  cases S with
  | gamma0 =>
    exact exists_isLFunctionOf_of_isWeightTwoEigenform N hN f a
      ((isWeightTwoEigenformOn_gamma0_iff N f a).1 (hχ ▸ hf))
  | gamma1 => exact exists_isLFunctionOf_of_isWeightTwoEigenformOn_gamma1 N hN χ f a hf

/-! #### The moduli pin for the Hecke operators on `Y_1(N)`

The `Γ₁` transposition of `X0.lean`'s subsection of the same name (new
2026-07-29).  What it produces is a **pin**: a predicate
`IsModularHeckeActionGamma1` on a candidate family `T` saying that `T ℓ`
acts on Abel–Jacobi images exactly by the `Γ₁(N)`-correspondence
`(E, P) ↦ ∑_D (E/D, P + D)`, with `D` running over the cyclic subgroups
of order `ℓ`.

**WHY IT IS HERE.**  `IsHeckeIsotypicDecompositionGamma1` below used to
leave `T` an arbitrary family of endomorphisms, and with an unpinned `T`
the `N = 37` eigen-system swap inhabits the structure — which is exactly
what forces `isTorsion_factor_of_heckeIsotypic_gamma1` to carry the full
analytic hypothesis `hL` rather than the single value
`L(form i, 1) ≠ 0`.  `X0.lean` closed that hole on 2026-07-28 with
`IsModularHeckeAction`; the `Γ₁` side was left open, and BOTH the `Γ₀`
crux paragraph and `exists_heckeAction_isotypicQuotients_gamma1` name
this construction, in these words, as the repair.  This subsection is
that repair and NOTHING ELSE: the sharpening of the Kolyvagin–Logachev
leaf it unblocks is deliberately a separate edit, because two
individually-correct edits to one statement have made a leaf FALSE in
this development before.

**THE ONE CHANGE FROM THE `Γ₀` PIN, and it makes the `Γ₁` version
SHARPER.**  A `Γ₀`-structure is a subgroup and `IsGamma0Isogeny.level`
can only ask that it be carried INTO the quotient's subgroup, recovering
equality from an `ℓ ∤ N` counting argument written out in that
docstring.  A `Γ₁`-structure is a SECTION, so `IsGamma1Isogeny.map_sec`
is a single equation between morphisms `T ⟶ d'.E`,
`d.pt.sec ≫ map = d'.pt.sec`.  That is the same simplification
`IsBaseChangeOfGamma1.map_sec` enjoys over `IsBaseChangeOf.liesIn_iff`,
and for the same reason: a section is transported by one equation where
a subgroup scheme needs a biconditional at every base.

**WHAT THE PIN DOES NOT SETTLE**, stated so it can be checked, and
identical to the `Γ₀` list: it constrains `T ℓ` only at primes `ℓ ∤ N`,
and only on Abel–Jacobi images; that this determines `T ℓ` as a morphism
needs `J_1(N)(ℚ̄)` to be generated by `aj`-images of geometric points,
which is true for the Jacobian of a curve and is not proven here.
Nothing below relies on uniqueness — the pin is used as a hypothesis,
never as a characterisation.

It also says nothing about the DIAMOND operators `⟨d⟩`, which are
genuinely `Γ₁`-specific and have no `Γ₀` counterpart.  That costs nothing
here, and the reason is structural rather than lucky:
`IsHeckeIsotypicDecompositionGamma1` records the nebentypus in its
`neben` field rather than through an action, and its `isotypic` field
speaks only about `T n`.  So the diamonds are not part of the data this
pin exists to constrain. -/

/-- **An `ℓ`-ISOGENY OF `Γ₁(N)`-DATA** (new 2026-07-28) — a morphism of
elliptic schemes with cyclic kernel of order `ℓ`, carrying the level
POINT to the level POINT.  The `Γ₁` analogue of `X0.lean`'s
`IsGamma0Isogeny`, and `d'` is `d/D = (E/D, φ_D P)`.

**THE ONE FIELD THAT DIFFERS FROM THE `Γ₀` VERSION, AND IT IS SIMPLER.**
`IsGamma0Isogeny.level` is a biconditional-free *inclusion* clause at
every base, because a cyclic subgroup scheme has to be compared as a
subfunctor.  A `Γ₁`-structure is a SECTION, so the whole clause collapses
to one equation between morphisms, `map_sec : d.pt.sec ≫ map = d'.pt.sec`
— and it implies the point-level statement at every base by
precomposition, since `RelPoint.ofSection` is literally `g ↦ g ≫ sec`.
This is the same simplification `IsBaseChangeOfGamma1.map_sec` records
against `IsBaseChangeOf.liesIn_iff`, and for the same reason.

**WHY THE QUOTIENT IS QUANTIFIED OVER RATHER THAN CONSTRUCTED**, verbatim
from the `Γ₀` version: constructing `E/D` as an elliptic SCHEME over an
arbitrary base needs fppf quotients by finite flat subgroup schemes
(Raynaud, SGA 3), which is not available at this pin; the `ℚ̄`-fibrewise
statement is, and the pin below is only ever evaluated over `Spec ℚ̄`.

**WHY `¬ ℓ ∣ N` MATTERS FOR SATISFIABILITY, and it is a `Γ₁`-specific
remark.**  `d'.pt` is a field of `Gamma1Datum`, so it carries exact order
`N` by assumption.  That is consistent with `map_sec` precisely because
`ℓ ∤ N` at every use site: `map` has kernel of order `ℓ`, hence is
injective on the `N`-torsion, hence `φ_D P` really does have exact order
`N`.  If `ℓ ∣ N` and `D ⊆ ⟨P⟩`, no `Γ₁`-datum `d'` satisfies `map_sec` at
all — so the pin below would become VACUOUS at such an `ℓ`, not false.
The pin quantifies only over primes `ℓ ∤ N`, so the case never arises.

**WHY THIS PINS `d'` UP TO ISOMORPHISM**, which is what the pin needs, and
the `Γ₀` argument transfers with the level structure carried along: two
quotients of `d` by the same `D` are related by a unique isomorphism `ψ`
of elliptic schemes with `ψ ∘ map = map'`, and then `map_sec` for both
gives `ψ (φ_D P) = φ_D' P`, so `ψ` is an isomorphism of `Γ₁(N)`-DATA over
the same base, hence an `IsBaseChangeOfGamma1 (𝟙 _)`, hence sent to the
SAME point of `Y_1(N)` by `IsCoarseModuliY1.classify_natural`.  That is
what makes the `∀`-over-witnesses form of the pin satisfiable rather than
contradictory. -/
structure IsGamma1Isogeny (N ℓ : ℕ) {T : Scheme.{0}} (d d' : Gamma1Datum N T) where
  /-- the morphism of elliptic schemes -/
  map : d.E ⟶ d'.E
  /-- it lies over the base -/
  comm : map ≫ d'.f = d.f
  /-- it is a homomorphism -/
  add : IsAdditiveOn d.ab d'.ab map comm
  /-- it is surjective -/
  surj : AlgebraicGeometry.Surjective map
  /-- its kernel, a cyclic subgroup scheme of order `ℓ` -/
  ker : CyclicSubgroupOfOrder d.ab ℓ
  /-- `ker` really is the kernel, at every base point -/
  ker_eq : ∀ {T' : Scheme.{0}} {g : T' ⟶ T} (x : RelPoint d.f g),
    RelPoint.post map comm x = d'.ab.zero g ↔ RelPoint.LiesIn ker.ι x
  /-- **the level point is carried to the level point**: `φ_D P = P'`.
  One equation of morphisms, which is the whole `Γ₁` level clause -/
  map_sec : d.pt.sec ≫ map = d'.pt.sec

/-- **THE `Γ₁` MODULI PIN FOR THE HECKE OPERATORS** (new 2026-07-28; the three
ANEMIC RELATIONS added 2026-07-30): `T ℓ` acts on Abel–Jacobi images by the
`Γ₁(N)`-correspondence, and `T` is determined off the primes by the relations.

**THE FOUR CLAUSES, and why (1)–(3) are not decoration.**  Clause (4) is the
moduli recipe and was the original body; it constrains `T` at PRIMES `ℓ ∤ N`
only.  Clauses (1)–(3) — `T 1 = 𝟙 J`, coprime multiplicativity, and the
prime-power recursion `T_{ℓ^{k+2}} = T_ℓ T_{ℓ^{k+1}} − ℓ T_{ℓ^k}` — extend that
to every `n` coprime to `N`, which is the arity range that
`IsIsotypicQuotient.isotypic` and `.equivariant` actually inspect.

**Without them this predicate was too weak and made its consumer FALSE, not
merely unprovable**, because `T` is an INPUT there: a caller could hand over a
family genuine where clause (4) can see and junk where it cannot, and
`exists_modularHeckeAction_gamma1` constructed exactly such a family (`𝟙 J` at
every non-prime arity).  The witness is `T 1 := 0`: `1` is not prime, so clause
(4) says nothing, while `minpoly ℤ (1 : ℂ) = X − 1` forces the quotient map to
be `0`, contradicting `nontriv`.  The full audit, kept as the record of the
defect, is the FALSITY AUDIT on
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` below.

This is a verbatim transport of the `Γ₀` repair of 2026-07-28 —
`IsModularHeckeAction` (`X0.lean`) has carried the identical clauses (1)–(3)
since then — and it costs the frontier nothing, because
`exists_anemicHeckeExtension` (`X0.lean`, level-structure-free) is what supplies
them and the `Γ₀` producer had already been rewritten through it.

For a prime `ℓ ∤ N` and a `Γ₁(N)`-datum `d = (E, P)` over `ℚ̄`, let
`D₁, …, D_{ℓ+1}` be the cyclic subgroups of `E` of order `ℓ` and
`d/D_k = (E/D_k, φ_{D_k} P)` the quotient data.  Then

    T ℓ (aj [d]) = ∑_k aj [d/D_k]

where `[·]` is `IsCoarseModuliY1.classify` followed by the open immersion
`Y_1(N) ↪ X_1(N)`.  This is the classical `T_ℓ` on `Div⁰(X_1(N))` read
through `aj : x ↦ [x] − [o]`.  Diamond–Shurman §5.2–5.3 state the
correspondence at `Γ₁(N)` directly — `Γ₁` being their default level — so
this is if anything the better-documented of the two.

**THE `ℓ + 1` SUBGROUPS ARE NOT COUNTED**, exactly as on the `Γ₀` side:
`m` is an arbitrary arity and the two hypotheses say the kernels are
pairwise distinct and exhaust the order-`ℓ` cyclic subgroups, which over
`ℚ̄` forces `m = ℓ + 1` without this file proving it.  Distinctness and
exhaustion are compared on `ℚ̄`-POINTS, which is faithful because a finite
subgroup scheme of an elliptic curve over an algebraically closed field of
characteristic `0` is étale, hence determined by its points.

**WHY `H` IS TAKEN AS DATA AND NOT AS
`ModularLevelShape.IsCompactification`.**  The latter is
`Nonempty (IsX1Compactification …)`, a `Prop`, and this pin needs
`H.coarse.classify`, which is DATA.  Consumers holding only the truncated
form recover `H` by `Nonempty` elimination, which is legitimate because
every statement they are proving is a `Prop` — that is exactly what the
proof of `exists_heckeAction_isotypicQuotients_gamma1` below does, and it
is why no `∀ H` quantification is needed anywhere.

**FAITHFULNESS, and the honest caveat is the `Γ₀` one.**  The predicate is
*true* of the genuine Hecke operators (the previous paragraph of
`IsGamma1Isogeny` is why the `∀`-over-witnesses form does not
overconstrain them), and it is *false* of `T n := 𝟙 J` and of the `N = 37`
eigen-system swap, which is the entire reason it exists.  **But its
non-vacuity AS A LEAN STATEMENT — that `IsGamma1Isogeny` is inhabited at
the scheme level — is NOT proven here**, exactly as `IsGamma0Isogeny`'s is
not.  The consequence is recorded on the leaf that consumes it below and
it is a graceful degradation, not a soundness problem: were the pin
formally vacuous, `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1`
would be precisely as hard as the undecomposed node and no harder, and
nothing false would have been asserted.  **The check that settles it**:
produce one `IsGamma1Isogeny` over `Spec ℚ̄`.  Note that `X0.lean` records
that check as RUN and NOT closing from `exists_velu_quotient_isogeny` plus
`exists_ellipticScheme_of_weierstrass`, because those produce maps of
POINT GROUPS while `map` is a morphism of SCHEMES; the obstruction is
level-structure-free, so it transfers here verbatim and should not be
re-run from those two inputs. -/
def IsModularHeckeActionGamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (H : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o)
    (T : ℕ → (J ⟶ J)) (T_comp : ∀ n, T n ≫ jstr = jstr) : Prop :=
  -- (1) `T_1 = 1`
  T 1 = 𝟙 J ∧
  -- (2) `T_{mn} = T_m T_n` at coprime arities
  (∀ m n : ℕ, Nat.Coprime m n → T (m * n) = T m ≫ T n) ∧
  -- (3) the prime-power recursion at `ℓ ∤ N`, read on relative points
  (∀ ℓ k : ℕ, ℓ.Prime → ¬ ℓ ∣ N →
    ∀ {T' : Scheme.{0}} (g : T' ⟶ SpecQ) (x : RelPoint jstr g),
      letI := ab.addCommGroup g
      RelPoint.post (T (ℓ ^ (k + 2))) (T_comp (ℓ ^ (k + 2))) x
        = RelPoint.post (T ℓ) (T_comp ℓ)
              (RelPoint.post (T (ℓ ^ (k + 1))) (T_comp (ℓ ^ (k + 1))) x)
            - ℓ • RelPoint.post (T (ℓ ^ k)) (T_comp (ℓ ^ k)) x) ∧
  -- (4) the moduli recipe at primes `ℓ ∤ N` (the original body)
  (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N →
    ∀ (d : Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (m : ℕ)
      (dq : Fin m → Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
      (iso : ∀ k, IsGamma1Isogeny N ℓ d (dq k)),
      -- the kernels are pairwise distinct on `ℚ̄`-points
      (∀ k k' : Fin m,
        (∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
          RelPoint.LiesIn (iso k).ker.ι x ↔ RelPoint.LiesIn (iso k').ker.ι x) → k = k') →
      -- and they exhaust the cyclic subgroups of order `ℓ`
      (∀ D : CyclicSubgroupOfOrder d.ab ℓ, ∃ k : Fin m,
        ∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
          RelPoint.LiesIn D.ι x ↔ RelPoint.LiesIn (iso k).ker.ι x) →
      letI := ab.addCommGroup (specAlgClos ℚ)
      RelPoint.post (T ℓ) (T_comp ℓ)
          (jac.aj (specAlgClos ℚ)
            (RelPoint.post jY H.comm (H.coarse.classify (specAlgClos ℚ) d)))
        = ∑ k : Fin m, jac.aj (specAlgClos ℚ)
            (RelPoint.post jY H.comm (H.coarse.classify (specAlgClos ℚ) (dq k))))

/-- **EICHLER–SHIMURA for `Γ₁(N)`, as a datum: the Hecke-isotypic
decomposition of `J_1(N)`** (new 2026-07-28) — the `Γ₁` counterpart of
`X0.lean`'s `IsHeckeIsotypicDecomposition`, field for field, with the one
change the nebentypus forces.

`J_1(N)` is `ℚ`-isogenous to a product `∏ A_i` in which each factor is cut
out by ONE system of Hecke eigenvalues.  Written, as in `X0.lean`, as a
family of quotient maps `u i : J ⟶ A i` with finite joint kernel on
rational points, because the product of abelian schemes is not available
in this development and is not needed: "the map to the product is an
isogeny" IS `finite_ker`.

**THE ONE CHANGE FROM THE `Γ₀` STRUCTURE, and why it is forced.**  A
factor of `J_1(N)` is labelled by an eigenform of `S₂(Γ₁(N))`, and such a
form carries a NEBENTYPUS: `S₂(Γ₁(N)) = ⊕_χ S₂(N, χ)`.  So the label is a
pair — a character `neben i` and a form `form i` — rather than a bare
form, and `cover` quantifies over `χ` as well.  Dropping `neben` and
hardwiring `χ = 1` would make `isEigen` and `cover` speak only about the
`Γ₀`-part of `S₂(Γ₁(N))`, i.e. would let a decomposition ignore every
factor with nontrivial nebentypus — which at `N = 25` is EVERY factor,
since `S₂(Γ₀(25)) = 0` while `dim S₂(Γ₁(25)) = 12`.  That is the same
falsification the module docstring records for `IsWeightTwoEigenformOn`.

**WHY IT IS TRUE.**  Exactly as in the `Γ₀` case: take `idx` to be, for
each newform `g` of each level `M ∣ N` (of any nebentypus), one copy per
degeneracy map, with `A` the modular abelian variety `A_g` and `u` the
corresponding optimal quotients `J_1(N) ↠ A_g`.  Those cut out
everything, which is `finite_ker`; labelling the copies by the eigenforms
of `S₂(Γ₁(N))` lying above `g` gives `cover`; `isotypic` holds because
`T_n` acts on `A_g` through `a_n(g)`, and `integral` is Shimura's theorem
that the `a_n` are algebraic integers.

**WHY `isotypic` IS RESTRICTED TO `n` COPRIME TO `N`.**  It is FALSE for
`n ∣ N`, for the reason `X0.lean` records: a `p`-stabilization and its
newform share every `a_n` with `(n, N) = 1` but not `a_p`, and `U_p` is
not semisimple on the old part.  The anemic Hecke algebra is the part
that descends.

**DEGENERACY AUDIT.**  Inherited verbatim from the `Γ₀` structure and
still valid: `cover` makes `idx` empty only when `S₂(Γ₁(N))` has no
eigenform at all (and then `J_1(N)` is trivial), and `isotypic` kills the
residual "one factor, `A = J`, `u = 𝟙`" witness, since two eigenforms
differing at some `a_n` with `(n, N) = 1` have coprime minimal
polynomials, so annihilating both on the same `J` already forces the
conclusion.

**THE CRUX — `T` USED TO BE UNPINNED, AND SINCE 2026-07-29 IT IS NOT.**
This paragraph previously read "`T` is an ARBITRARY family of
endomorphisms; nothing here says it is the family of genuine Hecke
correspondences", and sent the reader to
`isTorsion_factor_of_heckeIsotypic_gamma1` below for the `N = 37`
eigen-system counterexample.  The field `heckeModuli` now carries the
missing pin: `T ℓ` acts on Abel–Jacobi images by
`(E, P) ↦ ∑_D (E/D, P + D)` at every prime `ℓ ∤ N`.  See the subsection
heading above `IsGamma1Isogeny`, and `X0.lean`'s
`IsHeckeIsotypicDecomposition`, whose `heckeModuli` field this mirrors
field for field.

Three consequences, in decreasing order of how much they matter, and
they are the `Γ₀` ones transposed:

* the `N = 37` eigen-system swap **no longer inhabits this structure**,
  so `isTorsion_factor_of_heckeIsotypic_gamma1`'s "why the hypothesis is
  the whole of `hL`" section is superseded;
* sharpening that leaf to the single value `L(form i, 1) ≠ 0` is
  therefore UNBLOCKED on the `Γ₁` side as well — it was the one half of
  the sharpening still blocked after `X0.lean`'s pin landed on
  2026-07-28.  It is deliberately NOT done in the edit that lands the
  pin: two individually-correct edits to one leaf have made a statement
  FALSE in this development before, and the sharpening is a cut-level
  repair that deserves its own faithfulness audit;
* `heckeModuli` makes this structure strictly harder to produce, and
  that price is paid in the two leaves below that construct it —
  `exists_heckeAction_isotypicQuotients_gamma1` and
  `exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1`.  Note
  that the same field also REMOVES the reason those two had to be cut
  differently from `X0.lean`'s three: the `Γ₁` factor-building leaf was
  forced to quantify `T` existentially precisely because there was no pin
  to make a `T`-as-hypothesis form non-vacuous, and there now is one.
  Re-unifying the two cuts is a further refactor and is not done here.

**What the pin still does not do**: it says nothing about `T n` for `n`
not prime or `n ∣ N`, nothing about the diamond operators, and it does
not by itself prove `T` unique — see the last paragraph of the
subsection heading. -/
structure IsHeckeIsotypicDecompositionGamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) where
  /-- the Hecke operators `T_n`, as endomorphisms of `J_1(N)` -/
  T : ℕ → (J ⟶ J)
  /-- they are endomorphisms over the base -/
  T_comp : ∀ n, T n ≫ jstr = jstr
  /-- they are homomorphisms -/
  T_add : ∀ n, IsAdditiveOn ab ab (T n) (T_comp n)
  /-- **they are the genuine Hecke correspondences** — `T ℓ` acts on
  Abel–Jacobi images by `(E, P) ↦ ∑_D (E/D, P + D)` at every prime
  `ℓ ∤ N` (added 2026-07-29; this is what excludes the `N = 37`
  eigen-system swap, and it is the `Γ₁` counterpart of
  `IsHeckeIsotypicDecomposition.heckeModuli`).  `h.some` is the choice of
  compactification datum forced by `h` being a `Prop`-truncation here
  where `X0.lean`'s structure carries the datum; the alternatives, and
  why a universal quantifier over the datum would risk emptiness, are
  audited on `IsModularHeckeActionGamma1`. -/
  heckeModuli : IsModularHeckeActionGamma1 N h.some jac T T_comp
  /-- the index set of the isogeny factors -/
  idx : Type
  /-- there are finitely many factors -/
  fintypeIdx : Fintype idx
  /-- the factors -/
  A : idx → Scheme.{0}
  /-- their structure morphisms -/
  astr : ∀ i, A i ⟶ SpecQ
  /-- each factor is an abelian scheme over `ℚ` -/
  abA : ∀ i, AbelianSchemeStruct (astr i)
  /-- the optimal quotient maps -/
  u : ∀ i, J ⟶ A i
  /-- they are morphisms over the base -/
  u_comp : ∀ i, u i ≫ astr i = jstr
  /-- they are homomorphisms -/
  u_add : ∀ i, IsAdditiveOn ab (abA i) (u i) (u_comp i)
  /-- they are surjective; this is what bounds the rank of a factor by
  the rank of `J_1(N)` -/
  u_surj : ∀ i, AlgebraicGeometry.Surjective (u i)
  /-- the nebentypus of the eigenform labelling the factor — the field
  that has no `Γ₀` counterpart -/
  neben : idx → DirichletCharacter ℂ N
  /-- the eigenform labelling the factor -/
  form : idx → CuspForm (Gamma1GL N) 2
  /-- its `q`-expansion -/
  coeff : idx → (ℕ → ℂ)
  /-- the labels really are eigenforms of `S₂(Γ₁(N))`, of the recorded
  nebentypus -/
  isEigen : ∀ i, IsWeightTwoEigenformOn (Gamma1GL N) N (neben i) (form i) (coeff i)
  /-- the Hecke action descended to the factor -/
  S : ∀ i, ℕ → (A i ⟶ A i)
  /-- over the base -/
  S_comp : ∀ i n, S i n ≫ astr i = astr i
  /-- homomorphisms -/
  S_add : ∀ i n, IsAdditiveOn (abA i) (abA i) (S i n) (S_comp i n)
  /-- `u i` is a map of Hecke modules: `u i ∘ T n = S i n ∘ u i` -/
  equivariant : ∀ i n, T n ≫ u i = u i ≫ S i n
  /-- the Hecke eigenvalues are algebraic integers (Shimura); without
  this `minpoly ℤ (coeff i n)` would be `0` and `isotypic` vacuous -/
  integral : ∀ i n, IsIntegral ℤ (coeff i n)
  /-- **`A i` is isotypic for the eigenvalue system `coeff i`**: for `n`
  coprime to `N`, the descended `T n` is annihilated by the minimal
  polynomial of `coeff i n`, read on relative points over every base -/
  isotypic : ∀ (i : idx) (n : ℕ), Nat.Coprime n N →
    ∀ {T' : Scheme.{0}} (g : T' ⟶ SpecQ) (x : RelPoint (astr i) g),
      letI := (abA i).addCommGroup g
      ∑ k ∈ Finset.range ((minpoly ℤ (coeff i n)).natDegree + 1),
        (minpoly ℤ (coeff i n)).coeff k •
          ((fun y : RelPoint (astr i) g => RelPoint.post (S i n) (S_comp i n) y)^[k] x) = 0
  /-- **every eigenform of `S₂(Γ₁(N))`, of every nebentypus, labels some
  factor** — the field that makes an empty decomposition unavailable -/
  cover : ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
    IsWeightTwoEigenformOn (Gamma1GL N) N χ f a → ∃ i, coeff i = a
  /-- **the joint kernel on rational points is finite** — i.e. the map to
  the product of the factors is an isogeny, in the one form expressible
  without the product -/
  finite_ker : {x : RelPoint jstr (𝟙 SpecQ) |
      ∀ i, RelPoint.post (u i) (u_comp i) x = (abA i).zero (𝟙 SpecQ)}.Finite

/-! #### The `Γ₁` moduli pin for the Hecke operators — HOISTED ABOVE

**RELEASE-19 MERGE NOTE.**  `IsGamma1Isogeny` and `IsModularHeckeActionGamma1`
were written TWICE, independently, a day apart and in two different places in
this file: on 2026-07-28 here, and on 2026-07-29 in the
`#### The moduli pin for the Hecke operators on `Y_1(N)`` subsection above.  The
two definitions are the same object — they differ only in the name of the level
field (`level` vs `map_sec`) and in a binder name — but two declarations of one
name in one namespace is a `has already been declared` error, and no textual
merge can see it because the regions do not overlap.

The 2026-07-28 pair (the released one, with the fuller docstrings) is kept and
now stands ABOVE, at the earlier subsection's position, because
`IsHeckeIsotypicDecompositionGamma1.heckeModuli` — added on 2026-07-29 — refers
to `IsModularHeckeActionGamma1` and is declared between the two sites.  Nothing
is left here.

The paragraph this subsection used to carry, that
`IsHeckeIsotypicDecompositionGamma1` "does **not** acquire a `heckeModuli` field
here", was true when written and is now STALE: that field exists. -/

/-- **THE `Γ₁` HECKE CORRESPONDENCE, AS A NATURAL FAMILY ON POINTS**
(sorry leaf, new 2026-07-28) — the geometric half of
`exists_modularHeckeAction_gamma1` below, and the `Γ₁` transport of
`X0.lean`'s `exists_heckeCorrespondenceFamily`.

TRUE, and the witness is `c := RelPoint.post (T_ℓ) _ ∘ jac.aj` for the
genuine `T_ℓ`: that family is natural because `aj` is and `RelPoint.post`
commutes with `RelPoint.pre`, it sends `o` to `0` because `aj o = 0` and
`T_ℓ` is a homomorphism, and the recursion clause is the classical
description of `T_ℓ` on divisor classes.

**WHY THE STATEMENT IS ON POINTS AND NOT ON A CORRESPONDENCE SCHEME**,
inherited verbatim from the `Γ₀` leaf: the correspondence `X_1(N, ℓ)` with
its two degeneracy maps, and the trace of a finite flat correspondence on
the functor of points, exist neither here, nor in mathlib at this pin, nor
in `~/cs/FLT`.  The point-level form is writable today and is the exact
input `IsJacobianOf.universal` consumes — which is what makes
`exists_modularHeckeAction_gamma1` below a PROOF rather than a second
leaf.

**WHAT IS `Γ₁`-SPECIFIC HERE, AND IT IS ONLY THE LEVEL STRUCTURE.**  The
`Γ₀` leaf's own "WHAT REMAINS GENUINELY MISSING" paragraph — the quotient
datum over a general base — transfers unchanged, because the obstruction
is the quotient of the CURVE and not of the level structure: once `E/D`
exists as an elliptic scheme, the `Γ₁`-structure on it is `d.pt.sec ≫ map`,
which needs nothing further.  So this leaf is, if anything, marginally
easier than its `Γ₀` sibling, and the two should be taken together by
whoever builds the correspondence.

**AXIS NOT SEARCHED**, recorded so the next owner does not assume it was:
the complex-analytic route, where `c` comes from the action of
`Γ₁(N)`-double cosets on `H₁(Γ₁(N)\ℍ*, ℤ)`.  Everything above is the
algebraic-moduli axis. -/
theorem exists_heckeCorrespondenceFamilyGamma1 (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (H : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    ∃ c : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), RelPoint strX g → RelPoint jstr g,
      (∀ {T' T : Scheme.{0}} (p : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
          (hg : p ≫ g = g') (x : RelPoint strX g),
          c g' (RelPoint.pre p hg x) = RelPoint.pre p hg (c g x)) ∧
        c (𝟙 SpecQ) o = ab.zero (𝟙 SpecQ) ∧
        ∀ (d : Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (m : ℕ)
          (dq : Fin m → Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
          (iso : ∀ k, IsGamma1Isogeny N ℓ d (dq k)),
          (∀ k k' : Fin m,
            (∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
              RelPoint.LiesIn (iso k).ker.ι x ↔ RelPoint.LiesIn (iso k').ker.ι x) → k = k') →
          (∀ D : CyclicSubgroupOfOrder d.ab ℓ, ∃ k : Fin m,
            ∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
              RelPoint.LiesIn D.ι x ↔ RelPoint.LiesIn (iso k).ker.ι x) →
          letI := ab.addCommGroup (specAlgClos ℚ)
          c (specAlgClos ℚ)
              (RelPoint.post jY H.comm (H.coarse.classify (specAlgClos ℚ) d))
            = ∑ k : Fin m, jac.aj (specAlgClos ℚ)
                (RelPoint.post jY H.comm (H.coarse.classify (specAlgClos ℚ) (dq k))) :=
  sorry

/-- **THE HECKE CORRESPONDENCE ACTS ON `J_1(N)`** (**PROVEN 2026-07-28**,
over the single leaf `exists_heckeCorrespondenceFamilyGamma1` above) — the
`Γ₁` transport of `X0.lean`'s PROVEN `exists_modularHeckeAction`, and the
half of `exists_heckeAction_isotypicQuotients_gamma1` that carries the
*construction* of `T_ℓ`.

**THE PROOF is the `Γ₀` one line for line, and none of it is geometry** —
which is the point, and the reason this transport is worth making rather
than leaving the operator layer inside the leaf below:

* `IsJacobianOf.universal`, applied to the natural family `c` supplied by
  the leaf, returns `u : J ⟶ J` with `u ≫ jstr = jstr` and the Albanese
  equation `RelPoint.post u _ ∘ aj = c`;
* `isAdditiveOn_of_post_zero` — relative RIGIDITY, PROVEN in `X0.lean` —
  upgrades `u` to a homomorphism from the single equation
  `RelPoint.post u _ 0 = 0`, which is the leaf's base-point clause read
  through `aj_base` and the Albanese equation.  This is why the leaf does
  not have to say anything about additivity;
* the family `T : ℕ → (J ⟶ J)` is assembled pointwise, taking `u` at the
  primes `ℓ ∤ N` — the only arity `IsModularHeckeActionGamma1` constrains
  — and `𝟙 J` at every other `n`.  `𝟙 J` satisfies `T_comp` and `T_add`,
  and using it at the UNCONSTRAINED arities is legitimate precisely
  because the pin is a statement about primes `ℓ ∤ N` only.

So on the `Γ₁` side too the whole operator-level layer is now formal, and
the open geometric work is exactly the correspondence on points. -/
theorem exists_modularHeckeAction_gamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (H : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    ∃ (T : ℕ → (J ⟶ J)) (T_comp : ∀ n, T n ≫ jstr = jstr),
      (∀ n, IsAdditiveOn ab ab (T n) (T_comp n)) ∧
        IsModularHeckeActionGamma1 N H jac T T_comp := by
  classical
  -- One endomorphism per natural number, with the pin attached at exactly the
  -- arities `IsModularHeckeActionGamma1` constrains: the Albanese image of the
  -- correspondence family at a prime `n ∤ N`, and `𝟙 J` at every other `n`.
  have key : ∀ n : ℕ, ∃ u : J ⟶ J, ∃ hu : u ≫ jstr = jstr,
      IsAdditiveOn ab ab u hu ∧
      (n.Prime → ¬ n ∣ N →
        ∀ (d : Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) (m : ℕ)
          (dq : Fin m → Gamma1Datum N (Spec (CommRingCat.of (AlgebraicClosure ℚ))))
          (iso : ∀ k, IsGamma1Isogeny N n d (dq k)),
          (∀ k k' : Fin m,
            (∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
              RelPoint.LiesIn (iso k).ker.ι x ↔ RelPoint.LiesIn (iso k').ker.ι x) → k = k') →
          (∀ D : CyclicSubgroupOfOrder d.ab n, ∃ k : Fin m,
            ∀ x : RelPoint d.f (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))),
              RelPoint.LiesIn D.ι x ↔ RelPoint.LiesIn (iso k).ker.ι x) →
          letI := ab.addCommGroup (specAlgClos ℚ)
          RelPoint.post u hu
              (jac.aj (specAlgClos ℚ)
                (RelPoint.post jY H.comm (H.coarse.classify (specAlgClos ℚ) d)))
            = ∑ k : Fin m, jac.aj (specAlgClos ℚ)
                (RelPoint.post jY H.comm
                  (H.coarse.classify (specAlgClos ℚ) (dq k)))) := by
    intro n
    by_cases hn : n.Prime ∧ ¬ n ∣ N
    · obtain ⟨c, hnat, hzero, hrec⟩ :=
        exists_heckeCorrespondenceFamilyGamma1 N n hn.1 hn.2 H jac
      obtain ⟨u, ⟨hu, hueq⟩, -⟩ := jac.universal ab c hnat hzero
      -- the Albanese equation, read as an equation of relative points
      have hpost : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (x : RelPoint strX g),
          RelPoint.post u hu (jac.aj g x) = c g x := fun g x =>
        Subtype.ext (hueq g x).symm
      refine ⟨u, hu, ?_, ?_⟩
      · -- relative rigidity: `u` sends `0` to `0`, hence is a homomorphism
        refine isAdditiveOn_of_post_zero ab ab hu ?_
        rw [← jac.aj_base, hpost (𝟙 SpecQ) o, hzero, jac.aj_base]
      · intro _ _ d m dq iso hinj hsurj
        rw [hpost (specAlgClos ℚ) _]
        exact hrec d m dq iso hinj hsurj
    · exact ⟨𝟙 J, Category.id_comp jstr, fun x y => by
        simp only [RelPoint.post, Category.comp_id, Subtype.coe_eta],
        fun hp hd => absurd ⟨hp, hd⟩ hn⟩
  choose v v_comp v_add v_pin using key
  -- the multiplicative extension: it agrees with `v` at the primes `ℓ ∤ N`, so it
  -- inherits the moduli recipe, and it satisfies the three anemic relations.
  -- `exists_anemicHeckeExtension` (`X0.lean`) mentions no level structure, so the
  -- `Γ₀` repair of 2026-07-28 transports here verbatim.
  obtain ⟨T, T_comp, T_add, hTv, hT1, hTmul, hTrec⟩ :=
    exists_anemicHeckeExtension N ab v v_comp v_add
  refine ⟨T, T_comp, T_add, hT1, hTmul, hTrec, ?_⟩
  intro ℓ hℓ hℓN d m dq iso hinj hsurj
  have hpostℓ : ∀ {T' : Scheme.{0}} {g : T' ⟶ SpecQ} (y : RelPoint jstr g),
      RelPoint.post (T ℓ) (T_comp ℓ) y = RelPoint.post (v ℓ) (v_comp ℓ) y := by
    intro T' g y
    exact Subtype.ext (by show y.1 ≫ T ℓ = y.1 ≫ v ℓ; rw [hTv ℓ hℓ hℓN])
  rw [hpostℓ]
  exact v_pin ℓ hℓ hℓN d m dq iso hinj hsurj

/-- **SHIMURA'S `A_f` FOR `Γ₁(N)`: EVERY WEIGHT-TWO EIGENFORM OF LEVEL `N`
AND ANY NEBENTYPUS CUTS OUT AN ISOTYPIC QUOTIENT OF `J_1(N)`** (sorry leaf,
new 2026-07-28) — the "BUILD one factor" half of
`exists_heckeAction_isotypicQuotients_gamma1` below, and the `Γ₁` transport
of `X0.lean`'s `exists_isotypicQuotient_of_isWeightTwoEigenform`.

TRUE.  For a NEWFORM `g` of level `M ∣ N` and nebentypus `χ` this is
Shimura §7.5: `I_g := ker(𝕋 → O_g)` is the annihilator ideal of the
eigen-system and `A_g := J_1(M)/I_g J_1(M)` is an abelian variety over `ℚ`
of dimension `[K_g : ℚ]` receiving a surjection from `J_1(M)`, on which
`T_n` acts as multiplication by `a_n(g)`; composing with a degeneracy map
`J_1(N) ↠ J_1(M)` gives the surjection from `J_1(N)`.  For a general
eigenform — a stabilization or an oldform — the ANEMIC system equals that
of its underlying newform, and `isotypic` quantifies only over `n` coprime
to `N`, so the same `A_g` serves.  Diamond–Shurman §6.6 (stated for
`X_1(N)` in the source); Cornell–Silverman–Stevens Ch. V.

* `integral` is Shimura's theorem that the `a_n` are algebraic integers,
  and it is the one field with a purely geometric proof available here:
  `a_n` is an eigenvalue of an endomorphism of an abelian variety.
* `nontriv` is `dim A_g = [K_g : ℚ] ≥ 1`.

**`hmod` IS LOAD-BEARING — WITHOUT IT THIS LEAF IS FALSE**, and this is the
whole reason the pin above had to be built before the cut could be made.
Take `T n := 𝟙 J`.  Every other hypothesis still holds and the conclusion
fails: `equivariant` forces `S n = 𝟙 A` on the image of the surjection
`u`, hence `S n = 𝟙 A`; `isotypic` then demands that `minpoly ℤ (a n)`
annihilate the IDENTITY on `A`, i.e. `P(1) • x = 0` at every point, which
for `nontriv`-nontrivial `A` forces `minpoly ℤ (a n) (1) = 0`, i.e.
`a n = 1` for every `n` coprime to `N` — false already at `N = 11`,
`a₂ = −2`.  This is exactly the refutation
`IsHeckeIsotypicDecompositionGamma1`'s docstring records, and it is why
the leaf below quantifies `T` existentially: this leaf may take `T` as a
hypothesis ONLY because `hmod` accompanies it.

**`hN : N ≠ 0` IS LOAD-BEARING — WITHOUT IT THIS LEAF IS FALSE**, and the
witness is `X0.lean`'s, transferred a fortiori.  At level `0` every prime
divides `N`, so `IsWeightTwoEigenformOn (Gamma1GL 0) 0 χ f a`'s `hecke`
recursion is VACUOUS and the nebentypus is unconstrained; the
transcendental system `a (2 ^ k) = π ^ k`, `a n = 0` otherwise, carried by
`g τ = ∑_{k ≥ 1} π ^ k q ^ (2 ^ k)` (convergent on all of `ℍ` because
`2 ^ k` outruns `π ^ k`), is an admissible eigen-system, and
`IsIsotypicQuotient.integral` fails outright for it.  `Gamma1GL 0` is
smaller than `Gamma0GL 0` — it is `⟨T⟩` without `−I` — so the witness
transfers a fortiori.

**THE HONEST CAVEAT ON `hmod`, and it is a graceful degradation.**  The
non-vacuity of `IsModularHeckeActionGamma1` as a Lean statement is not
proven (see its docstring: `IsGamma1Isogeny` is not yet known to be
inhabited at the scheme level).  Were it formally vacuous, `hmod` would
carry no information and this leaf would be exactly as hard as the
undecomposed node `exists_heckeAction_isotypicQuotients_gamma1` and no
harder.  So the cut cannot make anything worse, and nothing false is
asserted either way.

**WHAT REMAINS GENUINELY MISSING**, re-checked 2026-07-28 and identical to
the `Γ₀` list plus one: no Hecke algebra acting on a Jacobian, no `A_g`,
no old/new decomposition of `S₂(Γ₁(N))`, and no isogeny theory for
abelian SCHEMES here (`Modularity/AbelianSchemeIsogeny.lean` supplies
`[n]` and its flatness, nothing more) — in this project, in mathlib at
this pin, or in `~/cs/FLT`.  The `Γ₁`-specific extra is only the
nebentypus decomposition of `S₂(Γ₁(N))` under `(ℤ/N)ˣ`, and this leaf
receives `χ` rather than having to produce that decomposition.

## ⚠ FALSITY AUDIT — REPAIRED 2026-07-30; THE STATEMENT BELOW IS NOW TRUE

**The audit that follows was CORRECT and is kept verbatim as the record of why
`IsModularHeckeActionGamma1` has the shape it now has.**  Its prescribed repair
has been carried out: the pin carries the three anemic relations as of
2026-07-30, so `hmod` now constrains `T` at every `n` coprime to `N`, the arity
gap is closed, and both witnesses below are excluded.  Nothing in THIS
statement changed — only its hypothesis became stronger.

**ONE HALF OF THE PRESCRIPTION WAS ALREADY STALE WHEN IT WAS WRITTEN, and a
reader who followed it literally would have duplicated clauses.**  The audit
says to add the relations "to `IsModularHeckeAction` and
`IsModularHeckeActionGamma1`".  `IsModularHeckeAction` (`X0.lean`) **already
carried them** — they are clauses (1)–(3) of its body, added 2026-07-28 in the
`Γ₀` repair the audit itself cites — so only the `Γ₁` side was outstanding, and
the change was a TRANSPORT rather than a two-sided design decision.  Verified by
reading both definitions on 2026-07-30.

**AND THE PREDICTED COST DID NOT MATERIALISE.**  The audit expected
`exists_modularHeckeAction` and `exists_modularHeckeAction_gamma1` to "revert to
leaves, since `𝟙 J` off the pinned arities no longer satisfies the pin".  Neither
did: `exists_anemicHeckeExtension` (`X0.lean`, itself a sorry leaf, and stated
with no level structure whatever — it takes only `N`, `ab` and the family) is the
multiplicative extension that repairs the junk arities, and the `Γ₀` proof had
already been rewritten through it.  `exists_modularHeckeAction_gamma1` now goes
through the same call, so it is still PROVEN and the frontier does not grow.

The audit as originally recorded follows.

The caveat above ("nothing false is asserted either way") is **wrong**, and it is
wrong for a reason discovered on the `Γ₀` side *after* this cut was written.  The
`Γ₁` transport inherited the `Γ₀` defect verbatim.

**The defect is an ARITY GAP.**  `IsModularHeckeActionGamma1` is
`∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → …` — it constrains `T` at **primes `ℓ ∤ N` only**.
`IsIsotypicQuotient.isotypic` and `.equivariant` constrain `T n` at **every `n`
coprime to `N`**.  `T` is an INPUT here, so a caller may hand over a family that
is genuine where `hmod` can see and junk where it cannot — and
`exists_modularHeckeAction_gamma1` **constructs exactly such a family**: its own
proof takes `𝟙 J` at every non-prime arity.

**Witness** (the `Γ₀` one, which transfers because nothing in it mentions the
level structure).  At `n = 1`: `1` is not prime, so `hmod` says nothing about
`T 1`; take `T 1 := 0`.  `minpoly ℤ (1 : ℂ) = X − 1`, so `isotypic` at `n = 1`
forces the quotient map `u` to satisfy `S 1 = id` on its image while
`equivariant` forces `u = 0`, contradicting `nontriv`.  So `IsIsotypicQuotient`
is uninhabited at that `T` and the conclusion `Nonempty …` is false.  A
level-dependent witness is `N = 37`, `n = 4`, using the family
`exists_modularHeckeAction_gamma1` itself produces.

**Do NOT prove this leaf, and do not build on it.**  *(That instruction is
DISCHARGED — see the header above.  It stood from the release-18 merge until
2026-07-30.)*  The repair is the one
prescribed for the `Γ₀` cluster and must be made on BOTH sides by ONE owner: add
to `IsModularHeckeAction` and `IsModularHeckeActionGamma1` the relations that
determine an anemic system from its primes —
`T 1 = 𝟙 J`, `Nat.Coprime m n → T (m * n) = T m ≫ T n`, and
`T (ℓ^(k+2)) = T ℓ ≫ T (ℓ^(k+1)) − ℓ • T (ℓ^k)`.  All the affected statements
then become true and no consumer's statement changes; the honest cost is that
`exists_modularHeckeAction` and `exists_modularHeckeAction_gamma1` revert to
leaves, since `𝟙 J` off the pinned arities no longer satisfies the pin.  The
cheaper alternative — restricting `IsIsotypicQuotient.isotypic`/`.equivariant`
to primes `ℓ ∤ N` — is a change to a structure shared with `X0.lean` and must
likewise be made once, for both sides.

## RECUT 2026-07-30 ALONG `integral` — the `Γ₀` recut of the same day, transported

This statement is UNCHANGED and every consumer calls it exactly as before; it is
now the one-line assembly of the two leaves immediately below.  `X0.lean` split
`exists_isotypicQuotient_of_isWeightTwoEigenform` along
`IsIsotypicQuotient.integral` on 2026-07-30, into
`isIntegral_coeff_of_isWeightTwoEigenform` (Shimura's algebraicity theorem, a
statement about the coefficient SEQUENCE with no scheme in it) and
`exists_isotypicQuotient_of_isIntegral` (the geometry, receiving algebraicity as
`hint`).  The `Γ₁` twins are `isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1`
and `exists_isotypicQuotient_of_isIntegral_gamma1`.

**Why transport it rather than leave the two sides divergent.**  `integral` is a
field of `IsIsotypicQuotient`, and that structure is REUSED VERBATIM here — so
the obligation being split off is literally the same obligation on both sides,
and the `Γ₁` geometric half is then literally the `Γ₁` twin of `X0.lean`'s.
Leaving one side split and the other not is how the two files drift into rival
cuts of one node, which this file has paid for before.

**The algebraicity leaf CANNOT be shared with `X0.lean`'s, and must not be
stated shape-free.**  `isIntegral_coeff_of_isWeightTwoEigenform` is about
`IsWeightTwoEigenform N f a` with `f : CuspForm (Gamma0GL N) 2`; the `Γ₁` form
carries a nebentypus and its coefficients generate `ℚ(χ)` rather than a
subfield of `ℝ`, so no instance of the `Γ₀` statement implies it.  Nor may the
`G` of `IsWeightTwoEigenformOn` be left free: at `G = ⟨T⟩` the `qExpansion`
fields still hold, `hecke`/`atkin` are the level-`0` degeneracy, and the
transcendental witness `a (2 ^ k) = π ^ k` recorded above satisfies every field
while `IsIntegral ℤ (a 2)` fails.  So `G := Gamma1GL N` is load-bearing in the
leaf below, exactly as `hN : N ≠ 0` is. -/
theorem isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1 (N : ℕ) (_hN : N ≠ 0)
    (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ)
    (_hf : IsWeightTwoEigenformOn (Gamma1GL N) N χ f a) (n : ℕ) :
    IsIntegral ℤ (a n) :=
  sorry

/-- **SHIMURA'S `A_f` FOR `Γ₁(N)`, GIVEN ALGEBRAICITY OF THE EIGENVALUES**
(sorry leaf, NEW 2026-07-30) — the GEOMETRIC half of
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` below, and the `Γ₁`
twin of `X0.lean`'s `exists_isotypicQuotient_of_isIntegral`.

The mathematics, the load-bearing hypotheses (`hmod`, `hN`, and — through `jac`
and `H` — the identification of `J` as the Jacobian of `X_1(N)`), and the
inventory of what is still missing are all recorded on the assembly below and
are not repeated here.  What this leaf does NOT have to do, and the undivided
statement did, is produce a field about `ℂ`-valued eigenvalues in the middle of
building an abelian variety: `hint` is handed to it.

`hint` is stated for EVERY `n`, not merely for `n` coprime to `N`, because
`IsIsotypicQuotient.integral` is — `minpoly ℤ (a n) = 0` for a non-integral
`a n` would degenerate `isotypic` to `(0 : ℤ) • x = 0` at that `n`, and
`isotypic`'s own restriction to `Nat.Coprime n N` is a statement about which
`T n` are controlled, not about which `a n` are algebraic. -/
theorem exists_isotypicQuotient_of_isIntegral_gamma1 (N : ℕ) (_hN : N ≠ 0)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (H : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) (T : ℕ → (J ⟶ J))
    (T_comp : ∀ n, T n ≫ jstr = jstr) (_T_add : ∀ n, IsAdditiveOn ab ab (T n) (T_comp n))
    (_hmod : IsModularHeckeActionGamma1 N H jac T T_comp)
    (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ)
    (_hf : IsWeightTwoEigenformOn (Gamma1GL N) N χ f a)
    (_hint : ∀ n, IsIntegral ℤ (a n)) :
    Nonempty (IsIsotypicQuotient ab T N a) :=
  sorry

/-- **SHIMURA'S `A_f` FOR `Γ₁(N)`: EVERY WEIGHT-TWO EIGENFORM OF LEVEL `N` AND
ANY NEBENTYPUS CUTS OUT AN ISOTYPIC QUOTIENT OF `J_1(N)`** (**PROVEN
2026-07-30** over the two leaves immediately above; a sorry leaf from
2026-07-28 until then).  The statement is unchanged — every consumer calls it
exactly as before — and this declaration is now the one-line assembly that
hands Shimura's algebraicity theorem to the geometry.  The mathematics, the
level-`0` falsity witness, the `hmod` refutation, the discharged FALSITY AUDIT
and the inventory of what is still missing are all in the long docstring above
this cluster; see the two leaves for what each half owns. -/
theorem exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1 (N : ℕ) (hN : N ≠ 0)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (H : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) (T : ℕ → (J ⟶ J))
    (T_comp : ∀ n, T n ≫ jstr = jstr) (T_add : ∀ n, IsAdditiveOn ab ab (T n) (T_comp n))
    (hmod : IsModularHeckeActionGamma1 N H jac T T_comp)
    (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (Gamma1GL N) N χ f a) :
    Nonempty (IsIsotypicQuotient ab T N a) :=
  exists_isotypicQuotient_of_isIntegral_gamma1 N hN H jac T T_comp T_add hmod χ f a hf
    (fun n => isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1 N hN χ f a hf n)

/-- **SHIMURA'S `A_f` FOR `Γ₁(N)`, TOGETHER WITH THE HECKE ACTION IT ACTS
THROUGH** (**PROVEN 2026-07-28**, over the two leaves
`exists_modularHeckeAction_gamma1` and
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` immediately
above; a bare sorry leaf from earlier the same day until then) — the
"BUILD the factors" half of
the cut of `exists_heckeIsotypicDecomposition_gamma1` below, and the
`Γ₁` transport of `X0.lean`'s pair
`exists_modularHeckeAction` / `exists_isotypicQuotient_of_isWeightTwoEigenform`.

**`IsIsotypicQuotient` IS REUSED VERBATIM FROM `X0.lean`, NOT MIRRORED.**
That structure is stated over `(ab : AbelianSchemeStruct jstr)`,
`(T : ℕ → (J ⟶ J))`, `N` and the eigen-system `a` alone — it mentions no
compactification, no moduli problem and no congruence subgroup, so there
is nothing `Γ₀`-specific in it to mirror.  `N` enters only through
`Nat.Coprime n N` in its `isotypic` field, which is the same anemic range
the `Γ₁` structure above uses.  This is why the `Γ₁` side of the cut costs
one theorem rather than one theorem plus a 15-field structure.

**WHY THE HECKE ACTION IS PRODUCED IN THIS STATEMENT AND NOT IN A
SEPARATE ONE — the one place this STATEMENT must differ from
`X0.lean`'s.**  On the `Γ₀` side the two halves are separable at the level
of the parent structure because `IsHeckeIsotypicDecomposition.T` is PINNED
by its `heckeModuli` field (`IsModularHeckeAction`, added 2026-07-28).

**⚠ THE NEXT SENTENCE IS STALE AS OF 2026-07-29 — read the correction under
"WHAT IS DELIBERATELY STILL NOT DONE" below before acting on it.**
`IsHeckeIsotypicDecompositionGamma1` **does** now carry a `heckeModuli`
field, and the "WHAT IS NOT PINNED, and it is the crux" heading it points
at no longer exists.  What survives unchanged is the *refutation* in the
rest of the paragraph, and with it the reason THIS statement quantifies `T`
existentially; only the premise about the parent structure has moved.

`IsHeckeIsotypicDecompositionGamma1` carries no such field — see its
docstring, "WHAT IS NOT PINNED, and it is the crux" — so a `Γ₁` leaf
taking a BARE `T` as an input would be **FALSE**, by exactly the
refutation recorded on the `Γ₀` factor leaf: with `T n := 𝟙 J`,
`equivariant` forces `S n = 𝟙 A` on the image of the surjection `u`,
`isotypic` then demands `minpoly ℤ (a n)` to annihilate the identity, and
for `nontriv`-nontrivial `A` that forces `a n = 1` for every `n` coprime
to `N`, which already fails at `N = 11`, `a₂ = −2`.  **Quantifying `T`
existentially is what keeps THIS statement true, and it is why this
statement is the pair of `X0.lean`'s two rather than one of them.  That
has not changed and the statement below is untouched.**

Consequence worth stating, because it is the price of the missing pin:
this leaf is strictly harder than `exists_isotypicQuotient_of_isWeightTwoEigenform`
alone, and closing it would be most of the way to closing that one too.

**THE `Γ₀` COUNTERPART WAS FALSE AND HAS BEEN REPAIRED — 2026-07-30, at
integration.**  This paragraph read "DO NOT 'HARMONISE' THIS LEAF WITH ITS
`Γ₀` COUNTERPART — THAT COUNTERPART IS FALSE", and that is no longer the
state of the tree: `IsModularHeckeAction` (`X0.lean`:38059) now carries
`T 1 = 𝟙 J`, coprime multiplicativity, and the prime-power recursion at
`ℓ ∤ N` as clauses (1)–(3), which pin `T` on exactly the arities the
conclusion inspects — clause (3) at `ℓ = 2`, `k = 0` pins `T 4`, the witness
arity of the refutation below.  So the arity gap is closed and the two `Γ₀`
leaves are no longer refuted.

The refutation is kept in full below because it is the reason the pin has
the shape it has, and because the reasoning generalises: an INPUT `T` whose
pin is narrower than the conclusion's range is false by construction,
whatever the range happens to be today.  What is now stale is only the
instruction: harmonising is no longer forbidden, it is merely unnecessary,
since this leaf's existential `T` needs no pin at all.

An earlier version of this paragraph proposed,
as the repair that would make the two cuts identical, giving
`IsHeckeIsotypicDecompositionGamma1` a `heckeModuli` field over a `Γ₁`
analogue of `IsGamma0Isogeny`, and then taking `T` as a hypothesis here the
way the `Γ₀` leaf does.  **Following that advice would import a falsity.**

The defect is an ARITY GAP, and it is worth stating precisely because it is
invisible unless the two ranges are compared side by side.
`IsModularHeckeAction` pins `T` only at **primes `ℓ` with `ℓ ∤ N`**, whereas
`IsIsotypicQuotient`'s `isotypic` and `equivariant` constrain **every `n`
coprime to `N`**.  Composite `n` coprime to `N` — `n = 4` at `N = 37`, say —
are therefore constrained by the conclusion and left entirely free by the
pin, so a caller may hand over a `T` that is genuine at primes and junk at
composite arities.  Both `exists_isotypicQuotient_of_isWeightTwoEigenform`
and `exists_heckeIsotypicDecomposition_of_modularHeckeAction` WERE FALSE for
that reason, refuted at `N = 37` with a family that
`exists_modularHeckeAction` itself constructs; `a 4 = 1` is forced by the pin
while `37a` has `a₄ = a₂² − 2 = 2`.  As of 2026-07-30 the pin covers `n = 4`
and both are open rather than false — see the paragraph above.

**THIS LEAF IS IMMUNE, AND THE IMMUNITY IS STRUCTURAL RATHER THAN LUCKY.**
`T` is quantified EXISTENTIALLY here and in the sibling below, and the `∃ T`
sits OUTSIDE the `∀ χ f a` — one action serving every factor, chosen by the
prover rather than supplied by a caller.  A prover picks the genuine Hecke
action, which satisfies `isotypic` and `equivariant` at every `n` coprime to
`N` and not merely at primes, so there is no arity at which junk can enter.
This is the same fact as the `T n := 𝟙 J` refutation two paragraphs above,
seen from the other side: unpinned `T` as an INPUT is what makes a statement
false, and unpinned `T` as an OUTPUT is what makes one true.

So if a `Γ₁` moduli pin is built later, the thing to check FIRST is that its
arity range matches `isotypic`/`equivariant` exactly — every `n` coprime to
`N`, not just the primes — or else that the structure's own ranges are
narrowed to match it.  And it must not be combined with any other change to
these statements in the same edit: two individually-correct edits to one
leaf have made a statement false in this development before, which is
precisely what happened on the `Γ₀` side here.

**WHAT CHANGED 2026-07-28 (`flt-lean-333`): THE PROOF, VIA A `Γ₁` PIN
BUILT IN THIS FILE.**  The paragraph that used to stand here concluded
that the `Γ₁` side could not be cut the way the `Γ₀` side is, and
prescribed as the repair "a moduli description of `T_ℓ` on `Y_1(N)` in
terms of `(E, P) ↦ ∑_D (E/D, P + D)`".  That prescription was carried out
— `IsGamma1Isogeny` and `IsModularHeckeActionGamma1` above — so the cut is
now the `Γ₀` one: `exists_modularHeckeAction_gamma1` (PROVEN over the
geometric leaf `exists_heckeCorrespondenceFamilyGamma1`) supplies `T`
together with the pin, `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1`
consumes both, and the assembly below is two `obtain`s.  THIS statement's
own `T` stays existentially quantified and its text is unchanged, so this
statement remains immune.

**⚠ MERGE-TIME FALSITY WARNING, RELEASE 18 — AND IT APPLIES TO THE NEW
SUB-LEAF, NOT TO THIS STATEMENT.**  Making the `Γ₁` cut identical to the
`Γ₀` one also imported the `Γ₀` cut's DEFECT, which was refuted after that
branch was written.  `IsModularHeckeActionGamma1` constrains `T` only at
**primes `ℓ ∤ N`** — its body is `∀ ℓ, ℓ.Prime → ¬ ℓ ∣ N → …`, and
`exists_modularHeckeAction_gamma1`'s proof deliberately takes `𝟙 J` at
every other arity — while `IsIsotypicQuotient`'s `isotypic` and
`equivariant` constrain **every `n` coprime to `N`**.  So
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1`, which takes
`T` and `hmod` as INPUTS, is FALSE for exactly the reason
`exists_isotypicQuotient_of_isWeightTwoEigenform` is: see that leaf's own
FALSITY AUDIT and the `N = 37` / `n = 4` witness.  **Repair the two sides
together, under ONE owner** — add to both pins the relations that
determine an anemic system from its primes (`T 1 = 𝟙 J`,
`Nat.Coprime m n → T (m * n) = T m ≫ T n`,
`T (ℓ^(k+2)) = T ℓ ≫ T (ℓ^(k+1)) − ℓ • T (ℓ^k)`), at the honest cost that
`exists_modularHeckeAction` / `exists_modularHeckeAction_gamma1` revert to
leaves.  Do NOT repair one side alone.

**WHAT IS DELIBERATELY STILL NOT DONE — HALF OF THIS PARAGRAPH IS NOW
STALE** (corrected 2026-07-30).  It used to read "`IsHeckeIsotypicDecomposition
Gamma1` has **not** gained a `heckeModuli` field … the `N = 37`
eigen-system swap therefore still inhabits it".  **The field WAS added, on
2026-07-29**: `heckeModuli : IsModularHeckeActionGamma1 N h.some jac T
T_comp` is a field of that structure, and the swap no longer inhabits it
at the arities the pin reaches.  A note of the form "X does not exist" is
refutable by one grep and this one had gone unrefuted for a day; it is the
class of stale claim this project treats as worse than an open sorry.

What IS still true, and is the whole of what remains here:
`isTorsion_factor_of_heckeIsotypic_gamma1` is UNTOUCHED — it still takes
the full `hL` rather than the sharper `L(D.form i, 1) ≠ 0`, and its own
docstring's claim that the sharpening is blocked "because the structure
has no such field" is stale for the same reason and is corrected there.
The sharpening is a restatement needing its own faithfulness audit, and
the thing that audit must settle is the **ARITY GAP above, not the missing
field**: the pin reaches only primes `ℓ ∤ N`, so a sharpening argument may
only use eigenvalues at primes.  That is enough to separate the `N = 37`
systems — an anemic eigen-system is determined by its values at primes —
but it is an argument to write, not a field to add.  Do not sharpen and
close the arity gap in one edit; two individually-correct edits to one
statement have made a leaf false in this development before.

## ⚠ CORRECTION (2026-07-30) — THAT SHARPENING WAS DONE, AND IT CHANGES WHICH REPAIR IS RIGHT

The paragraph immediately above is **STALE**, and so are the two other places
in this file that say the `Γ₁` structure has no pin (this docstring's "WHY THE
HECKE ACTION IS PRODUCED IN THIS STATEMENT" paragraph, and
`exists_heckeIsotypicDecomposition_gamma1`'s "the `Γ₁` transport is two leaves
rather than three").  `IsHeckeIsotypicDecompositionGamma1.heckeModuli :
IsModularHeckeActionGamma1 N h.some jac T T_comp` was **added on 2026-07-29**
and is in the structure now; the `#### The Γ₁ moduli pin` subsection's own
release-19 merge note already records the field's existence, but nothing
propagated the consequences to the three paragraphs that reason from its
absence.  Verified against the source at this commit, not from prose.

**Consequence 1 — the recorded "one owner, both sides" repair is now the WORSE
of the two options, and it was the better one when it was written.**  The
FALSITY AUDIT on `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1`
offers (a) add the anemic relations `T 1 = 𝟙 J`,
`Nat.Coprime m n → T (m * n) = T m ≫ T n`,
`T (ℓ^(k+2)) = T ℓ ≫ T (ℓ^(k+1)) − ℓ • T (ℓ^k)` to both pins — at the cost of
`exists_modularHeckeAction` / `exists_modularHeckeAction_gamma1` reverting to
leaves — or (b) restrict `IsIsotypicQuotient`'s `isotypic` and `equivariant` to
primes `ℓ ∤ N`, dismissed as "a change to a structure shared with `X0.lean`".
But (b) closes the arity gap on BOTH sides with **no leaf regression at all**,
while (a) costs two proven theorems; and (b)'s shared-structure objection is no
longer a discriminator, because after 2026-07-29 both parent structures pin `T`
through `heckeModuli`, so both sides need the same edit either way.  Whoever
owns `X0.lean`'s `IsIsotypicQuotient` should take (b).

**Consequence 2, and it is not recorded anywhere else: the sibling cut
`exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1` HAS QUIETLY
STOPPED BEING A REDUCTION.**  Its hypothesis `hquot` supplies
`∃ T T_comp, (∀ n, IsAdditiveOn …) ∧ ∀ χ f a, … → Nonempty (IsIsotypicQuotient
ab T N a)` — an **unpinned** `T`.  Its conclusion is
`Nonempty (IsHeckeIsotypicDecompositionGamma1 N h jac)`, which since
2026-07-29 requires a `T` satisfying `heckeModuli`.  So `hquot`'s `T` cannot be
used for the field it was cut out to supply: a prover must build the genuine
Hecke action from scratch anyway, and `hquot` now contributes only the factors.
The leaf is still TRUE — the genuine action satisfies everything — but the
"factors / all factors" split no longer removes the hardest object from it, and
the frontier accounting that treats it as a proper decomposition of
`exists_heckeIsotypicDecomposition_gamma1` is optimistic by one Hecke-action
construction.  Repair (b) does not fix this; matching `hquot`'s conclusion to
the parent's `heckeModuli` field does, and that is a one-line change to this
file that costs nothing.

**Consequence 3 — the "DO NOT HARMONISE" warning below was overtaken by events,
not withdrawn.**  It says that giving `IsHeckeIsotypicDecompositionGamma1` a
`heckeModuli` field *and then* taking `T` as a hypothesis in the factor leaf
"would import a falsity".  Exactly half of that happened: the field was added,
the factor leaf still takes `T` as a hypothesis, and the falsity is indeed
present — which is what the FALSITY AUDIT on that leaf records.  The warning was
right; it was simply not seen by the branch that added the field.

Nothing in this correction is a Lean change, so nothing here can turn the build
red; it is written here rather than in a commit message because a commit message
cannot be maintained and the frontier can.

**`hN : N ≠ 0` IS LOAD-BEARING — WITHOUT IT THIS LEAF IS FALSE**, and the
witness is `X0.lean`'s, unchanged.  At level `0` every prime divides `N`,
so `IsWeightTwoEigenformOn (Gamma1GL 0) 0 χ f a`'s `hecke` recursion is
VACUOUS and the nebentypus is unconstrained; the transcendental system
`a (2 ^ k) = π ^ k`, `a n = 0` otherwise, carried by
`g τ = ∑_{k ≥ 1} π ^ k q ^ (2 ^ k)` (convergent on all of `ℍ` because
`2 ^ k` outruns `π ^ k`), is then an admissible eigen-system, and
`IsIsotypicQuotient.integral` fails outright for it.  `Gamma1GL 0` is
smaller than `Gamma0GL 0` — it is `⟨T⟩` without `−I` — so the witness
transfers a fortiori.  The `N = 0` case is therefore owned by the sibling
below, which receives `hquot` only under `N ≠ 0`.

**`h` AND `jac` ARE LOAD-BEARING** and are not decoration inherited from
the parent: together they say `J` is the Jacobian of the compactified
coarse space of the `Γ₁(N)`-moduli problem.  Drop either and the statement
becomes "some abelian scheme over `ℚ` carries an action with a quotient
cut out by every weight-two eigenform of level `N`", which is false for,
say, an elliptic curve of conductor `11` at `N = 23`.

**WHAT REMAINS GENUINELY MISSING**, re-checked 2026-07-28 and identical to
the `Γ₀` list: no Hecke algebra acting on a Jacobian, no `A_g`, no
old/new decomposition of `S₂(Γ₁(N))`, and no isogeny theory for abelian
SCHEMES here (`Modularity/AbelianSchemeIsogeny.lean` supplies `[n]` and
its flatness, nothing more) — in this project, in mathlib at this pin, or
in `~/cs/FLT`.  The `Γ₁`-specific extra is only the nebentypus
decomposition of `S₂(Γ₁(N))` under `(ℤ/N)ˣ`. -/
theorem exists_heckeAction_isotypicQuotients_gamma1 (N : ℕ) (hN : N ≠ 0)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    ∃ (T : ℕ → (J ⟶ J)) (T_comp : ∀ n, T n ≫ jstr = jstr),
      (∀ n, IsAdditiveOn ab ab (T n) (T_comp n)) ∧
        IsModularHeckeActionGamma1 N h.some jac T T_comp ∧
        ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
          IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
            Nonempty (IsIsotypicQuotient ab T N a) := by
  -- `h` is `Nonempty (IsX1Compactification …)`; the classifying DATUM the pin
  -- needs is `h.some`, which is the SAME choice the decomposition structure's
  -- `heckeModuli` field names — so the pin exported here is the one the
  -- consumer can actually use.  (It used to be recovered by an anonymous
  -- `obtain ⟨H⟩ := h`, which is a different term and would not match.)
  obtain ⟨T, T_comp, T_add, hmod⟩ := exists_modularHeckeAction_gamma1 N h.some jac
  exact ⟨T, T_comp, T_add, hmod, fun χ f a hf =>
    exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1 N hN h.some jac T T_comp T_add hmod
      χ f a hf⟩

/-! ### The level-`0` degeneracy of `Γ₁` Eichler–Shimura

**SETTLED 2026-07-28, and the answer is the unwelcome one.**  The leaf
`exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1` below was
cut carrying the whole `N = 0` obligation, with a heading recording that
— unlike its `Γ₀` sibling — the obligation is NOT discharged by an
emptiness lemma, and naming the check that would settle it: *is
`IsCoarseModuliY1 0 strY` strong enough to contradict `X` being a
curve?*

The check was run.  **It is not.**  `IsCoarseModuliY1` has exactly three
fields — `classify`, `classify_natural`, `universal` — and its own
docstring says so in terms: "bijectivity on geometric points is
deliberately omitted".  There is no clause that can see that the
`ℚ̄`-points of `[Γ₁(0)]` are pairs `(E, P)` with `P` of infinite order;
initiality alone constrains nothing about cardinality.  So the `Γ₀`
route (`isEmpty_of_isCoarseModuliY0_zero`, which needs `Y_0(0) = ∅`) has
no `Γ₁` analogue, and none is reachable from this structure.

**What IS provable is the opposite, and it is what forces the repair
below**: `IsHeckeIsotypicDecompositionGamma1 0 h jac` is EMPTY, for every
`h` and `jac` — `isEmpty_isHeckeIsotypicDecompositionGamma1_zero`.  So at
`N = 0` the leaf's conclusion is `Nonempty ∅`, and the leaf is provable
there ONLY by refuting its geometric hypotheses, which the paragraph
above says cannot be done inside this vocabulary.  A statement in that
position is not "open"; it is a statement no prover can honestly close.
Hence `hN : N ≠ 0` on the leaf, on
`exists_heckeIsotypicDecomposition_gamma1`, and NOT one step further —
see below.

**THE REFUTATION, and note it needs no transcendence.**  The obstruction
is a COUNTING one, which is why it is robust.  `Gamma1 0` is
`{[[1, b], [0, 1]] : b ∈ ℤ} = ⟨T⟩` (mathlib's `Gamma1_mem` at `N = 0`
reads the congruences in `ZMod 0 = ℤ`, i.e. as equations — and note it
does NOT contain `−I`).  For a level-`0` eigen-system:

* `hecke` is VACUOUS, since its hypothesis is `¬ p ∣ 0` and every `p`
  divides `0`.  The nebentypus is therefore unconstrained too, and `1`
  serves.
* `atkin` is NOT vacuous and is the only surviving constraint: `p ∣ 0`
  holds for every prime, so `atkin` says `a (n * p) = a p * a n` at EVERY
  prime — i.e. `a` is completely multiplicative, with the values `a p`
  free.

So `lacunaryTwoCoeff c` below — `c ^ k` at `n = 2 ^ k`, `0` off the
powers of `2` — is admissible for EVERY `c : ℂ`, and these are pairwise
distinct (they differ at `n = 2`, where the value is `c`).  `cover`
demands a factor for each, `fintypeIdx` says there are finitely many
factors, and `ℂ` is infinite.  That is the whole proof.

**Why the counting argument and not the integrality one.**  The sibling
`exists_heckeAction_isotypicQuotients_gamma1`'s `hN` is justified by a
transcendental system breaking `IsIsotypicQuotient.integral`, and that
argument would work here too against `integral`.  It is not used, for two
reasons: mathlib at this pin has no transcendence of `π` (checked
2026-07-28 — `Real.transcendental_pi` does not exist), and the counting
argument does not care, since it never evaluates a coefficient beyond
`n = 2`.  Robustness: the refutation survives DELETING the `integral`
field, and survives replacing `ℂ` by any infinite coefficient ring.

**WHERE THE `N = 0` CASE ACTUALLY GOES, and why the cascade stops.**  It
is discharged one level up, at
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1`, whose analytic
hypothesis `hL` is CONTRADICTORY at `N = 0` —
`not_lFunctionHypothesis_gamma1GL_zero`.  Take `c = 8`: the Dirichlet
series `∑ a n n^{-s}` is `∑_k 8^k 2^{-ks}`, whose terms have modulus
`2^{k(3 − re s)} ≥ 1` throughout the strip `2 < re s < 3`, so it is not
summable there and `LSeries` takes its junk value `0`.  `IsLFunctionOf`
then forces the entire `L` to vanish on a nonempty open set, hence
identically (the same identity-theorem step as
`isLFunctionOf_apply_eq`), hence `L 1 = 0` against `L 1 ≠ 0`.

That is why `hN` is added to exactly two statements and stops there:
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1` keeps its signature, and
so the SHAPE-FREE wrapper
`isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` — shared with
`Γ₀`, and with consumers outside this file — is untouched.

**COROLLARY WORTH RECORDING FOR THE `Γ₀` SIDE.**  Nothing in the counting
argument is `Γ₁`-specific except which group carries the cusp form.  The
same `atkin`-at-every-prime degeneracy holds for `Gamma0GL 0`, so
`IsHeckeIsotypicDecomposition 0 h jac` is presumably empty too; there it
does no damage only because `isEmpty_of_isCoarseModuliY0_zero`
independently kills the hypotheses.  A `Γ₀` reader should not read that
lemma as evidence that the `Γ₀` structure is inhabited at `N = 0`. -/

/-- **The completely multiplicative eigen-system supported on the powers
of `2`**: `lacunaryTwoCoeff c (2 ^ k) = c ^ k`, and `0` at every `n` that
is not a power of `2`.

`2 ^ Nat.log 2 n = n` is the power-of-two test (`Nat.log 2 0 = 0` and
`2 ^ 0 = 1 ≠ 0`, so `n = 0` is correctly sent to `0`), and `Nat.log 2 n`
is then the exponent.

Used ONLY as the level-`0` witness of the section docstring above: at
`N = 0` the `hecke` field of `IsWeightTwoEigenformOn` is vacuous and
`atkin` reduces to complete multiplicativity, which this satisfies for
every `c`. -/
noncomputable def lacunaryTwoCoeff (c : ℂ) (n : ℕ) : ℂ :=
  if 2 ^ Nat.log 2 n = n then c ^ Nat.log 2 n else 0

theorem lacunaryTwoCoeff_zero (c : ℂ) : lacunaryTwoCoeff c 0 = 0 := by
  simp [lacunaryTwoCoeff]

theorem lacunaryTwoCoeff_one (c : ℂ) : lacunaryTwoCoeff c 1 = 1 := by
  simp [lacunaryTwoCoeff]

theorem lacunaryTwoCoeff_pow (c : ℂ) (k : ℕ) : lacunaryTwoCoeff c (2 ^ k) = c ^ k := by
  simp [lacunaryTwoCoeff, Nat.log_pow (b := 2) (by norm_num)]

/-- The value at `n = 2` is `c`; this is what makes the family
`c ↦ lacunaryTwoCoeff c` injective, and so what the counting refutation
runs on. -/
theorem lacunaryTwoCoeff_two (c : ℂ) : lacunaryTwoCoeff c 2 = c := by
  simpa using lacunaryTwoCoeff_pow c 1

theorem lacunaryTwoCoeff_eq_zero_of_odd_prime_dvd {c : ℂ} {m : ℕ} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ m) : lacunaryTwoCoeff c m = 0 := by
  rw [lacunaryTwoCoeff, if_neg]
  intro hpow
  have hd : p ∣ 2 ^ Nat.log 2 m := by rw [hpow]; exact hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (Nat.Prime.dvd_of_dvd_pow hp hd))

/-- **Complete multiplicativity at every prime** — which is exactly the
`atkin` field of `IsWeightTwoEigenformOn` at level `0`, since `p ∣ 0`
holds for every `p`. -/
theorem lacunaryTwoCoeff_atkin (c : ℂ) (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 0 < n) :
    lacunaryTwoCoeff c (n * p) = lacunaryTwoCoeff c p * lacunaryTwoCoeff c n := by
  rcases eq_or_ne p 2 with rfl | hp2
  · have hlog : Nat.log 2 (n * 2) = Nat.log 2 n + 1 :=
      Nat.log_mul_base (by norm_num) hn.ne'
    rw [lacunaryTwoCoeff_two]
    simp only [lacunaryTwoCoeff, hlog]
    by_cases hcond : 2 ^ Nat.log 2 n = n
    · rw [if_pos hcond, if_pos (by rw [pow_succ, hcond]), pow_succ]
      ring
    · rw [if_neg hcond, if_neg ?_, mul_zero]
      intro hpow
      rw [pow_succ] at hpow
      exact hcond (Nat.eq_of_mul_eq_mul_right (by norm_num) hpow)
  · rw [lacunaryTwoCoeff_eq_zero_of_odd_prime_dvd hp hp2 ⟨n, mul_comm n p⟩,
      lacunaryTwoCoeff_eq_zero_of_odd_prime_dvd hp hp2 dvd_rfl, zero_mul]

section LacunaryLevelZero

open Filter Asymptotics MeasureTheory UpperHalfPlane OnePoint
open scoped ModularForm

/-- The lacunary `q`-series `∑_{k ≥ 0} c^k q^{2^k}` as a function of `z : ℂ`,
with `q = exp (2πiz)`.  Written on `ℂ` rather than on `ℍ` so that
periodicity, holomorphy and decay are all statements about one honest
complex function. -/
noncomputable def lacunaryQSeries (c : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, lacunaryTwoCoeff c (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * z)

lemma norm_lacunaryQTerm (c : ℂ) (n : ℕ) (z : ℂ) :
    ‖lacunaryTwoCoeff c (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * z)‖
      = ‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * (n + 1) * z.im)) := by
  rw [norm_mul, Complex.norm_exp]
  congr 1
  simp

/-- The doubly-exponential decay that makes the series converge for EVERY
`c`, however large: the ratio of consecutive terms is `‖c‖ · r^{2^k}` with
`r = e^{-2πy} < 1`, which tends to `0`. -/
lemma summable_lacunary_pow (c : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable fun k : ℕ => ‖c‖ ^ k * Real.exp (-(2 * Real.pi * 2 ^ k * y)) := by
  have hpi := Real.pi_pos
  -- `e^{-2πy} < 1`, so `‖c‖ · (e^{-2πy})^k → 0`; the ratio at step `k` is
  -- `‖c‖ · e^{-2π 2^k y} ≤ ‖c‖ · (e^{-2πy})^k`, hence eventually `≤ 1/2`.
  have hr1 : Real.exp (-(2 * Real.pi * y)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have hlim : Tendsto (fun k : ℕ => ‖c‖ * Real.exp (-(2 * Real.pi * y)) ^ k)
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _) hr1).const_mul ‖c‖
  have hev : ∀ᶠ k : ℕ in atTop, ‖c‖ * Real.exp (-(2 * Real.pi * y)) ^ k < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [hev] with k hk
  have hnn : ∀ j : ℕ, 0 ≤ ‖c‖ ^ j * Real.exp (-(2 * Real.pi * 2 ^ j * y)) := fun j => by
    positivity
  rw [Real.norm_of_nonneg (hnn (k + 1)), Real.norm_of_nonneg (hnn k)]
  -- `e^{-2π 2^{k+1} y} = e^{-2π 2^k y} · e^{-2π 2^k y}`
  have hsplit : Real.exp (-(2 * Real.pi * 2 ^ (k + 1) * y))
      = Real.exp (-(2 * Real.pi * 2 ^ k * y)) * Real.exp (-(2 * Real.pi * 2 ^ k * y)) := by
    rw [← Real.exp_add]; congr 1; ring
  -- the ratio is `‖c‖ · e^{-2π 2^k y}`, and `2^k ≥ k` makes it `≤ ‖c‖ · (e^{-2πy})^k`
  have hkle : Real.exp (-(2 * Real.pi * 2 ^ k * y)) ≤ Real.exp (-(2 * Real.pi * y)) ^ k := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have h2k : (k : ℝ) ≤ 2 ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    have hprod : (k : ℝ) * (2 * Real.pi * y) ≤ 2 ^ k * (2 * Real.pi * y) :=
      mul_le_mul_of_nonneg_right h2k (by positivity)
    linarith
  have hratio : ‖c‖ * Real.exp (-(2 * Real.pi * 2 ^ k * y)) ≤ 1 / 2 := by
    calc ‖c‖ * Real.exp (-(2 * Real.pi * 2 ^ k * y))
        ≤ ‖c‖ * Real.exp (-(2 * Real.pi * y)) ^ k := by
          exact mul_le_mul_of_nonneg_left hkle (norm_nonneg c)
      _ ≤ 1 / 2 := hk.le
  calc ‖c‖ ^ (k + 1) * Real.exp (-(2 * Real.pi * 2 ^ (k + 1) * y))
      = (‖c‖ * Real.exp (-(2 * Real.pi * 2 ^ k * y)))
          * (‖c‖ ^ k * Real.exp (-(2 * Real.pi * 2 ^ k * y))) := by
        rw [hsplit]; ring
    _ ≤ (1 / 2) * (‖c‖ ^ k * Real.exp (-(2 * Real.pi * 2 ^ k * y))) :=
        mul_le_mul_of_nonneg_right hratio (hnn k)

/-- The bound sequence for the `q`-series on `{im z ≥ y}` is summable.

The family is supported on the powers of two, so it is the pushforward of
`summable_lacunary_pow` along the injection `k ↦ 2^k - 1`. -/
lemma summable_lacunaryBound (c : ℂ) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ =>
      ‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * (n + 1) * y)) := by
  have hi : Function.Injective fun k : ℕ => 2 ^ k - 1 := by
    intro k₁ k₂ h
    have hbeta : 2 ^ k₁ - 1 = 2 ^ k₂ - 1 := h
    have h1 : 1 ≤ 2 ^ k₁ := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ k₂ := Nat.one_le_two_pow
    have h3 : (2 : ℕ) ^ k₁ = 2 ^ k₂ := by
      have e1 : 2 ^ k₁ - 1 + 1 = 2 ^ k₂ - 1 + 1 := by rw [hbeta]
      rwa [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at e1
    exact Nat.pow_right_injective le_rfl h3
  have hzero : ∀ n ∉ Set.range fun k : ℕ => 2 ^ k - 1,
      ‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * (n + 1) * y)) = 0 := by
    intro n hn
    have hcoeff : lacunaryTwoCoeff c (n + 1) = 0 := by
      rw [lacunaryTwoCoeff, if_neg]
      intro hcond
      exact hn ⟨Nat.log 2 (n + 1), show 2 ^ Nat.log 2 (n + 1) - 1 = n by omega⟩
    simp [hcoeff]
  rw [← hi.summable_iff hzero]
  refine (summable_lacunary_pow c hy).congr fun k => ?_
  have hpow : 2 ^ k - 1 + 1 = 2 ^ k := Nat.succ_pred_eq_of_pos (Nat.two_pow_pos k)
  have hcast : ((2 ^ k - 1 : ℕ) : ℝ) + 1 = 2 ^ k := by
    have : ((2 ^ k - 1 + 1 : ℕ) : ℝ) = ((2 ^ k : ℕ) : ℝ) := by rw [hpow]
    push_cast at this ⊢
    linarith
  simp only [Function.comp_apply, hpow, hcast, lacunaryTwoCoeff_pow, norm_pow]

lemma summable_lacunaryQTerm (c : ℂ) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ =>
      lacunaryTwoCoeff c (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * z) := by
  refine .of_norm ?_
  refine (summable_lacunaryBound c hz).congr fun n => ?_
  exact (norm_lacunaryQTerm c n z).symm

lemma differentiableOn_lacunaryQSeries (c : ℂ) :
    DifferentiableOn ℂ (lacunaryQSeries c) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hU : IsOpen {w : ℂ | z.im / 2 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hy : 0 < z.im / 2 := by linarith
  have hdiff : DifferentiableOn ℂ (lacunaryQSeries c) {w : ℂ | z.im / 2 < w.im} := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_lacunaryBound c hy) ?_ hU ?_
    · intro n
      exact Differentiable.differentiableOn (by fun_prop)
    · intro n w hw
      rw [norm_lacunaryQTerm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      have hw' : z.im / 2 ≤ w.im := le_of_lt hw
      have hc0 : (0 : ℝ) ≤ 2 * Real.pi * ((n : ℝ) + 1) := by positivity
      nlinarith
  have hmem : z ∈ {w : ℂ | z.im / 2 < w.im} := by simp only [Set.mem_setOf_eq]; linarith
  exact (hdiff.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

/-- `1`-periodicity, termwise: `e^{2πi n (z + b)} = e^{2πi n z}` for `b : ℤ`. -/
lemma lacunaryQSeries_add_int (c : ℂ) (z : ℂ) (b : ℤ) :
    lacunaryQSeries c (z + b) = lacunaryQSeries c z := by
  unfold lacunaryQSeries
  refine tsum_congr fun n => ?_
  congr 1
  rw [mul_add, Complex.exp_add]
  have hone : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) * (b : ℂ)) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) * (b : ℂ)
        = (((n + 1) * b : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hone, mul_one]

/-- Exponential decay at `i∞`: on `im τ ≥ 1` the whole series is bounded by
`e^{-2π·im τ}` times the fixed constant `∑ ‖aₙ‖ e^{-2πn}`, because
`(n+1)·y ≥ y + n` there. -/
lemma tendsto_lacunaryQSeries_atImInfty (c : ℂ) :
    Tendsto (fun τ : ℍ => lacunaryQSeries c (τ : ℂ)) atImInfty (nhds 0) := by
  have hpi := Real.pi_pos
  -- the fixed comparison constant
  have hS : Summable fun n : ℕ =>
      ‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * n)) := by
    refine ((summable_lacunaryBound c one_pos).mul_right
      (Real.exp (2 * Real.pi))).congr fun n => ?_
    rw [mul_assoc, ← Real.exp_add,
      show -(2 * Real.pi * ((n : ℝ) + 1) * 1) + 2 * Real.pi = -(2 * Real.pi * n) by ring]
  set C : ℝ := ∑' n : ℕ, ‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * n)) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; exact tsum_nonneg fun n => by positivity
  -- the bound, valid once `im τ ≥ 1`
  have hbound : ∀ᶠ τ : ℍ in atImInfty,
      ‖lacunaryQSeries c (τ : ℂ)‖ ≤ Real.exp (-(2 * Real.pi * τ.im)) * C := by
    rw [eventually_iff_exists_mem]
    refine ⟨UpperHalfPlane.im ⁻¹' Set.Ici 1, atImInfty_basis.mem_of_mem trivial, ?_⟩
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ.im := hτ
    have hτ0 : 0 < τ.im := lt_of_lt_of_le one_pos hτ1
    have hsum : Summable fun n : ℕ =>
        ‖lacunaryTwoCoeff c (n + 1) *
          Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))‖ := by
      refine (summable_lacunaryBound c (y := τ.im) hτ0).congr fun n => ?_
      exact (norm_lacunaryQTerm c n (τ : ℂ)).symm
    calc ‖lacunaryQSeries c (τ : ℂ)‖
        ≤ ∑' n : ℕ, ‖lacunaryTwoCoeff c (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))‖ :=
          norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' n : ℕ, Real.exp (-(2 * Real.pi * τ.im)) *
            (‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * n))) := by
          refine Summable.tsum_le_tsum (fun n => ?_) hsum (hS.mul_left _)
          rw [norm_lacunaryQTerm]
          rw [show Real.exp (-(2 * Real.pi * τ.im)) *
              (‖lacunaryTwoCoeff c (n + 1)‖ * Real.exp (-(2 * Real.pi * n)))
            = ‖lacunaryTwoCoeff c (n + 1)‖ *
              (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * n))) by ring]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          -- `(n+1)·y ≥ y + n` for `y ≥ 1`
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hcoe : ((τ : ℂ)).im = τ.im := rfl
          rw [hcoe]
          have hprod : (n : ℝ) * 1 ≤ (n : ℝ) * τ.im := mul_le_mul_of_nonneg_left hτ1 hn0
          nlinarith
      _ = Real.exp (-(2 * Real.pi * τ.im)) * C := by rw [hC, tsum_mul_left]
  refine squeeze_zero_norm' hbound ?_
  -- `e^{-2πy}·C → 0` as `y → ∞`
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hlin : Tendsto (fun y : ℝ => -(2 * Real.pi * y)) atTop atBot := by
    have hmul : Tendsto (fun y : ℝ => 2 * Real.pi * y) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
    simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp hmul
  simpa using ((Real.tendsto_exp_atBot.comp (hlin.comp him)).mul_const C)

/-- **`∞` is the ONLY cusp of `Gamma1GL 0 = ⟨T⟩`.**  This is the fact the
level-`0` refutation turns on: mathlib's `IsCusp` is the set of fixed
points of the PARABOLIC elements OF THE GROUP, and every element of
`Γ₁(0)` is lower-left `0`, so its parabolic fixed point is `∞`. -/
lemma eq_infty_of_isCusp_gamma1GL_zero {x : OnePoint ℝ} (hx : IsCusp x (Gamma1GL 0)) :
    x = ∞ := by
  obtain ⟨g, hg, hgp, hgc⟩ := hx
  obtain ⟨γ, hγ, rfl⟩ := hg
  -- the lower-left entry of `γ` is `0` on the nose, `ZMod 0` being `ℤ`
  have hz0 : ∀ a b : ℤ, ((a : ZMod 0) = (b : ZMod 0)) → a = b := by
    intro a b h
    simpa [Int.ModEq, Int.emod_zero] using (ZMod.intCast_eq_intCast_iff a b 0).1 h
  have h10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 :=
    hz0 _ _ (by simpa using ((CongruenceSubgroup.Gamma1_mem 0 γ).1 hγ).2.2)
  rw [hgp.smul_eq_self_iff] at hgc
  rwa [Matrix.GeneralLinearGroup.parabolicFixedPoint, if_pos (by simp [h10])] at hgc

/-- **A weight-two cusp form for `Γ₁(0) = ⟨T⟩` with the lacunary
`q`-expansion `∑_{k ≥ 0} c^k q^{2^k}`** (**PROVEN 2026-07-30**; a sorry
leaf from 2026-07-28 until then) —
the one analytic input of the level-`0` refutation above, and the ONLY
new sorry this repair introduced.

**THE PROOF IS THE THREE BULLETS BELOW, IN ORDER, AND THE DIAGNOSIS WAS
EXACTLY RIGHT** — "only mathlib plumbing, no theory".  It is carried by the
six lemmas of the `LacunaryLevelZero` section above, all stated about the
single complex function `lacunaryQSeries c` rather than about a function on
`ℍ`, which is what makes periodicity, holomorphy and decay three
statements about one object:

* `summable_lacunary_pow` is the crux, and it is where "for EVERY `c`" is
  earned.  The terms are `‖c‖^k r^{2^k}` with `r = e^{-2πy} < 1`, so the
  RATIO is `‖c‖ r^{2^k} → 0` — doubly exponential decay beats any fixed
  geometric growth, and `summable_of_ratio_norm_eventually_le` at `1/2`
  closes it.  A comparison against a single geometric series cannot work:
  `‖c‖^k r^{2^k} ≤ (Mr)^k` needs `r < 1/M`, i.e. `y` large, and `y` is
  given.
* `summable_lacunaryBound` transports that to the index set the
  `q`-expansion actually runs over.  The family over `n` is supported on
  `n + 1 = 2^k`, so it is the pushforward along the injection
  `k ↦ 2^k - 1` (`Function.Injective.summable_iff`, whose side condition
  "zero off the range" is `lacunaryTwoCoeff`'s own `if`).
* `differentiableOn_lacunaryQSeries` is
  `Complex.differentiableOn_tsum_of_summable_norm` on `{im w > (im z)/2}`
  — a horizontal half-plane STRICTLY INSIDE `ℍ`, because the bound
  degrades as `im → 0` and the lemma wants it uniform.  `DifferentiableOn`
  there gives `DifferentiableAt` at `z`, and `mdifferentiable_iff` turns
  the resulting `DifferentiableOn ℂ · {0 < im}` into `MDiff`.
* `lacunaryQSeries_add_int` is `1`-periodicity, termwise, from
  `Complex.exp_int_mul_two_pi_mul_I`; combined with
  `coe_smul_of_det_pos` and `σ g = id` (`det (mapGL ℝ γ) = 1 > 0`) it is
  the whole of slash-invariance, since every `γ ∈ Γ₁(0)` has
  `γ₀₀ = γ₁₁ = 1` and `γ₁₀ = 0` ON THE NOSE (`ZMod 0` is `ℤ`), hence
  `denom = 1` and `γ • τ = τ + γ₀₁`.
* `tendsto_lacunaryQSeries_atImInfty` and
  `eq_infty_of_isCusp_gamma1GL_zero` are the cusp condition.  The second
  is where the trap below is DISCHARGED rather than avoided: `IsCusp` asks
  for a fixed point of a parabolic element OF THE GROUP, every element of
  `Γ₁(0)` has lower-left entry `0`, and `parabolicFixedPoint` of such an
  element is `∞` by definition — so `∞` is the only cusp and
  `isZeroAt_infty_iff` reduces the condition to `f → 0` at `i∞`.  The
  decay itself is `‖f(τ)‖ ≤ e^{-2π·im τ} · ∑ ‖aₙ‖e^{-2πn}` for
  `im τ ≥ 1`, which is `(n+1)y ≥ y + n` there.

TRUE, and the argument is short enough to state completely.  `Gamma1 0`
is `⟨T⟩` (see the section docstring), so mathlib's
`CuspForm (Gamma1GL 0) 2` asks for exactly three things.

* **Slash-invariance under `Gamma1GL 0`.**  Every element is
  `[[1, b], [0, 1]]` with determinant `1`, so `f ∣[2] T^b (τ) = f (τ + b)`,
  and a `q`-series in `q = exp (2πiτ)` is `1`-periodic.
* **Holomorphy on `ℍ`.**  `‖c ^ k q ^ (2 ^ k)‖ = |c| ^ k e ^ (−2π 2^k y)`,
  and `2 ^ k` in the exponent outruns `|c| ^ k` for EVERY `c`, uniformly
  on `y ≥ y₀ > 0`.  So the series converges locally uniformly and the sum
  is holomorphic; this also gives the `qExpansionSummable` clause.
* **Vanishing at the cusps.**  Mathlib's cusp condition is
  `zero_at_cusps' : ∀ {c}, IsCusp c Γ → c.IsZeroAt f k`, and
  `IsCusp c 𝒢 := ∃ g ∈ 𝒢, g.IsParabolic ∧ g • c = c` — the fixed points
  of the PARABOLIC elements of `𝒢`, and of `𝒢` only.  The parabolics of
  `⟨T⟩` are the `T ^ b` with `b ≠ 0`, acting on `OnePoint ℝ` by
  `x ↦ x + b`, whose only fixed point is `∞`.  **So `∞` is the one and
  only cusp of `Gamma1GL 0`**, and the condition there is `f → 0` as
  `im τ → ∞`, which the leading term `q` gives.

**THE TRAP THIS TURNS ON, and it is why the leaf is TRUE rather than
false.**  For a congruence subgroup of finite index the cusp set is all
of `ℙ¹(ℚ)`, and this `f` would then have to vanish at `0` as well — which
it does NOT: along the imaginary axis `τ → 0` one has `q → 1` and
`∑ c ^ k q ^ (2 ^ k)` diverges for `|c| ≥ 1` (the series has the real line
as a natural boundary).  `⟨T⟩` has INFINITE index in `SL(2, ℤ)`, is not a
congruence subgroup in the finite-index sense, and mathlib's `IsCusp` is
stated for a general `Subgroup (GL (Fin 2) ℝ)` precisely so that it does
not quantify over a larger group.  A prover who reaches for
`∀ A : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] A)` — the shape mathlib's
`CuspForm` had before it was generalised — will refute this leaf rather
than prove it, and the refutation will be of the wrong statement.

**WHAT WAS MISSING** was only mathlib plumbing: locally-uniform
convergence of a lacunary `q`-series and the resulting `MDiff`, plus the
identification of the parabolic elements of `⟨T⟩`.  No theory — and that
prediction held.  All of it is the subsection immediately above:

* `slashInvariant_lacunaryTwoSeries` over `gamma1GL_zero_entries`
  (`ZMod 0 = ℤ`, so the congruences are equalities) and
  `lacunaryTwoSeries_add_intCast` (`1`-periodicity of `q`);
* `mdiff_lacunaryTwoSeries` over `differentiableOn_lacunaryTwoSeries`,
  which is mathlib's `differentiableOn_tsum_of_summable_norm` on each
  half-plane `im z > b` — the majorant is uniform there but not on all of
  `ℍ`, hence the exhaustion at `b = im z / 2`;
* `eq_infty_of_isCusp_gamma1GL_zero` and
  `isZeroAtImInfty_lacunaryTwoSeries`, the latter via the explicit bound
  `‖f‖ ≤ C · e ^ (-2π im τ)` above `im τ = 1`
  (`norm_lacunaryTwoSeries_le`).

**THE ONE IDEA WORTH REUSING**, because it is what makes the analysis
routine rather than delicate.  The heading above says `2 ^ k` "outruns
`|c| ^ k`", which is true but awkward to formalise directly.  Instead
choose `s` with `‖c‖ ≤ 2 ^ s` and observe
`‖lacunaryTwoCoeff c n‖ ≤ n ^ s` for EVERY `n`
(`norm_lacunaryTwoCoeff_le`): at `n = 2 ^ k` this is
`‖c‖ ^ k ≤ (2 ^ s) ^ k = (2 ^ k) ^ s`, and off the powers of `2` the
coefficient vanishes.  The lacunary series is then an ORDINARY
polynomially-bounded `q`-series and
`summable_pow_mul_geometric_of_norm_lt_one` supplies every estimate.  The
lacunarity is never used again after that one line. -/
theorem exists_cuspForm_gamma1GL_zero_lacunary (c : ℂ) :
    ∃ f : CuspForm (Gamma1GL 0) 2,
      (∀ τ : UpperHalfPlane, f τ = ∑' n : ℕ, lacunaryTwoCoeff c (n + 1) *
          Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))) ∧
        ∀ τ : UpperHalfPlane, Summable fun n : ℕ => lacunaryTwoCoeff c (n + 1) *
          Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)) := by

  refine ⟨{ toFun := fun τ : ℍ => lacunaryQSeries c (τ : ℂ)
            slash_action_eq' := ?_
            holo' := ?_
            zero_at_cusps' := ?_ }, fun τ => rfl, fun τ => summable_lacunaryQTerm c τ.im_pos⟩
  · -- SLASH-INVARIANCE: every element of `Γ₁(0)` is `T^b`, so this is `1`-periodicity
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := hg
    have hz0 : ∀ a b : ℤ, ((a : ZMod 0) = (b : ZMod 0)) → a = b := by
      intro a b h
      simpa [Int.ModEq, Int.emod_zero] using (ZMod.intCast_eq_intCast_iff a b 0).1 h
    obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem 0 γ).1 hγ
    have e00 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := hz0 _ _ (by simpa using h00)
    have e11 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := hz0 _ _ (by simpa using h11)
    have e10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := hz0 _ _ (by simpa using h10)
    set g : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hgdef
    have hdetpos : (0 : ℝ) < g.det.val := by simp [hgdef]
    have hσ : ∀ w : ℂ, UpperHalfPlane.σ g w = w := fun w => by
      rw [UpperHalfPlane.σ, if_pos hdetpos]; rfl
    ext τ
    rw [ModularForm.slash_apply, hσ]
    -- `denom g τ = 1`, `|det g| = 1`, and `g • τ = τ + b`
    have hden : denom g (τ : ℂ) = 1 := by simp [hgdef, denom, e10, e11]
    have hsmul : ((g • τ : ℍ) : ℂ)
        = (τ : ℂ) + (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℂ) := by
      rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
      simp [hgdef, num, denom, e00, e10, e11]
    show lacunaryQSeries c ((g • τ : ℍ) : ℂ) * _ * _ = lacunaryQSeries c (τ : ℂ)
    rw [hsmul, lacunaryQSeries_add_int, hden]
    simp [hgdef]
  · -- HOLOMORPHY on `ℍ`, from `DifferentiableOn` of the series on `{im > 0}`
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_lacunaryQSeries c).congr fun z hz => ?_
    rw [UpperHalfPlane.comp_ofComplex_of_im_pos _ z hz]
    rfl
  · -- VANISHING AT THE CUSPS: `∞` is the only cusp of `⟨T⟩`, and the leading
    -- term `q` gives `f → 0` there
    intro x hx
    rw [eq_infty_of_isCusp_gamma1GL_zero hx, OnePoint.isZeroAt_infty_iff]
    exact tendsto_lacunaryQSeries_atImInfty c

end LacunaryLevelZero

/-- **Every `c : ℂ` is the second coefficient of a level-`0` eigenform**
(PROVEN 2026-07-28, over `exists_cuspForm_gamma1GL_zero_lacunary`) — the
degeneracy of `IsWeightTwoEigenformOn` at `N = 0`, in the form the two
refutations below consume.

`hecke` is discharged by `absurd (dvd_zero p)`: its hypothesis is
`¬ p ∣ 0`.  `atkin` is discharged by `lacunaryTwoCoeff_atkin`.  The
nebentypus is `1`, and any other would serve equally — at `N = 0` no
field mentions `χ`. -/
theorem exists_isWeightTwoEigenformOn_gamma1GL_zero (c : ℂ) :
    ∃ (χ : DirichletCharacter ℂ 0) (f : CuspForm (Gamma1GL 0) 2),
      IsWeightTwoEigenformOn (Gamma1GL 0) 0 χ f (lacunaryTwoCoeff c) := by
  obtain ⟨f, hq, hs⟩ := exists_cuspForm_gamma1GL_zero_lacunary c
  exact ⟨1, f,
    { qExpansion := hq
      qExpansionSummable := hs
      zero := lacunaryTwoCoeff_zero c
      one := lacunaryTwoCoeff_one c
      hecke := fun p _ hpd _ _ => absurd (dvd_zero p) hpd
      atkin := fun p hp _ n hn => lacunaryTwoCoeff_atkin c p hp n hn }⟩

/-- **THE `Γ₁` HECKE-ISOTYPIC DECOMPOSITION IS EMPTY AT LEVEL `0`**
(PROVEN 2026-07-28) — the settling check the assembly leaf below asked
for, with the answer that forces its `hN`.

Pure counting, as the section docstring explains: `cover` demands an
index for each of the pairwise-distinct systems `lacunaryTwoCoeff c`,
`c : ℂ`, and `fintypeIdx` says the index type is finite.  No field beyond
`cover`, `coeff` and `fintypeIdx` is touched, so the emptiness is not an
artefact of `integral`, `isotypic` or `finite_ker`. -/
theorem isEmpty_isHeckeIsotypicDecompositionGamma1_zero
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 0 strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    IsEmpty (IsHeckeIsotypicDecompositionGamma1 0 h jac) := by
  constructor
  intro D
  letI := D.fintypeIdx
  have hcov : ∀ c : ℂ, ∃ i : D.idx, D.coeff i 2 = c := by
    intro c
    obtain ⟨χ, f, hf⟩ := exists_isWeightTwoEigenformOn_gamma1GL_zero c
    obtain ⟨i, hi⟩ := D.cover χ f (lacunaryTwoCoeff c) hf
    exact ⟨i, by rw [hi]; exact lacunaryTwoCoeff_two c⟩
  choose g hg using hcov
  exact _root_.not_injective_infinite_finite g
    (fun c₁ c₂ hc => by rw [← hg c₁, ← hg c₂, hc])

/-- **THE LEVEL-`0` ANALYTIC HYPOTHESIS IS CONTRADICTORY** (PROVEN
2026-07-28) — what lets `isTorsion_jacobian_of_lFunction_ne_zero_gamma1`
keep its signature while the two Eichler–Shimura statements below gain
`hN : N ≠ 0`, so that the shape-free wrapper is untouched.

At `c = 8` the Dirichlet series of `lacunaryTwoCoeff 8` is
`∑_k 8^k 2^{-ks}`, whose `n = 2^k` terms have modulus
`8^k / (2^k)^{re s} = 2^{k(3 − re s)} ≥ 1` on the whole strip
`2 < re s < 3`.  A summable family tends to `0`, so the family is not
summable and `LSeries` — a `tsum` — takes its junk value `0` there.
`IsLFunctionOf.eq_lseries` then pins the entire `L` to `0` on a nonempty
open set, and the identity theorem (the step
`isLFunctionOf_apply_eq` runs) propagates that to all of `ℂ`. -/
theorem not_lFunctionHypothesis_gamma1GL_zero
    (hL : ∀ χ : DirichletCharacter ℂ 0,
      ∀ (f : CuspForm (Gamma1GL 0) 2) (a : ℕ → ℂ),
        IsWeightTwoEigenformOn (Gamma1GL 0) 0 χ f a →
        ∃ L : ℂ → ℂ, IsLFunctionOf a L ∧ L 1 ≠ 0) : False := by
  have hterm : ∀ (s : ℂ), s.re ≤ 3 → ∀ k : ℕ,
      (1 : ℝ) ≤ ‖LSeries.term (lacunaryTwoCoeff 8) s (2 ^ k)‖ := by
    intro s hs k
    have hne : (2 : ℕ) ^ k ≠ 0 := by positivity
    rw [LSeries.term_of_ne_zero hne, lacunaryTwoCoeff_pow, norm_div,
      Complex.norm_natCast_cpow_of_pos (by positivity)]
    have h8 : ‖(8 : ℂ) ^ k‖ = (8 : ℝ) ^ k := by rw [norm_pow]; norm_num
    rw [h8, le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _), one_mul]
    have hx : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      push_cast; exact one_le_pow₀ (by norm_num)
    have h3 : ((2 ^ k : ℕ) : ℝ) ^ (3 : ℝ) = (8 : ℝ) ^ k := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      push_cast
      rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      ring_nf
    exact (Real.rpow_le_rpow_of_exponent_le hx hs).trans_eq h3
  have hzero : ∀ s : ℂ, s.re ≤ 3 → LSeries (lacunaryTwoCoeff 8) s = 0 := by
    intro s hs
    refine tsum_eq_zero_of_not_summable ?_
    intro hsum
    have h0 : Filter.Tendsto (fun n => ‖LSeries.term (lacunaryTwoCoeff 8) s n‖)
        Filter.atTop (nhds 0) := by simpa using hsum.tendsto_atTop_zero.norm
    have hev : ∀ᶠ n in Filter.atTop, ‖LSeries.term (lacunaryTwoCoeff 8) s n‖ < 1 :=
      h0.eventually_lt_const (by norm_num)
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    exact absurd (hM (2 ^ M) (Nat.le_of_lt Nat.lt_two_pow_self)) (not_lt.2 (hterm s hs M))
  obtain ⟨χ, f, hf⟩ := exists_isWeightTwoEigenformOn_gamma1GL_zero 8
  obtain ⟨L, hLof, hne⟩ := hL χ f (lacunaryTwoCoeff 8) hf
  refine hne ?_
  have hopen : IsOpen {z : ℂ | 2 < z.re ∧ z.re < 3} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : (((5 / 2 : ℝ) : ℂ)) ∈ {z : ℂ | 2 < z.re ∧ z.re < 3} := by
    constructor <;> · simp only [Complex.ofReal_re]; norm_num
  have key : Set.EqOn L (fun _ => (0 : ℂ)) Set.univ := by
    refine hLof.entire.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_univ (Set.mem_univ (((5 / 2 : ℝ) : ℂ))) ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [hLof.eq_lseries z hz.1, hzero z (le_of_lt hz.2)]
  exact key (Set.mem_univ 1)

/-- **THE `Γ₁` ISOTYPIC DECOMPOSITION, GIVEN THE FACTORS** (sorry leaf,
new 2026-07-28; **`hN : N ≠ 0` ADDED 2026-07-28 after the level-`0` case
was REFUTED** — see the section docstring above and
`isEmpty_isHeckeIsotypicDecompositionGamma1_zero`) — the "ASSEMBLE the
factors" half of the cut of `exists_heckeIsotypicDecomposition_gamma1`
below, and the `Γ₁` transport of `X0.lean`'s
`exists_heckeIsotypicDecomposition_of_isotypicQuotients`.

TRUE, and it is what is left of Eichler–Shimura once Shimura's `A_f` is
granted.  The three things this leaf owns are exactly the ones a single
factor cannot see, and they are the `Γ₀` list plus one:

* **finiteness of the index set.**  `S₂(Γ₁(N))` is finite-dimensional and
  eigenforms with distinct eigen-systems are linearly independent, so
  there are finitely many systems; `hquot` supplies one factor for each,
  and `cover` is then immediate.
* **the MULTIPLICITIES.**  `hquot` gives ONE quotient per system; the
  decomposition needs `σ₀(N/M)` copies of `A_g`, carried by the distinct
  degeneracy-twisted surjections `J_1(N) ↠ J_1(M) ↠ A_g`.  Those maps are
  not in `hquot`'s output and must be built.  That the copies are needed
  is the same multiplicity computation `X0.lean` records: at `N = p³M`
  with `p ∤ M` the `g`-old space is `4`-dimensional while `U_p` on it has
  only `2` eigenvalues and is not semisimple.
* **`finite_ker`**, i.e. that the map to the product is an isogeny.  This
  is Poincaré complete reducibility together with `∑_i dim A_i =
  g(X_1(N))`.  Mumford, *Abelian Varieties* §19; Diamond–Shurman
  Thm 6.6.6.
* **`neben`, the field with no `Γ₀` counterpart.**  Each factor must be
  labelled by the nebentypus of the eigenform cutting it out, which is
  the decomposition of `S₂(Γ₁(N))` into `χ`-eigenspaces under the action
  of `Γ₀(N)/Γ₁(N) ≅ (ℤ/N)ˣ`.  `hquot` is already quantified over `χ`, so
  this leaf receives the labels rather than having to produce the
  decomposition — it only has to keep them attached to the right factor.

**THE `N = 0` OBLIGATION WAS THIS LEAF'S, IT WAS REFUTED, AND `hN` IS THE
REPAIR** (2026-07-28).  The heading this replaces said the obligation was
"not known to be dischargeable" and named the settling check.  Both
halves are now resolved, and in opposite directions:

* **The proposed rescue does not exist.**  The check was: is
  `IsCoarseModuliY1 0 strY` strong enough to contradict `X` being a
  curve?  It is not.  `IsCoarseModuliY1` has exactly three fields —
  `classify`, `classify_natural`, `universal` — and its own docstring
  records that "bijectivity on geometric points is deliberately
  omitted".  Initiality constrains no cardinality, so nothing in it can
  see that a single `E` contributes uncountably many pairs `(E, P)`.
  The `Γ₀` route (`isEmpty_of_isCoarseModuliY0_zero`) has no analogue
  here, exactly as the old heading warned.
* **And the conclusion is EMPTY at `N = 0`**, which the old heading did
  not suspect: `isEmpty_isHeckeIsotypicDecompositionGamma1_zero`, by the
  counting argument of the section docstring above (`atkin` degenerates
  to complete multiplicativity at level `0`, so `lacunaryTwoCoeff c` is
  admissible for every `c : ℂ`; `cover` demands an index for each and
  `fintypeIdx` says there are finitely many).

Together: at `N = 0` the conclusion is `Nonempty` of an empty type, so
the leaf was provable there only by refuting its own hypotheses, and the
first bullet says that cannot be done in this vocabulary.  That is a
statement no prover can honestly close, which is worse than an open one —
so `hN : N ≠ 0` is now a hypothesis, and `hquot` is correspondingly
UNCONDITIONAL rather than guarded by `N ≠ 0`.

The `N = 0` case did not vanish; it moved to where it is genuinely
dischargeable, `isTorsion_jacobian_of_lFunction_ne_zero_gamma1`, whose
analytic hypothesis is contradictory at level `0`
(`not_lFunctionHypothesis_gamma1GL_zero`).  The shape-free wrapper
`isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` is therefore
untouched and the `Γ₀` side is unaffected.

**WHY THIS IS A CUT AND NOT A RESTATEMENT.**  `hquot` is consumed three
times — one factor per system for `cover`, the factors themselves for
`A`/`u`/`S`/`neben`, and `integral` per factor — and it is the single
hardest object in the parent, the existence of an abelian-variety
quotient with a prescribed Hecke action.  What it does NOT remove is the
global content: a prover here still has to produce ONE datum whose
`finite_ker` holds, which is why the cut is "the factors / all factors"
rather than a split of the field groups.  Every such split dies to the
witness `A i := SpecQ`, `astr i := 𝟙 SpecQ`, `u i := jstr`, which
`finite_ker` kills globally and no per-field split does.

**THE CUT HAD LEAKED, AND `hquot` NOW CARRIES THE MODULI PIN** (repaired
2026-07-30).  Two individually-correct edits made this cut deliver
nothing, which is a failure shape this development has hit before and
which no falsity check sees, because the leaf stayed TRUE throughout:

* 2026-07-28, the cut: `hquot` exports `∃ T` with `IsAdditiveOn` and the
  isotypic quotients — and nothing else about `T`.
* 2026-07-29, the structure: `IsHeckeIsotypicDecompositionGamma1` gained
  `heckeModuli : IsModularHeckeActionGamma1 N h.some jac T T_comp`, the
  field that excludes the `N = 37` eigen-system swap.

After the second edit the conclusion demands a `T` that IS the genuine
Hecke correspondence, while `hquot` hands over an existentially quantified
`T` with no pin at all.  So a prover could not use `hquot`'s `T` for
`heckeModuli`, and the only way forward was to DISCARD `hquot`, call
`exists_modularHeckeAction_gamma1` and
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` directly, and
rebuild the hypothesis — i.e. this leaf was exactly as hard as the parent
`exists_heckeIsotypicDecomposition_gamma1` and the decomposition bought
nothing.  A stale docstring made it worse: the paragraph above says
`hquot` "is consumed three times", which was true when written.

The repair costs nothing and is on the SUPPLIER side.
`exists_heckeAction_isotypicQuotients_gamma1` already HELD the pin — it
obtains `hmod` from `exists_modularHeckeAction_gamma1` and feeds it to
`exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` — and merely
dropped it on the way out.  It is now exported, at `h.some`, which is the
same choice `heckeModuli` names, so the two match.  (Its proof previously
recovered the datum by an anonymous `obtain ⟨H⟩ := h`; that is a different
term from `h.some` and would not have matched the field, so the fix is a
statement change AND a proof change, not just a widening.)  That theorem
is PROVEN and stays proven; only this leaf's hypothesis got stronger.

**AXIS NOT SEARCHED**, inherited from the `Γ₀` node: the complex-analytic
route through `Γ₁(N)\ℍ*`, which is how the classical proof identifies the
factors in the first place.  Everything above is the algebraic-moduli
axis.

## ⚠ THE SECTION THAT STOOD HERE IS STALE — THE FIX IT PRESCRIBED IS IN THE STATEMENT BELOW

It was headed "THIS IS NO LONGER A REDUCTION (found 2026-07-30, and it is a
one-line fix)", it correctly diagnosed that `hquot` handed over an **unpinned**
`T` while the conclusion had gained `heckeModuli`, and it ended "It is left
unmade here deliberately".  **It was made** — commit `1452a0bf`, the same day —
and `hquot` below now carries `IsModularHeckeActionGamma1 N h.some jac T T_comp`
as the second conjunct.  The paragraph four blocks up ("THE CUT HAD LEAKED, AND
`hquot` NOW CARRIES THE MODULI PIN") is the current record and is correct.

So this docstring was for a while asserting both that the repair was made and
that it was deliberately not made, which is the shape this development treats as
worse than an open sorry: the two halves were written by different branches, both
landed, and neither could see the other.  Removed rather than annotated, because
the SOURCE settles it — read `hquot`'s conjunction.

The two entangling reasons the removed section gave for waiting are also gone.
The FALSITY of `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` was
repaired on 2026-07-30 (see the header of its own FALSITY AUDIT: the pin now
carries the three anemic relations, so the arity gap is closed), and the pin
therefore means the SAME thing at both call sites in this file. -/
theorem exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1 (N : ℕ) (hN : N ≠ 0)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o)
    (hquot : ∃ (T : ℕ → (J ⟶ J)) (T_comp : ∀ n, T n ≫ jstr = jstr),
      (∀ n, IsAdditiveOn ab ab (T n) (T_comp n)) ∧
        IsModularHeckeActionGamma1 N h.some jac T T_comp ∧
        ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
          IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
            Nonempty (IsIsotypicQuotient ab T N a)) :
    Nonempty (IsHeckeIsotypicDecompositionGamma1 N h jac) :=
  sorry

/-- **EICHLER–SHIMURA for `Γ₁(N)`: the Hecke-isotypic decomposition
exists** (**PROVEN 2026-07-28**, over the two leaves
`exists_heckeAction_isotypicQuotients_gamma1` and
`exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1`
immediately above; a bare sorry node from earlier the same day until
then) — the first of the two leaves
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1` decomposes into, and the
one carrying Eichler–Shimura.

TRUE; the witness is spelled out in `IsHeckeIsotypicDecompositionGamma1`'s
docstring ("WHY IT IS TRUE"), and it is the classical statement
`J_1(N) ∼ ∏_{M ∣ N} ∏_{g new of level M} A_g^{σ₀(N/M)}` together with the
Hecke action on each factor, the product now running over newforms of
every nebentypus.

**REFERENCES.**  Shimura, *Introduction to the arithmetic theory of
automorphic functions*, §7.5; Diamond–Shurman, *A first course in modular
forms*, §6.6 and Thm 6.6.6 — which is stated for `X_1(N)` in the source,
`Γ₁` being Diamond–Shurman's default level structure, so the `Γ₁` case is
if anything the better-documented one; Cornell–Silverman–Stevens Ch. V.

**WHAT IS GENUINELY MISSING** is exactly what `X0.lean`'s
`exists_heckeIsotypicDecomposition` records, and nothing more: no Hecke
algebra acting on a Jacobian, no `A_g`, no old/new decomposition of
`S₂(Γ₁(N))`, and no isogeny theory for abelian schemes beyond `[n]` and
its flatness (`Modularity/AbelianSchemeIsogeny.lean`).  **So this node and
its `Γ₀` sibling are gated on the SAME missing theory** and should be
taken together by whoever builds it — the `Γ₁` case needs, additionally,
only the decomposition of `S₂(Γ₁(N))` by nebentypus, which is a statement
about the finite abelian group `(ℤ/N)ˣ` acting on a finite-dimensional
space.  The decomposition below does not change that; it partitions the
obligation, it does not shrink it.

**THE CUT (2026-07-28): THE FACTORS / ALL FACTORS**, transported from
`X0.lean`, where `exists_heckeIsotypicDecomposition` is PROVEN over
`exists_modularHeckeAction` and
`exists_heckeIsotypicDecomposition_of_modularHeckeAction`, the latter in
turn over `exists_isotypicQuotient_of_isWeightTwoEigenform` and
`exists_heckeIsotypicDecomposition_of_isotypicQuotients`.  The `Γ₁`
transport is **two** leaves rather than three, and the reason is recorded
in full on `exists_heckeAction_isotypicQuotients_gamma1` above: the `Γ₀`
side can hand `T` to its factor-building leaf as a hypothesis only because
`IsHeckeIsotypicDecomposition` PINS `T` by its `heckeModuli` field, and
`IsHeckeIsotypicDecompositionGamma1` has no such field, so the `Γ₁` leaf
must quantify `T` existentially and thereby absorbs
`exists_modularHeckeAction`'s job.

**⚠ STALE (corrected 2026-07-30): the `Γ₁` structure DOES have a
`heckeModuli` field**, added 2026-07-29.  The clause "and
`IsHeckeIsotypicDecompositionGamma1` has no such field" above is false at
this commit.  The count "two leaves rather than three" is still the right
count of *declarations*, but the reason given for it has gone, and one of
those two — `exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1`
— is no longer a genuine reduction, because its `hquot` hands over an
UNPINNED `T` while its conclusion now needs a pinned one.  The full
accounting is under "⚠ CORRECTION (2026-07-30)" on
`exists_heckeAction_isotypicQuotients_gamma1` above.

`IsIsotypicQuotient` is reused verbatim from `X0.lean` — it is
shape-free — so this transport adds no structure.

**`hN : N ≠ 0` ADDED 2026-07-28, and it is a SOUNDNESS repair, not a
convenience.**  Without it this statement is FALSE at `N = 0`: the
conclusion is `Nonempty (IsHeckeIsotypicDecompositionGamma1 0 h jac)` and
that type is EMPTY (`isEmpty_isHeckeIsotypicDecompositionGamma1_zero`),
while the hypotheses `h` and `jac` are not refutable at level `0` —
`IsCoarseModuliY1` carries no bijectivity clause, so the `Γ₀` rescue
`isEmpty_of_isCoarseModuliY0_zero` has no analogue.  See the section
docstring "The level-`0` degeneracy of `Γ₁` Eichler–Shimura" above for
the witness.  The sole consumer,
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1`, absorbs the `N = 0`
case through `not_lFunctionHypothesis_gamma1GL_zero` and so keeps its own
signature; nothing above it changes.

**THE `Γ₀` CHAIN NAMED ABOVE IS A MAP OF THE TERRITORY, NOT A MODEL TO
COPY** (2026-07-28).  Two of its links —
`exists_isotypicQuotient_of_isWeightTwoEigenform` and
`exists_heckeIsotypicDecomposition_of_modularHeckeAction` — were refuted
the same day, on an ARITY GAP between the `heckeModuli` pin (primes
`ℓ ∤ N` only) and the isotypy fields (every `n` coprime to `N`).  The `Γ₁`
cut below is unaffected because it quantifies `T` existentially, with the
`∃ T` outside the `∀ χ f a`; the full argument is on
`exists_heckeAction_isotypicQuotients_gamma1`.  Anyone tempted to bring
the two cuts into line should move the `Γ₀` one toward this shape, not
this one toward the `Γ₀` shape. -/
theorem exists_heckeIsotypicDecomposition_gamma1 (N : ℕ) (hN : N ≠ 0)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    Nonempty (IsHeckeIsotypicDecompositionGamma1 N h jac) :=
  exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1 N hN h jac
    (exists_heckeAction_isotypicQuotients_gamma1 N hN h jac)

/-- **KOLYVAGIN–LOGACHEV for `Γ₁(N)`: a Hecke-isotypic factor of `J_1(N)`
has torsion Mordell–Weil group** (sorry node, new 2026-07-28) — the second
of the two leaves, and the one carrying the Euler system.

The intended proof uses only `hL (D.neben i) (D.form i) (D.coeff i)
(D.isEigen i)`: `A i` is the modular abelian variety attached to the
newform underlying `D.form i`, its `L`-function is `∏_σ L(g^σ, s)`, and
Kolyvagin–Logachev (*Finiteness of the Shafarevich–Tate group and the
group of rational points for some modular abelian varieties*, 1989) turns
`L(g, 1) ≠ 0` into finiteness of `A_g(ℚ)` via Heegner points and
Gross–Zagier.  Nothing in that argument is `Γ₀`-specific: Heegner points
on `X_1(N)` work the same way, and the passage from the eigenform
`D.form i` of level `N` to its newform `g` of level `M ∣ N` is free in
the direction needed, `L(f, s)` differing from `L(g, s)` by Euler factors.

**WHY THE HYPOTHESIS IS THE WHOLE OF `hL` AND NOT `L(form i, 1) ≠ 0`.**
Because `IsHeckeIsotypicDecompositionGamma1.T` is not pinned to be the
genuine Hecke correspondences, and with an unpinned `T` the sharper
statement is **FALSE**: swap the eigen-systems of `E_{37a}` and
`E_{37b}`, which no field of this structure can see.  The swap uses
nothing about the level structure, so it inhabits the `Γ₁` structure
exactly as it inhabited the `Γ₀` one.

**THE `Γ₀` CROSS-REFERENCE THAT USED TO STAND HERE IS NOW STALE, AND THE
ASYMMETRY IS THE POINT** (corrected 2026-07-28).  This paragraph used to
say the counterexample "transfers verbatim from `X0.lean`".  It no longer
lives there: `IsHeckeIsotypicDecomposition` acquired a `heckeModuli`
field (`IsModularHeckeAction`, the moduli description
`(E, C) ↦ ∑_D (E/D, (C+D)/D)` of `T_ℓ` at `ℓ ∤ N`), the `N = 37` swap does
**not** inhabit the pinned structure, and sharpening the `Γ₀` leaf is
recorded there as UNBLOCKED.

**AND THE SENTENCE THAT FOLLOWED HERE IS ITSELF NOW STALE — CORRECTED
2026-07-30.**  It read: "`IsHeckeIsotypicDecompositionGamma1` has no such field,
so the swap survives here and the sharpening is still blocked on the `Γ₁` side.
**The repair is to build the `Γ₁` pin** …".  **The `Γ₁` pin was built on
2026-07-29** — `IsHeckeIsotypicDecompositionGamma1.heckeModuli :
IsModularHeckeActionGamma1 N h.some jac T T_comp`, whose own field docstring says
in terms that it "is what excludes the `N = 37` eigen-system swap" — and its
arity gap was closed on 2026-07-30 (the three anemic relations; see the repaired
FALSITY AUDIT on `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1`
above).  So the `E_{37a}`/`E_{37b}` swap does **not** inhabit this structure
either: it already fails at `ℓ = 2`, where `a₂(37a) = −2` and `a₂(37b) = 0`.

**WHAT THAT DOES AND DOES NOT UNBLOCK.**  It removes the *stated* obstruction to
sharpening this leaf to `L(form i, neben i, 1) ≠ 0`, so the sharpening is now in
the same position as its `Γ₀` sibling: available, and still requiring its OWN
faithfulness audit against the pinned structure rather than an inherited one.
Two things a successor should know before attempting it, both checked on
2026-07-30:

* **`N ≠ 0` does NOT have to be threaded in from a consumer, and looking for a
  consumer to thread it is a dead end.**  Neither
  `isTorsion_jacobian_of_lFunction_ne_zero_gamma1` nor the `_of_levelShape`
  wrapper carries `hN`, which reads as a blocker — but this leaf does not need
  them to: it holds a `D`, and `isEmpty_isHeckeIsotypicDecompositionGamma1_zero`
  (PROVEN, ~350 lines above) says that type is EMPTY at `N = 0`.  So `N ≠ 0` is
  derivable here from `D` alone, and `heckeModuli` is therefore never read at
  the level where it degenerates to the empty conjunction.  That is why this
  leaf keeps its signature while the two Eichler–Shimura statements above gained
  `hN`.
* the sharpening is a CUT-LEVEL change — it alters what the consumer must
  supply — so it must not be bundled with any other edit to this declaration.
  Two individually-correct edits to one statement have made a leaf false in this
  development before.

**BEFORE BUILDING THAT PIN, READ THE ARITY-GAP WARNING** on
`exists_heckeAction_isotypicQuotients_gamma1` above.  `IsModularHeckeAction`
constrains `T` only at PRIMES `ℓ ∤ N`, while the isotypy fields it is meant
to support range over EVERY `n` coprime to `N`; that mismatch is what made
`exists_isotypicQuotient_of_isWeightTwoEigenform` and
`exists_heckeIsotypicDecomposition_of_modularHeckeAction` FALSE on the `Γ₀`
side (refuted at `N = 37`, 2026-07-28).  A `Γ₁` pin copied at the `Γ₀` arity
range would reproduce that falsity here, and it would do so while looking
like a faithful transport.  Do not do both at once:
two individually-correct edits to one statement have made a leaf false in
this development before.

**A ROUTE THAT READS AS AVAILABLE AND IS CIRCULAR** (recorded so it is
not re-tried; the `Γ₀` leaf carries the same warning).  "With the full
`hL` the statement is TRUE for any `T`, because `hL` already forces
`J_1(N)(ℚ)` to be torsion and `u_surj` bounds the rank of a factor" —
`J_1(N)(ℚ)` torsion is the conclusion of THIS LEAF'S OWN CONSUMER,
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1` below, so a prover
taking that sentence literally has nothing to start from.  The
non-circular route uses `D.u_surj i` and nothing else about `D`: `A i` is
an abelian-variety QUOTIENT of `J_1(N)`; by Eichler–Shimura every such
quotient is `ℚ`-isogenous to a product of modular abelian varieties `A_g`
with `g` a newform of level `M ∣ N` and some nebentypus; each such `g` is
an eigenform to which `hL` applies directly at its own `χ`; and
Kolyvagin–Logachev makes each `A_g(ℚ)` torsion, with isogeny invariance
already PROVEN as `X0.lean`'s `isTorsion_of_finite_jointKer`.

**THAT ROUTE IS A PROOF SKETCH, NOT A CUT**, and this is why this leaf is
left whole rather than decomposed alongside its sibling above.  Its
second step — "every quotient of `J_1(N)` is `ℚ`-isogenous to a product
of modular abelian varieties" — cannot be split off without an interface
for "`B` is the modular abelian variety attached to `g`", and every
pin-free way of writing that is either too weak (a bare Hecke-isotypy
condition, which the `E_{37a}`/`E_{37b}` swap satisfies) or is this leaf
verbatim (a quotient of `J_1(N)` plus the full `hL`).  The shape that
would work is the `L`-function characterisation `L(B, s) = ∏_σ L(g^σ, s)`,
which needs a Hasse–Weil `L`-function of an abelian variety — absent from
this project, from mathlib at this pin, and from `~/cs/FLT`.  The route's
one further input, Poincaré reducibility, is absent from all three as
well (`grep -ri "poincar" Fermat/ .lake/packages/mathlib/Mathlib/
~/cs/FLT/FLT/` returns only this development's own prose).

**AXIS NOT SEARCHED**: everything above ranges over algebraic-moduli and
isogeny-shaped cuts.  The complex-analytic route — Heegner points on
`X_1(N)` and the Gross–Zagier formula read on `Γ₁(N)\ℍ*` — has not been
searched as a source of sub-leaves.

`D.u_surj`, `D.isotypic`, `D.cover`, `D.equivariant` and `D.integral` are
all available to a prover and none is decoration: the first carries the
rank bound, the rest identify which eigenform `A i` belongs to. -/
theorem isTorsion_factor_of_heckeIsotypic_gamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    {h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {jac : IsJacobianOf strX ab o} (D : IsHeckeIsotypicDecompositionGamma1 N h jac)
    (hL : ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
      IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
      ∀ L : ℂ → ℂ, IsLFunctionOf a L → L 1 ≠ 0) (i : D.idx) :
    letI := (D.abA i).addCommGroup (𝟙 SpecQ)
    AddMonoid.IsTorsion (RelPoint (D.astr i) (𝟙 SpecQ)) :=
  sorry

/-- **Kolyvagin–Logachev for `Γ₁(N)`: analytic rank `0` forces the
Jacobian of `X_1(N)` to have torsion Mordell–Weil group** (PROVEN
2026-07-28, over the two leaves above plus `X0.lean`'s PROVEN
`isTorsion_of_finite_jointKer`) — the genuinely `Γ₁` half.

The `Γ₀` half is `X0.lean`'s `isTorsion_jacobian_of_lFunction_ne_zero`,
which is PROVEN there over `exists_heckeIsotypicDecomposition`
(Eichler–Shimura), `isTorsion_factor_of_heckeIsotypic`
(Kolyvagin–Logachev) and the elementary `isTorsion_of_finite_jointKer`;
the shape-free wrapper below cites that at `.gamma0` and this at
`.gamma1`.

TRUE, by the same three classical theorems that the `Γ₀` half is
assembled from, and none of the three cares which congruence subgroup is
in play — for `Γ₁(N)` the Eichler–Shimura product runs over newforms of
every nebentypus, which is precisely why `hL` here quantifies over `χ`
with no side condition.

**THE CUT PRESCRIBED BY THE PREVIOUS DOCSTRING HAS BEEN CARRIED OUT**, in
the form it prescribed: the two sub-leaves above are the `Γ₁` instances of
`exists_heckeIsotypicDecomposition` and `isTorsion_factor_of_heckeIsotypic`,
and `X0.lean`'s PROVEN `isTorsion_of_finite_jointKer` is reused verbatim as
the third step.  The one deviation, and it is forced rather than
stylistic: the prescription hoped
`IsHeckeIsotypicDecomposition` could simply be **restated** over
`ModularLevelShape.IsCompactification` so that this leaf would dispose of
itself.  It cannot be, where it lives: `ModularLevelShape` is declared in
THIS module and `X1.lean` `public import`s `X0.lean`, so a shape-generic
restatement inside `X0.lean` would be circular.  Making the seam
shape-free therefore requires MOVING `ModularLevelShape` (and
`IsWeightTwoEigenformOn`) down into `X0.lean` or into a new module below
both — a relocation, not a restatement, and one that would rewrite two
`X0.lean` declarations that are already cut and owned.  The `Γ₁` mirror
above costs one extra structure and closes this node now; unifying the
two is a later refactor whose only mathematical content is that
`IsHeckeIsotypicDecompositionGamma1` differs from
`IsHeckeIsotypicDecomposition` in exactly one field (`neben`).

TRUE.  The proof is the composite of three classical theorems, and none
of the three cares which of `Γ₀(N)`, `Γ₁(N)` is in play:

* **Eichler–Shimura.**  `J(X)` is `ℚ`-isogenous to a product of the
  modular abelian varieties `A_g` cut out by the newforms `g` of level
  `M ∣ N` occurring in `S_2(G)`, with `L(A_g, s) = ∏_σ L(g^σ, s)`.  For
  `Γ₁(N)` the product runs over newforms of every nebentypus, which is
  precisely why `hL` quantifies over `χ`.
* **Gross–Zagier and Kolyvagin–Logachev** (Kolyvagin–Logachev,
  *Finiteness of the Shafarevich–Tate group and the group of rational
  points for some modular abelian varieties*, 1989): `L(g, 1) ≠ 0`
  implies `A_g(ℚ)` finite, via the Heegner-point Euler system.
* **Isogeny invariance**, the only elementary step, and the reason the
  conclusion is `IsTorsion` rather than `Finite`: a `ℚ`-isogeny has
  finite kernel, so if every factor is torsion then for `x ∈ J(ℚ)` some
  `m ≠ 0` sends `m • x` into the finite kernel.  Finiteness would need
  Mordell–Weil in addition, which is `X0.lean`'s
  `fg_relPoint_of_abelianScheme` and is deliberately NOT re-absorbed
  here.

**FAITHFULNESS AUDIT.**

*`hL` quantifies over the right set, in both shapes.*  At `.gamma0` the
`IsNebentypus` side condition restricts `χ` to `1`, so the obligation is
literally `X0.lean`'s: every normalized Hecke eigenform of `S_2(Γ_0(N))`,
which by Atkin–Lehner is the newforms of every `M ∣ N` together with
their `p`-stabilizations.  That set is larger than the newforms and the
enlargement is harmless, because a stabilization has
`L(f, s) = L(g, s) ∏ (1 - β_p p^{-s})` with `|β_p| ≤ √p < p` by Deligne,
so the correction factor at `s = 1` is nonzero.  At `.gamma1` every `χ`
is admitted, which is exactly the decomposition
`S_2(Γ_1(N)) = ⊕_χ S_2(N, χ)`.  Neither too weak nor too strong.

*Not vacuous, in either shape.*  At `.gamma0` the hypothesis holds at the
thirteen Kenku levels — that is what
`lFunction_apply_one_ne_zero_of_kenkuLevel` asserts — and at `.gamma1`,
`N = 25` it holds by the reconnaissance recorded below; it is FALSE at
`N = 37` and at every level of positive analytic rank, which is what
makes it the honest carrier of the arithmetic rather than a formality.

*Neither `h` nor `jac` may be dropped.*  Without `jac`, `J` is an
arbitrary abelian scheme over `ℚ` and the conclusion fails for an
elliptic curve of rank `1`; without `h`, `X` is an arbitrary curve and
the `L`-functions in `hL` have nothing to do with it.  `N` and `S` enter
the conclusion only through `h` and `hL`.

**THE OLD `IRREDUCIBLE` VERDICT IS RETIRED (2026-07-27).**  It said the
correct further decomposition is "`A_g(ℚ)` is torsion when `L(g, 1) ≠ 0`"
as a leaf about a modular abelian variety, needing a Hecke-algebra
interface to be STATED, and that no such interface exists in `Mathlib`,
in `~/cs/FLT` or here.  The first half was exactly right; the second half
was wrong within nine minutes of being written, and the interface now
exists in both shapes.

The *axis not searched*: a `p`-adic / Iwasawa route (Kato's Euler system,
which also gives rank `0` from `L(f, 1) ≠ 0` and applies verbatim to
`Γ₁`), and Mazur's Eisenstein-ideal argument, which is `Γ₀`-specific and
so could not have been shared even if it applied.

**THE `N = 0` BRANCH (2026-07-28).**  `exists_heckeIsotypicDecomposition_gamma1`
gained `hN : N ≠ 0` when its level-`0` case was refuted, so this proof now
splits.  At `N = 0` the hypothesis `hL` is itself CONTRADICTORY
(`not_lFunctionHypothesis_gamma1GL_zero`): the level-`0` eigen-system
`lacunaryTwoCoeff 8` has a Dirichlet series that diverges throughout
`2 < re s < 3`, so no ENTIRE `L` can agree with it there and be nonzero at
`1`.  This is what keeps `hN` out of the present signature, and hence out
of the shape-free wrapper below, which `Γ₀` shares.

**THE ASSEMBLY.**  `hL` supplies an `L`-function it CHOSE and the leaves
want "*the* `L`-function does not vanish"; `isLFunctionOf_apply_eq`
(uniqueness, by the identity theorem) is the bridge, exactly as in
`X0.lean`'s assembly.  Then the decomposition is obtained, each factor is
torsion by `isTorsion_factor_of_heckeIsotypic_gamma1`, and
`isTorsion_of_finite_jointKer` pulls that back to `J` along the family of
quotient maps, whose joint kernel is finite by `finite_ker`. -/
theorem isTorsion_jacobian_of_lFunction_ne_zero_gamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o)
    (hL : ∀ χ : DirichletCharacter ℂ N,
      ∀ (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
        IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
        ∃ L : ℂ → ℂ, IsLFunctionOf a L ∧ L 1 ≠ 0) :
    letI := ab.addCommGroup (𝟙 SpecQ)
    AddMonoid.IsTorsion (RelPoint jstr (𝟙 SpecQ)) := by
  letI := ab.addCommGroup (𝟙 SpecQ)
  rcases eq_or_ne N 0 with rfl | hN
  · exact (not_lFunctionHypothesis_gamma1GL_zero hL).elim
  have hL' : ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
      IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
      ∀ L : ℂ → ℂ, IsLFunctionOf a L → L 1 ≠ 0 := by
    intro χ f a hf L hLf
    obtain ⟨L₀, hL₀, hne⟩ := hL χ f a hf
    rw [isLFunctionOf_apply_eq hLf hL₀ 1]
    exact hne
  obtain ⟨D⟩ := exists_heckeIsotypicDecomposition_gamma1 N hN h jac
  letI := D.fintypeIdx
  letI : ∀ i, AddCommGroup (RelPoint (D.astr i) (𝟙 SpecQ)) :=
    fun i => (D.abA i).addCommGroup (𝟙 SpecQ)
  refine isTorsion_of_finite_jointKer
    (φ := fun i => AddMonoidHom.mk' (fun x => RelPoint.post (D.u i) (D.u_comp i) x)
      (fun x y => D.u_add i x y))
    (fun i => isTorsion_factor_of_heckeIsotypic_gamma1 N D hL' i) ?_
  exact D.finite_ker

/-- **Kolyvagin–Logachev: analytic rank `0` forces the Jacobian of a
modular curve to have torsion Mordell–Weil group** (PROVEN 2026-07-27) —
stated ONCE for `Γ₀` and `Γ₁`, LEVEL-FREE and SHAPE-FREE.

**This is an ASSEMBLY, not a leaf.**  At `.gamma0` it is `X0.lean`'s
`isTorsion_jacobian_of_lFunction_ne_zero` — PROVEN there over
Eichler–Shimura, Kolyvagin–Logachev and isogeny invariance — reached
through `isWeightTwoEigenformOn_gamma0_iff` and the `IsNebentypus` side
condition, which is what restricts `χ` to `1` and so makes the `hL` this
wrapper demands exactly the one `X0.lean` demands, neither stronger nor
weaker.  At `.gamma1` it is
`isTorsion_jacobian_of_lFunction_ne_zero_gamma1` above.

The earlier version of this declaration was a `sorry` asserting the `Γ₀`
case as well, which was already proven over a finer cut; see the
subsection docstring for why that direction was inverted.

`h.some` at `.gamma0` is where the `Nonempty` wrapper on
`IsCompactification` is paid back: `X0.lean`'s theorem wants the
classifying DATUM, this statement carries only its `Prop`-truncation, and
`Nonempty.some` bridges them.  Nothing downstream inspects the datum, so
no information is lost. -/
theorem isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape
    (S : ModularLevelShape) (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : S.IsCompactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o)
    (hL : ∀ χ : DirichletCharacter ℂ N, S.IsNebentypus N χ →
      ∀ (f : CuspForm (S.group N) 2) (a : ℕ → ℂ),
        IsWeightTwoEigenformOn (S.group N) N χ f a →
        ∃ L : ℂ → ℂ, IsLFunctionOf a L ∧ L 1 ≠ 0) :
    letI := ab.addCommGroup (𝟙 SpecQ)
    AddMonoid.IsTorsion (RelPoint jstr (𝟙 SpecQ)) := by
  cases S with
  | gamma0 =>
    exact isTorsion_jacobian_of_lFunction_ne_zero N h.some jac fun f a hf =>
      hL 1 rfl f a ((isWeightTwoEigenformOn_gamma0_iff N f a).2 hf)
  | gamma1 =>
    exact isTorsion_jacobian_of_lFunction_ne_zero_gamma1 N h jac
      fun χ f a hf => hL χ trivial f a hf

section CuspPeriodOn

open Filter Asymptotics MeasureTheory

/-- **Hecke's Mellin transform at `s = 1`, for every group between `Γ₁(N)`
and `Γ₀(N)`: `L(f, 1) = 2π ∫₀^∞ f(iy) dy`** (PROVEN 2026-07-28) — the
group-generic form of `X0.lean`'s `lFunction_apply_one_eq_two_pi_mul_cuspPeriod`,
and the statement of which BOTH that theorem and
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` below are instances.

The proof is `X0.lean`'s, with the group left free.  It is a transposition
and not new mathematics, and that is exactly the claim being made: every
step of the `Γ₀` argument goes through `cuspFEPairOn`,
`isStrongFEPair_cuspFEPairOn`, `mellin_axisRestrictOn` and
`hasSum_axisRestrictOn` — the `HeckeOn` subsection above — none of which
mentions which congruence subgroup `f` lives on.  Writing
`c = 2π/√N` and `Λ = (cuspFEPairOn …).Λ`:

1. `Λ` is ENTIRE (`IsStrongFEPair.differentiable_Λ`); this is where the
   Fricke involution is consumed, through `cuspFEPairOn`;
2. `Λ s = Γ(s) c^{-s} · LSeries a s` on `Re s > 2` (`mellin_axisRestrictOn`),
   so `s ↦ c^s Λ(s)/Γ(s)` is entire — `1/Γ` is entire, so no pole has to be
   dodged — and agrees with `L` there;
3. the identity theorem on `ℂ` gives `L 1 = c · Λ 1`, since `Γ(1) = 1`;
4. `Λ 1 = ∫₀^∞ f(iy/√N) dy` (the Mellin weight is `1` at `s = 1`), and
   `y ↦ y/√N` scales it by `√N` (`integral_comp_mul_left_Ioi`), so
   `Λ 1 = √N · cuspPeriod a` and `L 1 = (2π/√N)·√N·cuspPeriod a`.

**A STALE ROUTE NOTE IS CORRECTED HERE** (2026-07-28).  The leaf below was
dispatched with the instruction "in `ModularCurve/WeightTwoEigenform.lean`,
replace `Gamma0GL N` by a variable `G` in `axisRestrict`, `cuspFEPair`, and
the four analytic leaves" — a real route, but one that had already been
taken, in THIS file rather than that one, by the `HeckeOn` subsection
above.  No edit to `WeightTwoEigenform.lean` was needed or made.  The same
note called those four declarations "leaves"; in `WeightTwoEigenform.lean`
they are PROVEN theorems, and that file contains no `sorry` at all.  What
is open is their group-generic restatements here.

`hN : N ≠ 0` is load-bearing for the reason recorded on the `Γ₀`
statement — at `N = 0` the Fricke matrix is singular and `axisPoint`
divides by `√N`, so the route does not exist; `χ` is inert, the analysis
never looking at the nebentypus, and the eigenform fields `hecke`/`atkin`
are unused, `hf` entering only through `qExpansion`, `qExpansionSummable`
and `isBigO_atTop_coeffOn`. -/
theorem lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn (N : ℕ) (hN : N ≠ 0)
    (G : Subgroup (GL (Fin 2) ℝ)) (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N)
    {χ : DirichletCharacter ℂ N}
    (f : CuspForm G 2) (a : ℕ → ℂ) (hf : IsWeightTwoEigenformOn G N χ f a)
    (L : ℂ → ℂ) (hL : IsLFunctionOf a L) :
    L 1 = 2 * (Real.pi : ℂ) * cuspPeriod a := by
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hcpos : (0 : ℝ) < 2 * Real.pi / Real.sqrt N := by positivity
  have hcC : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hstrong : IsStrongFEPair (cuspFEPairOn N hN G h1 h0 f) :=
    isStrongFEPair_cuspFEPairOn N hN G h1 h0 f
  -- `s ↦ c^s Λ(s) / Γ(s)` is entire: `Λ` is entire and `1/Γ` is entire.
  have hFentire : AnalyticOnNhd ℂ
      (fun s : ℂ => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (cuspFEPairOn N hN G h1 h0 f).Λ s * (Complex.Gamma s)⁻¹) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact ((differentiable_id.const_cpow (Or.inl hcC)).mul
      hstrong.differentiable_Λ).mul Complex.differentiable_one_div_Gamma
  -- and it is the Dirichlet series on `Re s > 2`
  have hFeq : ∀ s : ℂ, 2 < s.re →
      ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s * (cuspFEPairOn N hN G h1 h0 f).Λ s *
        (Complex.Gamma s)⁻¹ = LSeries a s := by
    intro s hs
    have hΛ : (cuspFEPairOn N hN G h1 h0 f).Λ s =
        Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
      rw [congr_fun hstrong.Λ_eq s]
      exact mellin_axisRestrictOn hN h1 hf hs
    have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcancel : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hcC, add_neg_cancel, Complex.cpow_zero]
    rw [hΛ, show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s) *
        (Complex.Gamma s)⁻¹
      = (((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
          ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) * LSeries a s from by ring,
      hcancel, mul_inv_cancel₀ hΓ, one_mul, one_mul]
  -- identity theorem: two entire functions agreeing on `Re s > 2` agree at `s = 1`
  have hL1 : L 1 =
      ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) * (cuspFEPairOn N hN G h1 h0 f).Λ 1 := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (3 : ℂ) ∈ {z : ℂ | 2 < z.re} := by norm_num
    have key : Set.EqOn L (fun s : ℂ => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (cuspFEPairOn N hN G h1 h0 f).Λ s * (Complex.Gamma s)⁻¹) Set.univ := by
      refine hL.entire.eqOn_of_preconnected_of_eventuallyEq hFentire isPreconnected_univ
        (Set.mem_univ (3 : ℂ)) ?_
      filter_upwards [hopen.mem_nhds hmem] with z hz
      rw [hL.eq_lseries z hz, hFeq z hz]
    have := key (Set.mem_univ (1 : ℂ))
    simpa [Complex.cpow_one, Complex.Gamma_one] using this
  -- the completed transform at `s = 1` is `√N` times the period
  have hΛ1 : (cuspFEPairOn N hN G h1 h0 f).Λ 1 = ((Real.sqrt N : ℝ) : ℂ) * cuspPeriod a := by
    have hmel : (cuspFEPairOn N hN G h1 h0 f).Λ 1 =
        ∫ y in Set.Ioi (0 : ℝ), axisRestrictOn G N f y := by
      rw [congr_fun hstrong.Λ_eq 1]
      simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
      rfl
    have hpt : ∀ y ∈ Set.Ioi (0 : ℝ), axisRestrictOn G N f y =
        (fun u : ℝ => ∑' n : ℕ,
            a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ))))
          ((Real.sqrt N)⁻¹ * y) := by
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      have h := (hasSum_axisRestrictOn hN hf hy').tsum_eq
      rw [← h]
      refine tsum_congr fun n => ?_
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hint : (∫ y in Set.Ioi (0 : ℝ), axisRestrictOn G N f y)
        = ∫ y in Set.Ioi (0 : ℝ), (fun u : ℝ => ∑' n : ℕ,
            a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ))))
          ((Real.sqrt N)⁻¹ * y) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt
    rw [hmel, hint,
      MeasureTheory.integral_comp_mul_left_Ioi (fun u : ℝ => ∑' n : ℕ,
        a (n + 1) * Complex.exp (-(2 * (Real.pi : ℂ) * (n + 1) * (u : ℂ)))) 0
        (inv_pos.mpr hsq)]
    rw [cuspPeriod]
    rw [mul_zero, inv_inv, Complex.real_smul]
  rw [hL1, hΛ1]
  have hsqC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
  push_cast
  field_simp

end CuspPeriodOn

/-- **Hecke's Mellin transform at `s = 1` on `Γ₁(N)`:
`L(f, 1) = 2π ∫₀^∞ f(iy) dy`** (**PROVEN 2026-07-28**, as the instance
`G = Γ₁(N)` of `lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn` above;
formerly a `sorry` leaf) — the `Γ₁`
transposition of `X0.lean`'s **PROVEN**
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod`.  LEVEL-FREE and
NEBENTYPUS-FREE: it is the whole of the *analysis* under
`lFunction_apply_one_ne_zero_x1TwentyFive` below, and `25` does not
appear in it.

**THIS IS NOW AN ASSEMBLY, NOT A LEAF.**  It is
`lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn_of_le` (in the `HeckeOn`
subsection above) at `G = Γ₁(N)`, with the two side conditions `le_rfl`
and `gamma1GL_le_gamma0GL`.  **The route the sections below prescribe was
right about what was needed and wrong about where it was**: the
group-generic machinery it asks for does not have to be built in
`WeightTwoEigenform.lean`, because it was already built HERE on
2026-07-28 — `axisRestrictOn`, `exists_frickeInvolutionOn`,
`cuspFEPairOn`, `isStrongFEPair_cuspFEPairOn`, `hasSum_axisRestrictOn`,
`mellin_axisRestrictOn`, all PROVEN, for the sake of
`exists_isLFunctionOf_of_isWeightTwoEigenformOn_of_le`.  So the whole
cost of closing this node was writing the *second* consumer of that
machinery, which is the `Γ₀` proof with two names changed and no step of
the argument altered.

The analysis below is therefore a correct account of the mathematics and
an obsolete account of the frontier; it is kept because the `Γ₁`-specific
fact it records — that `W_N` normalises `Γ₁(N)`, computed out in full —
is the one input the `Γ₀` docstring does not contain, and it is what
makes `exists_frickeInvolutionOn` applicable at `G = Γ₁(N)`.

TRUE, and it is the SAME classical theorem as the `Γ₀` one rather than an
analogue of it.  Writing `Λ(s) = ∫₀^∞ f(iy/√N) y^{s-1} dy`:

* for `Re s > 2`, termwise integration of the `q`-expansion gives
  `Λ(s) = Γ(s) (2π/√N)^{-s} L(s)` (mathlib's `hasSum_mellin`);
* `Λ` is entire because `f` decays exponentially at BOTH ends of the
  imaginary axis — at `y → ∞` from the `q`-expansion, at `y → 0` from
  the Fricke functional equation, `f` being cuspidal at every cusp;
* so `s ↦ (2π/√N)^s Λ(s) / Γ(s)` and `L` are entire and agree on
  `Re s > 2`, hence everywhere by the identity theorem, and at `s = 1`
  (`Γ(1) = 1`) this reads `L 1 = (2π/√N)·Λ(1) = 2π · cuspPeriod a`,
  since `Λ(1) = ∫₀^∞ f(iy/√N) dy = √N · cuspPeriod a` by the change of
  variables `y ↦ y/√N`.

### WHY THIS WAS A LEAF AND NOT AN APPLICATION OF THE `Γ₀` THEOREM

(Historical, and it is the diagnosis that turned out to be correct — the
hoist it prescribes is what `lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn_of_le`
now is.)

`X0.lean`'s theorem is proven, and **its proof uses nothing about
`Γ₀(N)` beyond the TYPE of `f`.**  All of it — `axisPoint`,
`axisRestrict`, `cuspFEPair`, `hasSum_axisRestrict`,
`mellin_axisRestrict`, `isStrongFEPair_cuspFEPair` and the identity-
theorem assembly itself — is written against `CuspForm (Gamma0GL N) 2`
purely because that is the type it was first needed at.  So the two
statements cannot be shared TODAY (a `Γ₁(N)` cusp form is not a `Γ₀(N)`
cusp form unless `χ = 1`), and they will be ONE statement the moment the
machinery upstream is group-generic.

**THE ROUTE BELOW WAS ALREADY TAKEN, IN THIS FILE, AND THE PARAGRAPH IS
KEPT ONLY BECAUSE ITS MATRIX COMPUTATION IS STILL WANTED** (2026-07-28).
The generalisation it prescribes is the `HeckeOn` subsection above —
`axisRestrictOn`, `cuspFEPairOn`, `mellin_axisRestrictOn` and the
group-generic quartet — so this leaf closed by citing
`lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn` and **no edit to
`WeightTwoEigenform.lean` was made**.  Two corrections to the text that
follows: that file's four declarations are called "leaves" here but are
PROVEN theorems there (`WeightTwoEigenform.lean` contains no `sorry` at
all — what is open is their group-generic restatements above); and the
`W_N` normalisation computation written out below is the justification of
`exists_frickeInvolutionOn`'s upper bound `G ≤ Γ₀(N)`, which is where it
is now consumed.

**The route, and it is a small mechanical diff, not a theory.**  In
`ModularCurve/WeightTwoEigenform.lean`, replace `Gamma0GL N` by a
variable `G : Subgroup (GL (Fin 2) ℝ)` in `axisRestrict`, `cuspFEPair`,
and the four analytic leaves.  Three of the four never mention `Γ₀` in
their *content* at all —

* `isBigO_atTop_axisRestrict` (a cusp form decays faster than every power
  at `i∞`),
* `locallyIntegrableOn_axisRestrict` (continuity through the `ℍ`
  coercion),
* `isBigO_atTop_coeff` (`|aₙ| = O(n)`, the Petersson bound),

— and transpose verbatim.  The one that does is `exists_frickeInvolution`,
whose statement is "`W_N` normalises the group, so `f ∣[2] W_N` is again
a cusp form on it".

**And `Γ₁(N)` IS normalised by `W_N`.**  This is the one fact the
transposition needs that the `Γ₀` docstring does not record, so it is
written out here.  With `W_N = ![![0, -1], ![N, 0]]`, so that
`W_N⁻¹ = (1/N)·![![0, 1], ![-N, 0]]`, a direct multiplication gives, for
`γ = ![![a, b], ![c, d]]`,

> `W_N γ W_N⁻¹ = ![![d, -c/N], ![-N b, a]]`.

Read off the three `Γ₁(N)` conditions on the right-hand side: its
`(0,0)` entry is `d ≡ 1`, its `(1,1)` entry is `a ≡ 1`, its `(1,0)`
entry is `-Nb ≡ 0`, and its `(0,1)` entry `-c/N` is an INTEGER exactly
because `N ∣ c`.  Its determinant is `ad - bc = 1`.  So
`W_N Γ₁(N) W_N⁻¹ = Γ₁(N)`, and the Fricke involution preserves
`S₂(Γ₁(N))` — which is the familiar `W_N : S₂(N, χ) → S₂(N, χ̄)`, the
nebentypus conjugation being invisible at the level of `Γ₁(N)`.  (That
conjugation is also why the FE-pair partner `g` must be allowed to be a
*different* form, which `exists_frickeInvolution` already permits: it
existentially quantifies `g` and never claims `g = ±f`.)

**FAITHFULNESS.**  `hN : N ≠ 0` is load-bearing for exactly the reason
recorded in the `FALSITY AUDIT` on the `Γ₀` statement, and the
counterexample transports verbatim: `Γ₁(0) = ⟨T⟩`, so
`CuspForm (Gamma1GL 0) 2` is just "holomorphic, `1`-periodic, `→ 0` at
`i∞`"; `hecke` is vacuous at `N = 0` (every prime divides `0`) and
`atkin` then says only that `a` is completely multiplicative; so
`a n = 1` for `n ≥ 1` with `f (τ) = q/(1 − q)` satisfies every field, and
`LSeries a = riemannZeta` has a POLE at `s = 1`, so no entire `L` agrees
with it on `Re s > 2`.

`χ` is inert here — the analysis never looks at the nebentypus, and a
prover may `omit` it.  It is carried only so that the hypothesis is
literally the one `lFunction_apply_one_ne_zero_x1TwentyFive` holds.  For
the same reason the eigenform fields `hecke`/`atkin` are not used either;
what IS used is `qExpansion`, `qExpansionSummable` and `zero`. -/
theorem lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1 (N : ℕ) (hN : N ≠ 0)
    (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (Gamma1GL N) N χ f a)
    (L : ℂ → ℂ) (hL : IsLFunctionOf a L) :
    L 1 = 2 * (Real.pi : ℂ) * cuspPeriod a :=
  lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn N hN (Gamma1GL N) le_rfl
    (gamma1GL_le_gamma0GL N) f a hf L hL

/-- **The period `∫₀^∞ f(iy) dy` of a weight-two eigenform of
`S₂(Γ_1(25))` is nonzero** (sorry leaf, NEW 2026-07-28) — the ARITHMETIC
half of `lFunction_apply_one_ne_zero_x1TwentyFive` below, and the ONLY
declaration in this cluster that mentions the level `25`.

After the cut it contains no `L`-function, no scheme, no Jacobian and no
abelian variety: it is a statement about a convergent integral of a
`q`-expansion.  It is the exact `Γ₁(25)` counterpart of `X0.lean`'s
`cuspPeriod_ne_zero_of_kenkuLevel`, and it shares its subject `a` with
it, `cuspPeriod` being defined on the coefficient sequence alone.

TRUE: the twelve values are tabulated on
`lFunction_apply_one_ne_zero_x1TwentyFive` below, all nonzero, the
smallest `|L(f, 1)| = 0.4212…`; by
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` above a nonzero
`L`-value is a nonzero period and conversely, so the table is a
reconnaissance for this statement just as much as for that one.

*Re-run a THIRD time on 2026-07-28* (PARI/GP 2.17.4, `znstar(25,1)`,
`mfinit([25,2,[G,[k]]],1)` for `k = 0..19`, `mfeigenbasis`, `mffields` to
split single-embedding spaces from multi-, `lfun(lfunmf(·), 1)` at every
embedding).  Every digit of the recorded table reproduced: eight nonzero
characters at `k = 2, 4, 6, 8, 12, 14, 16, 18`, `newdim = cuspdim` in all
eight, `Σ newdim = 12`, `12` embeddings, `0` vanishing,
`min |L(f, 1)| = 0.421217773477606542527525787430`.  PARI/GP is an
untrusted searcher: this establishes that the statement is not false, and
is not a proof.

### WHAT A PROVER MUST BUILD, and one gate that is ABSENT here

`X0.lean`'s sibling records that the first thing its prover must write is
the reduction to newforms, because `IsWeightTwoEigenform` admits the
`p`-stabilizations of forms of every level `M ∣ N` alongside the newforms
themselves.  **At `N = 25` that step is free**, and this is the one
respect in which this leaf is genuinely cheaper than the `Γ₀` one: the
divisors of `25` are `1`, `5`, `25`, and `X_1(1)` and `X_1(5)` both have
genus `0`, so `S₂(Γ_1(1)) = S₂(Γ_1(5)) = 0` and there are no oldforms and
no stabilizations to strip.  That is visible in the reconnaissance as
`newdim = cuspdim` in every one of the eight nonzero characters.

Two consequences.  First, every `a` admitted by `hf` is the expansion of
a NEWFORM, hence a `W_25`-eigenform up to the nebentypus conjugation
`χ ↦ χ̄`; so the Fricke cut that `X0.lean` records as unavailable *before*
the reduction to newforms is available here immediately.  Second, that
cut is what makes the numerics finite: splitting `Λ(1)` at `y = 1` and
applying the functional equation turns the period into

> `2π · cuspPeriod a = (2π/5)·(∑_{n≥1} (aₙ/n) e^{-2πn/5}
>   + ε ∑_{n≥1} (ā ₙ/n) e^{-2πn/5})`,

with `e^{-2π/5} = 0.2846…`, so the tail after `n` terms is
`O(0.285ⁿ)` and separating `0.42` from `0` needs on the order of twenty
coefficients — which is what "the precision demanded is modest" means.

**The gate that remains, and it is the real one.**  The statement
quantifies over EVERY `(χ, f, a)` satisfying `hf`, so a proof must first
know that `hf` pins `a` to one of the twelve tabulated sequences.  That
needs an explicit certified basis of `S₂(Γ_1(25))` — dimension formulas
per nebentypus, the eigenbasis, and proven `q`-expansion coefficients —
and none of that exists at this pin.  This is the same missing theory that
`X0.lean` names as "the axis not searched" on its own period leaf, and
closing it closes both.

**THE GREP CLAIM ABOVE WAS WRONG, AND IS CORRECTED HERE** (2026-07-28, by
running it).  The recorded check —
`grep -rn "newform\|Newform\|oldform\|degeneracy\|eigenbasis" Fermat/
.lake/packages/mathlib/ ~/cs/FLT/` — was said to have "returned nothing".
It returns nothing on **mathlib** and on **`~/cs/FLT`**, and that half is
right.  It returns a great deal on `Fermat/`, and the following are real
declarations, not prose:

* `X0.lean`: `IsOldEigenformAt`, `IsNewEigenformAt`, `IsFrickeEigenform`,
  and a whole `CuspPeriodReduction` section culminating in
  `cuspPeriod_ne_zero_of_isNewEigenformAt`;
* `Modularity/Interface.lean`: `degeneracyTransform`, `degeneracyOp`,
  `degeneracyOp_injective`, `qCoeff_degeneracyOp`, `IsWeightTwoNewform`,
  `exists_weightTwoNewform_of_weightTwoEigenform`.

**What that changes, and what it does not.**  It does *not* discharge this
leaf, and the "gate that remains" above still stands: none of the above is
a certified `q`-expansion basis of `S₂(Γ_1(25))`, which is what pins `a`.
Two specific reasons the `Γ₀` machinery does not transpose, both checked:

1. **`25 ∉ kenkuLevels`** (`= [20, 24, 26, 28, 30, 35, 36, 39, 42, 45, 50,
   54, 63, 75]`), and every theorem in `CuspPeriodReduction` carries
   `hN : N ∈ kenkuLevels`.
2. `IsFrickeEigenform` is stated over `CuspForm (Gamma0GL M) 2`, and — more
   fundamentally — **no eigenform of `S₂(Γ_1(25))` is a Fricke eigenform at
   all**.  `W_25` sends `S₂(25, χ)` to `S₂(25, χ̄)`, so `f ∣ W_25` is a
   multiple of `f` only when `χ² = 1`; the eight characters carrying the
   space are `ψ^k` for `k = 2, 4, 6, 8, 12, 14, 16, 18`, and `ψ^k` is real
   only for `k = 0, 10`, at which the space is ZERO.  So the `Γ₀` identity
   `cuspPeriod b = (1 - ε)·(√M)⁻¹·∫₁^∞ …` has no `Γ₁(25)` instance: the
   correct relation couples `a` with the coefficients of the partner form
   of conjugate nebentypus, which is the two-tail formula displayed above.

This is why the axis note below — "a cut that isolates the Fricke sign `ε`
is a real decomposition but is worth nothing on its own" — survives the
correction: the Fricke cut is not merely low-value here, its `Γ₀` form is
not even available.

**The axis searched, so the next reader need not redo it.**  A cut on the
character `χ` (eight cases) is mechanically available and is *not* a
decomposition: it moves no theory and multiplies the frontier by eight.
A cut that isolates the Fricke sign `ε` is a real decomposition but is
worth nothing on its own, because the sum above still needs the certified
`aₙ`; it becomes worth writing at the moment the basis does.

**THE JUNK-VALUE REFUTATION DOES NOT RUN HERE, and it is worth saying so
because the shape of it has killed two statements in this cluster
already** (checked 2026-07-30 against `X0.lean`'s definition).  The
obvious way for a period leaf to be FALSE in Lean is the one that made
`IsWeightTwoEigenformOn` unsound before `qExpansionSummable` was added: a
`tsum` of a non-summable family takes its junk value `0`, so a statement
"the period is nonzero" is refuted for EVERY eigenform at once.  And the
naive spelling of this period invites exactly that — Hecke's bound gives
`aₙ = O(n^{1/2+ε})`, hence `aₙ/n = O(n^{-1/2+ε})`, which converges only
CONDITIONALLY; had `cuspPeriod` been `∑' n, aₙ / n` it would be `0`
identically and this leaf would be false with no arithmetic input
whatsoever.

It is not: `cuspPeriod` is a Bochner INTEGRAL
`∫ y in Ioi 0, ∑' n, a (n+1) * exp (-(2π (n+1) y))`, whose integrand's
inner `tsum` is summable at every `y > 0` (geometric decay) and which is
integrable because `f (iy)` decays exponentially at BOTH ends — at `∞`
from the `q`-expansion and at `0` because `f` vanishes at the cusp `0`,
`Γ_1(25)` having finite index.  So the gate really is the certified basis
above and nothing cheaper. -/
theorem cuspPeriod_ne_zero_x1TwentyFive (χ : DirichletCharacter ℂ 25)
    (f : CuspForm (Gamma1GL 25) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (Gamma1GL 25) 25 χ f a) :
    cuspPeriod a ≠ 0 :=
  sorry

/-- **`L(f, 1) ≠ 0` for every weight-two eigenform on `Γ_1(25)`** (PROVEN
2026-07-28 from the two leaves above) — the ONLY genuinely
level-specific input left under
`hasRankZeroJacobian_x1TwentyFive`, and the `Γ₁(25)` counterpart of
`X0.lean`'s `lFunction_apply_one_ne_zero_of_kenkuLevel`.

It contains no arithmetic geometry at all: no scheme, no Jacobian, no
abelian variety.  Everything geometric under the rank-`0` claim has moved
to `isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` above, which
is shared with the `Γ₀` layer.

**FALSITY AUDIT (2026-07-27) — THIS LEAF WAS FALSE AS STATED, and the
repair is one field on `IsWeightTwoEigenformOn`, not one word here.**

The statement below is UNCHANGED.  What changed is `hf`: until today
`IsWeightTwoEigenformOn` had no `qExpansionSummable` field, and without
it this leaf had an explicit counterexample.  Recording it, because a
future editor tempted to "simplify" that field away is re-breaking this
leaf, not tidying a structure:

* `χ := 1`, `f := 0`, and `a` the multiplicative sequence with
  `a p := 2 ^ (p ^ 2)` at every prime `p ≠ 5`, `a 5 := 0`, extended over
  prime powers by `a_{p^{k+1}} = a p · a_{p^k} − χ(p)·p·a_{p^{k-1}}` — the
  `hecke` field itself, which bounds the size of `a p` not at all.
* `qExpansion` holds with both sides `0`: along the primes
  `|a p · q^p| = exp (p² log 2 − 2π p · Im τ) → ∞` for every `τ ∈ ℍ`, so
  the family is not summable, and `tsum` of a non-summable family is `0`.
  `zero`, `one`, `hecke`, `atkin` hold by construction.
* `L := 0` then satisfies `IsLFunctionOf a L`: it is entire, and
  `|a p · p^{-s}| = 2^{p²} p^{-Re s} → ∞` makes `LSeries a s` non-summable
  for every `s`, hence `LSeries a s = 0` on `Re s > 2`.
* So `L 1 = 0`, contradicting the conclusion.

Two consequences beyond this leaf, both repaired by the same field:

1. `isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` was VACUOUS at
   `.gamma1 25` — and at `.gamma0 N` too, since it quantifies over the
   same predicate.  For the junk `a` above, ANY `L` with
   `IsLFunctionOf a L` is `0` by `isLFunctionOf_apply_eq`, so its `hL`
   demanded `0 ≠ 0` and was unsatisfiable.  A leaf whose hypothesis
   cannot hold proves nothing about `J_1(25)(ℚ)`, which is the failure
   mode that subsection's own docstring says it was written to avoid.
2. The bridge `isWeightTwoEigenformOn_gamma0_iff` recorded in the
   subsection docstring was unprovable in the `→` direction.

`X0.lean`'s `lFunction_apply_one_ne_zero_of_kenkuLevel` was FALSE for the
identical reason and was repaired the identical way; this is that repair
transported, not a new one.  With the field, the `q`-series converges on
all of `ℍ`, so its Taylor coefficients in `q` are unique, `a` really is
determined by `f`, `f = 0` forces `a = 0`, and `a 1 = 1` rules the junk
out.

TRUE as now stated, and here is the complete verification.

**RECONNAISSANCE (PARI/GP 2.17.4, 2026-07-27, EXHAUSTIVE — every
eigenform, not a sample).**  `S_2(Γ_1(25)) = ⊕_χ S_2(25, χ)` over the
twenty Dirichlet characters mod `25`.  Writing characters as powers
`χ = ψ^a` of a generator `ψ` of the cyclic group `(ℤ/25)ˣ ≅ ℤ/20`, the
spaces are nonzero for exactly eight values of `a`, and the whole space
is NEW at level `25` (`newdim = cuspdim` in every case), as it must be
since `genus X_1(5) = 0` leaves no oldforms:

| `a` | `dim S_2(25, ψ^a)` | `|L(f, 1)|` at each embedding |
|---|---|---|
| 2 | 2 | `0.5645…`, `0.4212…` |
| 4 | 1 | `0.5306…` |
| 6 | 2 | `0.5860…`, `0.4386…` |
| 8 | 1 | `0.5134…` |
| 12 | 1 | `0.5134…` |
| 14 | 2 | `0.5860…`, `0.4386…` |
| 16 | 1 | `0.5306…` |
| 18 | 2 | `0.5645…`, `0.4212…` |

`Σ_χ dim S_2(25, χ) = 12`, matching `x1Genus_twentyFive`'s `decide`d
`genus X_1(25) = 12` — an independent check that the character
decomposition is complete.  All **12** embeddings were evaluated and
`vanishing = 0`; the smallest is `|L(f, 1)| = 0.4212…`.  The `L`-values
repeat in conjugate pairs `(2, 18)`, `(4, 16)`, `(6, 14)`, `(8, 12)`
exactly as the Galois action on characters predicts, which is a third
consistency check.  PARI/GP is an untrusted searcher: this establishes
that the statement is not false, and is not a proof.

*Independently re-run on 2026-07-27* by the owner of the falsity audit
above, from a script written without reference to this table
(`znstar(25,1)` has `cyc = [20]`; `mfinit([25,2,[G,[a]]],1)` for
`a = 0..19`, `mfeigenbasis` on the newspace, `lfun(lfunmf(...), 1)` at
every embedding).  Every entry reproduced to the digits printed here:
eight nonzero characters, `newdim = cuspdim` throughout, `Σ dim = 12`,
`12` embeddings evaluated, `0` vanishing, and
`min |L(f, 1)| = 0.42121777347760654…`.  Reproducing the numerics is what
makes the repair above a *correction* rather than a retraction: the leaf
was false only in its HYPOTHESIS, and is true as now stated.  (The `A₄ × A₈`
description in this module's opening docstring is the same fact read
through Eichler–Shimura: the four `dim 2` orbits assemble the
`8`-dimensional factor and the four `dim 1` orbits the `4`-dimensional
one.)

**The level is load-bearing** and `25` may not be generalized: `L(f, 1)`
vanishes for the newform of level `37` and at every level of positive
analytic rank, so the analogous statement is FALSE for most `N`.

`hf` is load-bearing in both of its halves.  `qExpansion` pins `a` as the
expansion of a genuine cusp form — without it `a` ranges over
junk sequences satisfying the recursions, for which no `L`-function
statement is true — and the eigenform conditions are what make `a`
multiplicative, hence what make `L(a, s)` an Euler product rather than an
arbitrary Dirichlet series.

**DECOMPOSED 2026-07-28, ALONG THE PERIOD — this node is no longer a
leaf.**  It used to carry two unrelated theories at once, and the seam
between them is Hecke's Mellin transform at `s = 1`.  Above the seam is
the ANALYSIS, `L 1 = 2π · cuspPeriod a`
(`lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1`, LEVEL-FREE);
below it is the ARITHMETIC, `cuspPeriod a ≠ 0`
(`cuspPeriod_ne_zero_x1TwentyFive`, the only place `25` survives).  The
assembly is a rewrite plus "a product of nonzero complex numbers is
nonzero", `2π ≠ 0`.

**This is exactly the cut `X0.lean` already made** at
`lFunction_apply_one_ne_zero_of_kenkuLevel`, with `cuspPeriod` — which is
defined on the coefficient sequence `a` alone, and is therefore already
shared between the two layers — as the common seam.  The old note here
saying the two layers' computations are "NOT captured by a common
statement" was right about the arithmetic half and **wrong about the
analytic half**: `lFunction_apply_one_eq_two_pi_mul_cuspPeriod` is
proven, level-free, and uses nothing about `Γ₀(N)` beyond the type of
`f`, so the two analytic halves become ONE declaration as soon as
`ModularCurve/WeightTwoEigenform.lean` is made group-generic.  The route
for that — including the matrix computation showing `W_N` normalises
`Γ₁(N)` — is written out on
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` above.

What remains genuinely level-`25` is therefore only
`cuspPeriod_ne_zero_x1TwentyFive`: a modular-symbol or explicit-period
computation of the twelve values above to enough precision to separate
them from zero — the smallest being `0.42`, so the precision demanded is
modest.  Unlike its `Γ₀` sibling it needs no reduction to newforms, the
space at level `25` being entirely new; see that leaf for what the
computation still costs. -/
theorem lFunction_apply_one_ne_zero_x1TwentyFive (χ : DirichletCharacter ℂ 25)
    (f : CuspForm (Gamma1GL 25) 2) (a : ℕ → ℂ)
    (hf : IsWeightTwoEigenformOn (Gamma1GL 25) 25 χ f a)
    (L : ℂ → ℂ) (hL : IsLFunctionOf a L) : L 1 ≠ 0 := by
  rw [lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1 25 (by norm_num) χ f a hf L hL]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (cuspPeriod_ne_zero_x1TwentyFive χ f a hf)

end KolyvaginLogachev

/-- **`rank J_1(25)(ℚ) = 0`, i.e. `J_1(25)(ℚ)` is a TORSION group**
(PROVEN 2026-07-27, over the subsection above, of which exactly ONE open
leaf — the `L`-value computation — is specific to this level; the other
two open leaves are the `Γ₁` halves of theories whose `Γ₀` halves are
proven in `X0.lean` / `WeightTwoEigenform.lean`).

The assembly is the shape of the classical argument:
`exists_isLFunctionOf_of_isWeightTwoEigenformOn` (Hecke) produces the
`L`-function of each normalized eigenform of `S_2(Γ_1(25))`;
`lFunction_apply_one_ne_zero_x1TwentyFive` (numerics) says it does not
vanish at `s = 1`; and
`isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape` (Eichler–Shimura
plus Kolyvagin–Logachev) converts that analytic input into the arithmetic
conclusion.  It is the exact mirror of `X0.lean`'s
`isTorsion_jacobian_of_kenkuLevel`, and the first and third steps are now
literally the same declarations that file's assembly uses, reached
through their `.gamma0`/`.gamma1` branches rather than duplicated.

`N ≠ 0` is discharged by `norm_num` at `N = 25`, and the nebentypus side
condition by `trivial`, `.gamma1` admitting every `χ` — which is exactly
the decomposition `S_2(Γ_1(25)) = ⊕_χ S_2(25, χ)` the reconnaissance on
`lFunction_apply_one_ne_zero_x1TwentyFive` enumerates.

TRUE.  `X_1(25)` has genus `12` (`x1Genus_twentyFive`), and `J_1(25)` is
`ℚ`-isogenous to `A₄ × A₈` — the two newform factors of `S_2(Γ_1(25))`,
of dimensions `4` and `8`.  Evaluating the `L`-function of each factor at
`1` gives `LRatio(A₄, 1) = 1/5041` and `LRatio(A₈, 1) = 1/10272025`, both
NONZERO, so `J_1(25)` has analytic rank `0` and hence Mordell–Weil rank
`0` by Kolyvagin–Logachev (or Kato).  For a finitely generated abelian
group rank `0` is exactly torsion, which is what is stated.

RECONNAISSANCE.  The partial sweep once recorded here has been COMPLETED
and moved, with the full table of all twelve embeddings, to
`lFunction_apply_one_ne_zero_x1TwentyFive` — the leaf that now carries
the `L`-value claim.  In summary: `Σ_χ dim S_2(25, χ) = 12`, matching the
genus; the space is entirely new; all twelve `L(f, 1)` are nonzero, the
smallest in absolute value being `0.4212…`.

**Why TORSION and not FINITENESS**, which is the seam this leaf now sits
on and the reason it is cheaper than it was.  Rank `0` and finiteness are
the same statement only *given* Mordell–Weil, and Mordell–Weil is a
general theorem about abelian varieties with nothing to do with modular
curves.  Keeping them together made one leaf carrying two unrelated
theories.  Separated, `X0.lean`'s `fg_relPoint_of_abelianScheme` holds
the general half — it is stated for an arbitrary abelian scheme over `ℚ`
and is reused here VERBATIM, not restated — and this leaf holds exactly
the Kolyvagin–Logachev half.  The two are recombined by
`AddCommGroup.finite_of_fg_torsion` in
`hasRankZeroJacobian_x1TwentyFive`, exactly as
`finite_jacobian_of_kenkuLevel` does on the `Γ₀` side.

`h` is load-bearing and may not be dropped: it pins `X` as `X_1(25)`.
`jac` is load-bearing too — the conclusion is FALSE for an arbitrary
abelian scheme over `ℚ` receiving `X`, and true only because `jac` pins
`J` as the Jacobian of this particular curve, whose `L`-function is the
one being evaluated.

**THE CUT, and why it is not a second Kolyvagin–Logachev.**  The previous
version of this docstring proposed exactly the interface that now exists:
"a single Kolyvagin–Logachev interface phrased over an abelian variety
whose `L`-function is nonvanishing at `1` would serve both, and writing
that interface — not proving it — is the natural next cut for either
owner."  That is what the subsection above does, with one correction the
proposal did not anticipate: the interface cannot be phrased over a bare
abelian variety, because "the `L`-functions belonging to `J`" is
meaningful only once `X` is pinned as a modular curve, and it cannot be
phrased over `Γ₀` alone either, because a `Γ₁` form has a NEBENTYPUS.
Both corrections are carried by `ModularLevelShape`.

What is left here is therefore only the level-`25` `L`-value input.  The
three theories the original leaf carried — Hecke's continuation,
Eichler–Shimura + Kolyvagin, and the `L`-value numerics — are now three
named leaves, and **two of the three are shared with the `Γ₀` layer
rather than duplicated**, which is the difference between this cut and
the one a naive `Γ₁` mirror would have produced. -/
theorem isTorsion_jacobian_x1TwentyFive {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification 25 strX strY jY)
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    letI := ab.addCommGroup (𝟙 SpecQ)
    AddMonoid.IsTorsion (RelPoint jstr (𝟙 SpecQ)) :=
  isTorsion_jacobian_of_lFunction_ne_zero_of_levelShape .gamma1 25 ⟨h⟩ jac
    fun χ _ f a hf =>
      let ⟨L, hLf⟩ :=
        exists_isLFunctionOf_of_isWeightTwoEigenformOn .gamma1 25 (by norm_num) χ trivial f a hf
      ⟨L, hLf, lFunction_apply_one_ne_zero_x1TwentyFive χ f a hf L hLf⟩

/-- **THE GENUS FORMULA AT `Γ₁`, GEOMETRICALLY: over an ALGEBRAICALLY
CLOSED field no fibre of `X_1(N)` is a rational curve when
`genus X_1(N) ≥ 1`** (sorry leaf, cut 2026-07-30) — the arithmetic half of
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` below, and after
that cut the ONLY declaration in the `Γ₁` genus formula that mentions `N`.

TRUE, and it is Diamond–Shurman Thm 3.1.1 and NOTHING ELSE.  `hmodel`
makes the fibre `X_K = X ×_S Spec K` a smooth proper connected curve which
is the `X_1(N)` of `K`; `hg` with `hN` says its genus is `≥ 1`; genus is a
birational invariant and `𝔸¹_K` has genus `0`.  Over an algebraically
closed field that is the whole argument: Riemann–Roch is available, closed
points are rational, and "not birational to `𝔸¹`" IS "genus `≥ 1`" with no
descent anywhere.

**WHY THE `IsAlgClosed K`, AND WHY THIS IS NOT A DUPLICATE OF
`not_birationalOver_affineLine_of_one_le_x1Genus` BELOW.**  That
declaration is the SAME statement over an ARBITRARY field, and it is a
THEOREM, not an input: it is proven from
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus`, which is proven
from this leaf together with the level-free geometric leaf below.  So the
general form is a CONSEQUENCE of the algebraically closed form and there
is no cycle — what the geometric leaf needs, and all it needs, is the
algebraically closed case, and that case is strictly the easier one.  The
economy of the cut is exactly this: a prover of this leaf owes the genus
formula and owes NO abelian variety, no `Pic⁰` and no Galois descent.

**BOTH ARITHMETIC HYPOTHESES ARE LOAD-BEARING and each makes the leaf
FALSE if dropped**, with the same witnesses the node below carries.

* `hg` — `X_1(5)` is the witness INSIDE the validity range
  (`x1Genus 5 = 0`, and `5 ≤ 5`): it is `ℙ¹`, which contains `𝔸¹` as a
  dense open and so IS birational to `𝔸¹_K` over `K`.
* `hN : 5 ≤ N` — see the VALIDITY RANGE note on `x1Genus`.  At `N = 1` the
  definition evaluates to `x1Genus 1 = 1`, so `hg` is satisfiable while
  `X_1(1) = ℙ¹` has genus `0`.  **`N = 0` is a SECOND witness and was not
  previously recorded**: `x1Genus 0 = 1` as well.

  All of these are `decide`-computable and were CHECKED against the
  compiler on 2026-07-30, in a scratch module transcribing `gammaOneIndex`,
  `numCuspsX1` and `x1Genus` verbatim — `x1Genus 0 = 1`, `x1Genus 1 = 1`,
  `x1Genus 2 = x1Genus 3 = x1Genus 4 = 0`, `x1Genus 5 = 0`,
  `gammaOneIndex 1 = 0`, `numCuspsX1 1 = 0`, `gammaOneIndex 25 = 300`,
  `numCuspsX1 25 = 28`, `x1Genus 25 = 12`.  They had been prose until then;
  the falsity audit of this leaf and of the node below rests on them, so
  they are now compiler-checked facts rather than claims.  (The check does
  not live in the tree as theorems because nothing would consume them —
  see the free-floating policy.)  `x1Genus 11 = 1` and `x1Genus 10 = 0`
  were checked at the same time: inside the validity range the genus first
  turns positive at `N = 11`, so `N = 10` is a further `hg` witness that
  needs no out-of-range level at all.
* `hmodel` is load-bearing twice over — it supplies the curve conditions
  AND it is the only thing tying the arithmetic `x1Genus N` to the
  geometry of `strX`.  `N` enters only through `hg`, `hN` and `hmodel`.

**NOT VACUOUS**: `Scheme.BirationalOver _ (𝔸(Unit; Spec K) ↘ _)` is
satisfiable — it holds for `𝔸¹_K` itself by `BirationalOver.refl`, and for
any smooth proper rational curve since a dense open is birational to the
whole (`Opens.birationalOver_of_dense`).  So the conclusion is a real
constraint.

**A FAITHFULNESS AXIS THAT IS NOT THE GENUS FORMULA, AND THAT THE CUT DID
NOT INHERIT AN AUDIT FOR** (opened 2026-07-30; its second bullet is since
the same day a REFUTATION rather than a question, and `hchar` is the
repair — see the FALSITY AUDIT below).  The audits above range over the
arithmetic parameters `hN`, `hg` and over what `hmodel` supplies; none of
them looks at WHICH `K` and WHICH `k` are allowed, and both are arbitrary.
Two obligations hide there, and the heading "Diamond–Shurman Thm 3.1.1 and
NOTHING ELSE" is true only after they are discharged.

* **`hmodel` is a statement over `S`; the conclusion is about the FIBRE.**
  `coarse` says `strY : Y ⟶ S` is COARSE — initial among `S`-schemes
  receiving a natural transformation from `[Γ₁(N)]` — and coarse moduli
  spaces are NOT stable under base change in general.  So "the fibre `X_K`
  is the `X_1(N)` of `K`", which is what ties `x1Genus N` to the geometry,
  is an extra step.  The rescue is real but is not a hypothesis: `[Γ₁(N)]`
  is RIGID for `N ≥ 4`, hence FINE, hence stable — and
  `IsCoarseModuliY1`'s own docstring records that fineness as something it
  deliberately does not carry as a field.  `hN : 5 ≤ N` is in scope, so
  this is dischargeable; it is simply not free.
* **Nothing makes `N` invertible on `S`, and `K` may have characteristic
  `p ∣ N`.**  `PointOfExactOrder ab N` is the NAIVE level structure — a
  section of exact order `N` — and that problem is represented by the
  classical `X_1(N)` only where `N` is invertible.  In characteristic
  `p ∣ N` an ordinary `E/K̄` has `E[p^a](K̄) ≅ ℤ/p^a`, so the problem is
  NONEMPTY and its coarse space is an Igusa-type curve, not
  `X_1(N) ⊗ 𝔽_p` — Katz–Mazur replace the naive structure by a Drinfeld
  one precisely here.  Its genus is not `x1Genus N`, so in that
  characteristic the leaf is not the genus formula at all.  **That second
  bullet is now a refutation**, and `hchar : (N : K) ≠ 0` is the repair.

**FALSITY AUDIT (2026-07-30, SECOND RESTATEMENT OF THIS LEAF).  Without
`hchar` THE STATEMENT IS FALSE, and the witness is the IGUSA CURVE
`Ig(11)` in characteristic `11`.**  The version cut earlier the same day
carried no characteristic hypothesis and recorded the bullet above as an
OPEN question with no witness claimed.  A witness exists, it is small, and
it is explicit.  Per this project's rule that a second restatement VOIDS
the earlier audits rather than inheriting them, the two bullets above have
been re-checked against the composite statement and stand; what follows is
the new audit that the composite requires.

  `N = 11`,  `S = Spec 𝔽̄₁₁`,  `K = 𝔽̄₁₁`,  `k = 𝟙`,  `X = Ig(11) ≅ ℙ¹`.

`5 ≤ 11` gives `hN`, and `x1Genus 11 = 1` gives `hg` (`decide`-checked
with the rest of the table above); `𝔽̄₁₁` is algebraically closed.  What
goes wrong is `hmodel`'s tie to the classical curve:

* `PointOfExactOrder ab 11` asks only for a section whose additive order
  on every GEOMETRIC fibre is `11`.  In characteristic `11` an ORDINARY
  `E` has `E[11](K̄) ≅ ℤ/11`, so such sections exist — ten of them, five
  up to `±1` — while a SUPERSINGULAR `E` has `E[11]` infinitesimal and has
  none.  So `[Γ₁(11)]` over `𝔽̄₁₁` is NOT empty (the cheap rescue fails)
  but lives over the ORDINARY locus; being rigid (`11 ≥ 4`) it is
  representable, its moduli scheme is the open IGUSA CURVE `Ig(11)°`, and
  that is the `Y` of the witness.  Initiality — all `IsCoarseModuliY1`
  asks for — is Yoneda for a representable functor.
* `Ig(11)° → 𝔸¹_j` is finite étale of degree `(11 − 1)/2 = 5`, Galois with
  group `(ℤ/11)ˣ/±1 ≅ ℤ/5`, over the ordinary locus `ℙ¹_j ∖ {0, 1, ∞}`.
  In characteristic `11` the supersingular `j` are exactly `0` and
  `1728 = 1`, which is what makes this prime the clean case: the two
  `X(1)` orbifold points are supersingular, so they contribute no EXTRA
  ramification.  Take `X := Ig(11)`, the smooth compactification; then
  `isProper`, `smooth`, `connected` (Igusa's irreducibility theorem) and
  `finite_compl` (the complement of `Y` is the two supersingular points
  and the five cusps) all hold.

**`Ig(11)` HAS GENUS `0`**, and that is the whole refutation: `X_K = X` is
`ℙ¹_{𝔽̄₁₁}`, which IS birational to `𝔸¹` over `𝔽̄₁₁`, so the conclusion
fails with every hypothesis satisfied.  The genus is computed two
independent ways, which agree here and at three further primes:

* **Riemann–Hurwitz on `Ig(p) → ℙ¹_j`.**  Degree `d = (p−1)/2`, tame
  (`gcd(d, p) = 1`), totally ramified over each supersingular `j`,
  ramified with `e = 3` over an ORDINARY `j = 0` and `e = 2` over an
  ORDINARY `j = 1728`, and UNRAMIFIED over `j = ∞` (`Ig(p)` has `(p−1)/2`
  cusps).  At `p = 11` both orbifold points are supersingular, so
  `2g − 2 = 5·(−2) + 4 + 4 + 0 = −2` and `g = 0`.
* **The Katz–Mazur / Deligne–Rapoport special fibre.**  `X_1(p)_{𝔽_p}` is
  two copies of `Ig(p)` crossing transversally at the supersingular
  points, so `g(X_1(p)) = 2·g(Ig(p)) + #ss − 1`.  At `p = 11`,
  `g(X_1(11)) = 1` and `#ss = 2`, giving `g(Ig(11)) = 0` again.  The `Γ₀`
  form of the same identity — `g(X_0(p)) = #ss − 1`, the two components
  there being `ℙ¹` — is the control, and it is correct at
  `p = 11, 13, 17, 19` (`g = 1, 0, 1, 1` against `#ss = 2, 1, 2, 2`).

The two methods also agree at `p = 13, 17, 19`, where they give
`g(Ig(p)) = 1, 2, 3` against `g(X_1(p)) = 2, 5, 7`.  That is what makes
`p = 11` a computed value rather than a guess: **`11` is the only prime at
which the level-`p` Igusa curve is rational while `x1Genus p ≥ 1`.**  (At
`p = 5, 7` it is rational too, but `x1Genus 5 = x1Genus 7 = 0` kills `hg`.)

**WHY `(N : K) ≠ 0` IS THE MINIMAL REPAIR.**  It says exactly
`char K ∤ N`, which is Katz–Mazur's own validity condition: where `N` is
invertible the naive `PointOfExactOrder` structure IS the classical level
structure, `[Γ₁(N)]` is finite étale over the whole `j`-line, and its
coarse space really is `Y_1(N)_K` with genus `x1Genus N`.  In
characteristic `p ∣ N` it is the DRINFELD structure that represents
`X_1(N)`, and the naive problem represents an Igusa-type curve of a
different genus.  So `hchar` removes nothing on which the statement was
ever true, and the first bullet above (coarse-vs-fibre) is unchanged by it
and still dischargeable from `hN : 5 ≤ N` through rigidity.

**IT COSTS THE CONSUMERS NOTHING**, which is why the repair is carried
through here rather than left to a successor.  `hchar` threads verbatim
through `exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` and
`not_birationalOver_affineLine_of_one_le_x1Genus` below — a field
extension `K → L` is injective, so `(N : K) ≠ 0` gives `(N : L) ≠ 0` and
the algebraically closed `L` the geometric leaf quantifies over is covered
— becomes the base-level `∀ K, (Spec K ⟶ S) → (N : K) ≠ 0` on
`hasNoFibreAffineLine_of_one_le_x1Genus`, and is DISCHARGED at that
theorem's single consumer `hasNonconstantAbelianMap_of_one_le_x1Genus`,
whose base is `SpecQ`: a `ℚ`-point gives a ring map `ℚ →+* K`
(`nonempty_ringHom_of_hom_specQ`), hence `CharZero K`, hence `(N : K) ≠ 0`
from `5 ≤ N`.  Nothing above that line changes, and `N = 25` over `ℚ` —
the only level this file is built for — never meets the hypothesis.

**THE THREE THEOREMS BELOW WERE FALSE TOO, and the same hypothesis repairs
them.**  All three are marked PROVEN over this leaf, and a proof over a
false leaf establishes nothing: the same witness refutes
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` (`ℙ¹` receives only
constant maps to abelian varieties), and
`not_birationalOver_affineLine_of_one_le_x1Genus` together with
`hasNoFibreAffineLine_of_one_le_x1Genus` (`𝔸¹ ⊂ ℙ¹` is a nonconstant
fibre line).  The LEVEL-FREE geometric leaf
`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` is NOT
affected: its `hgeom` FAILS at the witness, `ℙ¹` being birational to `𝔸¹`,
so no hypothesis of it is added. -/
theorem not_birationalOver_affineLine_of_one_le_x1Genus_algClosed {N : ℕ} (hN : 5 ≤ N)
    (hg : 1 ≤ x1Genus N) {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} {jY : Y ⟶ X}
    (hmodel : IsX1Compactification N strX strY jY)
    (K : Type) [Field K] [IsAlgClosed K] (k : Spec (CommRingCat.of K) ⟶ S)
    (hchar : (N : K) ≠ 0) :
    ¬ Scheme.BirationalOver (curveBaseChangeProj strX k)
        (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
  sorry

/-- **`Pic⁰` AND THE DEGREE-`n` ABEL–JACOBI MAP: a GEOMETRICALLY
non-rational fibre receives a nonconstant map to an abelian variety**
(sorry leaf, cut 2026-07-30) — the geometric half of
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` below.

**LEVEL-FREE: no `N`, no `Gamma1Datum`, no modular curve.**  It is stated
about a bare proper smooth geometrically connected relative curve, which
is exactly the data `IsX1Compactification` supplies through `isProper`,
`smooth` and `connected`.

TRUE.  `hgeom` says the geometric fibre is not rational, i.e. the fibre has
genus `≥ 1`, so `J = Pic⁰(X_K/K)` is an abelian variety over `K` of
dimension `≥ 1`.  Any closed point of `X_K` has some finite residue degree
`n ≥ 1` and so gives a `K`-rational divisor `D` of degree `n`; then
`x ↦ n[x] − D` is a `K`-morphism `X_K ⟶ J` needing NO rational point.  It
is nonconstant because over `K̄` the Abel–Jacobi map is a closed immersion
(genus `≥ 1`) and `[n]` is an isogeny, so the composite is finite onto its
image; a morphism that is nonconstant after base change is nonconstant.

**THE HYPOTHESIS MUST BE GEOMETRIC — FALSITY AUDIT OF THE OBVIOUS CUT.**
The tempting form of this leaf takes `¬ BirationalOver` over `K` ITSELF,
which is what `not_birationalOver_affineLine_of_one_le_x1Genus` below
literally says, three declarations away and in the same shape.  **With
that hypothesis the leaf is FALSE**, and the counterexample is small and
completely explicit:

  `K = ℝ`, `C ⊆ ℙ²_ℝ` the pointless conic `x² + y² + z² = 0`.

`C` is smooth, proper and geometrically connected (`C_ℂ ≅ ℙ¹_ℂ`), and it
is NOT birational to `𝔸¹_ℝ` over `ℝ`: a birational map over `ℝ` would
carry a dense open of `𝔸¹_ℝ` — which has infinitely many `ℝ`-points —
isomorphically onto a dense open of `C`, while `C(ℝ) = ∅`.  So the
`K`-form's hypothesis HOLDS.  Its conclusion FAILS: for any abelian
variety `A/ℝ` and any `c : C ⟶ A` over `ℝ`, the base change `c_ℂ` is a
morphism `ℙ¹_ℂ ⟶ A_ℂ`, hence constant at some `a ∈ A(ℂ)`; `a` is then
`Gal(ℂ/ℝ)`-fixed because `c` is defined over `ℝ`, so `a ∈ A(ℝ)` and `c`
factors as `C ⟶ Spec ℝ ⟶ A`.  That is exactly `c = proj ≫ s`, the
negation of the nonconstancy clause.

The gap the witness exploits is that over a non-closed field
"non-rational" mixes genus with the arithmetic of rational points, and
only the genus part is what `Pic⁰` sees.  Quantifying `hgeom` over
algebraically closed extensions removes the arithmetic part and nothing
else.  (`∀ L` and `∃ L` are classically the same hypothesis here — genus
does not change under extension of an algebraically closed field — and
`∀` is the form the consumer can supply, since the arithmetic leaf above
is stated at an arbitrary algebraically closed `K`.)

**`hgeom` IS LOAD-BEARING**: drop it and `ℙ¹_K` refutes the leaf outright
— smooth, proper, geometrically connected, and every morphism from it to
an abelian variety is constant.  `hproper`, `hsmooth` and `hconn` are the
standing curve conditions the `Pic⁰` construction needs; they are supplied
free by `hmodel` and no separate falsity witness is claimed for them.

**WHAT IS IN TREE, AND WHY IT IS NOT ENOUGH.**  `RelativePicard.lean`'s
`exists_relPicZero` (PROVEN, over `exists_relPicFull` and
`exists_relPicZero_of_isRelPicOf`) builds precisely `Pic⁰` as an abelian
scheme with an Abel–Jacobi map, with the same three curve hypotheses — but
it also demands a SECTION `o : RelPoint strX (𝟙 S)`, and no section is
available here: `k` is an arbitrary `K`-point of an arbitrary base and
nothing in `IsX1Compactification` carries one.  (`X_1(N)` does have
rational cusps, but only where `N` is invertible, which is not a
hypothesis.)  That gap IS the degree-`n` trick, and closing this leaf means
either extending that development to the base-point-free case or producing
the section some other way.

**THERE IS A SECOND GAP, AND IT IS NOT THE SECTION** (2026-07-30).  The
paragraph above names the missing base point and stops, which reads as
"one extension of `RelativePicard.lean` and this closes".  It does not:
the nonconstancy clause needs `Pic⁰` to have POSITIVE DIMENSION, and the
only thing offered for that is `hgeom`.  Getting from `hgeom` to it is the
implication

> over an algebraically closed field, a smooth proper connected curve with
> `Pic⁰ = 0` is birational to `𝔸¹`,

which is Riemann–Roch content and is absent at this pin by exactly the
audit that `exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` below
records under "THE AXIS THIS DECOMPOSITION IS NOT" — "a genus of a scheme,
`h¹(𝒪_X)`, Riemann–Hurwitz — none of those exists at this pin".  That
verdict was made about the ARITHMETIC half and applies here verbatim.  So
this leaf is blocked on TWO theories, not one,
and a cut that only splits off the base-point-free `Pic⁰` is a
RESTATEMENT: the residue would be this same implication with a `Pic⁰` in
front of it.  Note the phrasing above is deliberately `Pic⁰`-only — no
genus NUMBER is needed, which is why the two halves are separable in
principle even though neither is available.

**THE DEGENERATE REFUTATION DOES NOT RUN, so do not spend a cycle on it**
(checked 2026-07-30 by reading
`Mathlib/AlgebraicGeometry/Geometrically/Connected.lean`).  The tempting
cheap witness is `X_K = ∅`: `hgeom` would hold (`∅` is not birational to
`𝔸¹`) while the conclusion would FAIL, because there is exactly one
morphism out of the initial object and so `c = proj ≫ s` is forced.  It is
blocked at the hypothesis: mathlib's `GeometricallyConnected f` is
`geometrically (ConnectedSpace ·) f`, `ConnectedSpace` extends `Nonempty`,
and mathlib derives `[GeometricallyConnected f] : Surjective f` as a
low-priority instance — so `hconn` makes every fibre, `X_K` included,
nonempty and connected.  `hconn` is therefore load-bearing for a second
reason beyond the `Pic⁰` construction, and the same check disposes of the
`S = ∅` variant, where no `k : Spec K ⟶ S` exists at all and the statement
is vacuous rather than false.

**RELOCATION NOTE.**  Nothing here is `Γ₁`-specific, and the `Γ₀` sibling
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus` in `X0.lean` is an
open leaf of exactly the same shape which would close over this leaf plus
its own algebraically-closed arithmetic leaf, word for word.  It is stated
in `X1.lean` only because `X1.lean` imports `X0.lean` and not conversely;
moving it down to `X0.lean` is a pure relocation with no mathematical
content, and is what a `Γ₀` owner should do rather than restate it. -/
theorem exists_nonconstant_toAbelianScheme_of_notGeometricallyRational
    {X S : Scheme.{0}} {strX : X ⟶ S} (hproper : IsProper strX)
    (hsmooth : SmoothOfRelativeDimension 1 strX) (hconn : GeometricallyConnected strX)
    (K : Type) [Field K] (k : Spec (CommRingCat.of K) ⟶ S)
    (hgeom : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosed L],
      ¬ Scheme.BirationalOver
          (curveBaseChangeProj strX (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ k))
          (𝔸(Unit; Spec (CommRingCat.of L)) ↘ Spec (CommRingCat.of L))) :
    ∃ (A : Scheme.{0}) (astr : A ⟶ Spec (CommRingCat.of K))
      (_ : AbelianSchemeStruct astr) (c : curveBaseChange strX k ⟶ A),
      c ≫ astr = curveBaseChangeProj strX k ∧
        ∀ s : Spec (CommRingCat.of K) ⟶ A, c ≠ curveBaseChangeProj strX k ≫ s :=
  sorry

/-- **EICHLER–SHIMURA, FIBREWISE, AT `Γ₁`: `genus X_1(N) ≥ 1` gives EVERY
fibre of `X_1(N)` a nonconstant map to an abelian variety** (**PROVEN
2026-07-30 by decomposition**; a sorry leaf from 2026-07-28) — the
arithmetic half of `not_birationalOver_affineLine_of_one_le_x1Genus`
below, and the exact transposition of `X0.lean`'s
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus`, which is still
open and can close the same way.

**THE CUT, and what it buys.**  The leaf bundled two theories that have
nothing to do with each other: the genus of `X_1(N)` (Diamond–Shurman
3.1.1, arithmetic, mentions `N`) and the construction of `Pic⁰` with its
degree-`n` Abel–Jacobi map (geometry, level-free).  A prover of the bundle
owed both.  Separated, they are the two leaves above:

* `not_birationalOver_affineLine_of_one_le_x1Genus_algClosed` — the genus
  formula over an ALGEBRAICALLY CLOSED field and nothing else;
* `exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` — the
  `Pic⁰` construction, with no `N` in it, SHARED in principle with the
  `Γ₀` layer (see its RELOCATION NOTE).

The frontier goes from one leaf to two, which is what decomposition costs;
what it buys is that neither piece carries the other's theory, and one of
them is reusable by `X0.lean`.

**THE AXIS THIS DECOMPOSITION IS NOT.**  The earlier audit of the bundled
leaf recorded the identification of the arithmetic `x1Genus N` with an
invariant of the SCHEME `X` — a genus of a scheme, `h¹(𝒪_X)`,
Riemann–Hurwitz — as exhausted, and that verdict stands: none of those
exists at this pin and none is introduced here.  The genus stays sealed
inside the arithmetic leaf, where it is a citation rather than a
construction.  What was missed is that the leaf ALSO owed a `Pic⁰`, and
that half is separable without any genus notion at all.

**WHY THE GEOMETRIC HALF NEEDS AN ALGEBRAICALLY CLOSED BASE.**  Because
the same cut with the arbitrary-field hypothesis is FALSE — the pointless
conic over `ℝ` refutes it.  The audit is on
`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational`; it is
the one thing to read before "simplifying" this assembly, because
`not_birationalOver_affineLine_of_one_le_x1Genus` below has precisely the
shape the false version would want and sits three declarations away.

**WHY THIS IS NOT A DUPLICATE OF THE `Γ₀` LEAF**, which is the question to
ask of any `Γ₁` transposition.  The natural degree-`φ(N)/2` map
`X_1(N) ↠ X_0(N)` would deduce this from
`exists_nonconstant_toAbelianScheme_of_one_le_x0Genus` by composition —
but `x0Genus 25 = 0`, and `25` is the level `MazurTorsion.lean` needs, so
the `Γ₀` hypothesis is unavailable exactly where it would be used.  The
two are genuinely independent, and the sharing that IS available is of the
geometric half only.

**BOTH ARITHMETIC HYPOTHESES ARE LOAD-BEARING and each makes the
statement FALSE if dropped.**

* `hg` — at genus `0` the conclusion is FALSE outright.  `X_1(5)` is the
  witness INSIDE the validity range (`x1Genus 5 = 0`, and `5 ≤ 5`): it is
  `ℙ¹`, and every morphism from `ℙ¹` to an abelian variety is constant, so
  no such `c` exists at any `K`.
* `hN : 5 ≤ N` — at `N = 1` and at `N = 0` alike the definition evaluates
  to `1`, so `hg` is satisfiable while the curve has genus `0`.  Both
  values are `decide`-checked; see the arithmetic leaf's audit, which
  carries the full list.  **This is the guard the `Γ₀` sibling lacks**,
  and it is why that layer needs the extra leaf
  `pos_of_isX0Compactification_of_fieldPoint` while this one does not.
* `hmodel` is load-bearing twice over — it supplies the curve conditions
  AND it is the only thing tying the arithmetic `x1Genus N` to the
  geometry of `strX`.  `N` enters only through `hg`, `hN` and `hmodel`.

**NOT VACUOUS, and the junk witness is killed by the nonconstancy clause
alone**: `A = Spec K` with `astr = 𝟙` forces `c = curveBaseChangeProj
strX k`, which is `curveBaseChangeProj strX k ≫ 𝟙`, so the final clause
fails at `s = 𝟙`.  A prover must therefore produce a genuinely
positive-dimensional `A`.

**`hchar : (N : K) ≠ 0` ADDED 2026-07-30, AND IT IS LOAD-BEARING: without
it this statement is FALSE**, refuted by the same `Ig(11)` witness that
refutes the arithmetic leaf above — `N = 11` over `𝔽̄₁₁` makes the fibre
`ℙ¹`, and every morphism from `ℙ¹` to an abelian variety is constant, so
no such `c` exists.  See that leaf's FALSITY AUDIT; this theorem was
marked PROVEN over it, and a proof over a false leaf establishes nothing.
The hypothesis is CONSUMED rather than merely carried: the geometric leaf
quantifies over algebraically closed extensions `L/K`, and `hchar` is
transported to each by injectivity of `algebraMap K L`. -/
theorem exists_nonconstant_toAbelianScheme_of_one_le_x1Genus {N : ℕ} (hN : 5 ≤ N)
    (hg : 1 ≤ x1Genus N) {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} {jY : Y ⟶ X}
    (hmodel : IsX1Compactification N strX strY jY)
    (K : Type) [Field K] (k : Spec (CommRingCat.of K) ⟶ S) (hchar : (N : K) ≠ 0) :
    ∃ (A : Scheme.{0}) (astr : A ⟶ Spec (CommRingCat.of K))
      (_ : AbelianSchemeStruct astr) (c : curveBaseChange strX k ⟶ A),
      c ≫ astr = curveBaseChangeProj strX k ∧
        ∀ s : Spec (CommRingCat.of K) ⟶ A, c ≠ curveBaseChangeProj strX k ≫ s :=
  exists_nonconstant_toAbelianScheme_of_notGeometricallyRational
    hmodel.isProper hmodel.smooth hmodel.connected K k
    fun L _ _ _ => not_birationalOver_affineLine_of_one_le_x1Genus_algClosed hN hg hmodel L _
      fun hL => hchar ((algebraMap K L).injective (by simpa using hL))

/-- **The genus formula at `Γ₁`: no fibre of `X_1(N)` is a RATIONAL curve
when `genus X_1(N) ≥ 1`** (PROVEN 2026-07-28 over the leaf above together
with `X0.lean`'s level-free
`eq_comp_of_birationalOver_affineLine_toAbelianScheme`) — the arithmetic
half of `hasNoFibreAffineLine_of_one_le_x1Genus` below, and the `Γ₁`
transposition of `not_birationalOver_affineLine_of_one_le_x0Genus`.

TRUE: genus is a birational invariant of a smooth proper curve and `𝔸¹_K`
has genus `0`, so a fibre of genus `≥ 1` is not birational to `𝔸¹_K` over
`K`.  What replaces the (unavailable) genus in the proof is the birational
invariant a MAP provides: *does the curve admit a nonconstant morphism to
an abelian variety?*  Rational curves do not, positive-genus curves do,
and both halves are statable at this pin — the first is `X0.lean`'s
level-free `eq_comp_of_birationalOver_affineLine_toAbelianScheme` (proven
there over the single geometric leaf
`exists_section_of_denseOpen_affineLine_toAbelianScheme`), the second is
the leaf immediately above.  No genus of a scheme, no `h¹`, no `ℙ¹` and no
Riemann–Hurwitz enters.

**WHY THE FIBRE AND NOT `X` ITSELF.**  `BirationalOver strX (…)` over the
base `S` would be FALSE for a reason having nothing to do with the genus:
over `S = Spec ℤ` the arithmetic surface `X` and the curve `𝔸¹_{𝔽_p}` have
different dimensions, so no partial isomorphism exists whatever `N` is.
Rationality is a property of the FIBRE, which is why the base change is
taken here rather than left to the consumer.

**`hg` AND `hN` ARE LOAD-BEARING**, and both make the statement FALSE if
dropped: at `N = 1`, `x1Genus 1 = 1` satisfies `hg` while `X_1(1) = ℙ¹`
contains `𝔸¹` as a dense open, so the fibre IS birational to `𝔸¹_K` at
every `K`; at `N = 5` (inside the validity range) `x1Genus 5 = 0` and the
same witness applies.  `hmodel` is load-bearing twice over, exactly as on
the leaf above.

**NOT VACUOUS**: `Scheme.BirationalOver _ (𝔸(Unit; Spec K) ↘ _)` is
satisfiable — it holds for `𝔸¹_K` itself by `BirationalOver.refl`, and for
any smooth proper rational curve since a dense open is birational to the
whole (`Opens.birationalOver_of_dense`).  So the conclusion is a real
constraint and this leaf really consumes the genus.

**`hchar : (N : K) ≠ 0` ADDED 2026-07-30, AND IT IS LOAD-BEARING**: the
`Ig(11)` witness of the arithmetic leaf above refutes this statement too
(`N = 11` over `𝔽̄₁₁` gives the fibre `ℙ¹`, which contains `𝔸¹` as a dense
open and so IS birational to it), exactly as `hN` and `hg` do at their own
degenerate levels.  It is passed straight down to
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus`. -/
theorem not_birationalOver_affineLine_of_one_le_x1Genus {N : ℕ} (hN : 5 ≤ N)
    (hg : 1 ≤ x1Genus N) {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} {jY : Y ⟶ X}
    (hmodel : IsX1Compactification N strX strY jY)
    (K : Type) [Field K] (k : Spec (CommRingCat.of K) ⟶ S) (hchar : (N : K) ≠ 0) :
    ¬ Scheme.BirationalOver (curveBaseChangeProj strX k)
        (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  intro hrat
  haveI : SmoothOfRelativeDimension 1 strX := hmodel.smooth
  haveI hsm : SmoothOfRelativeDimension 1 (curveBaseChangeProj strX k) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension 1 strX›
  obtain ⟨A, astr, abA, c, hc, hnc⟩ :=
    exists_nonconstant_toAbelianScheme_of_one_le_x1Genus hN hg hmodel K k hchar
  obtain ⟨s, hs⟩ := eq_comp_of_birationalOver_affineLine_toAbelianScheme hsm abA hrat c hc
  exact hnc s hs

/-- **The genus formula, fibrewise, at `Γ₁`: `genus X_1(N) ≥ 1` puts no
rational curve in any fibre of `X_1(N)`** (PROVEN 2026-07-28 by
decomposition; formerly a sorry leaf audited as IRREDUCIBLE) — the
`Γ₁` transposition of `X0.lean`'s `hasNoFibreAffineLine_of_one_le_x0Genus`.
It is NO LONGER "the ONLY place where the computed number `x1Genus N` meets
the scheme `X`": after the cuts above that role belongs to
`not_birationalOver_affineLine_of_one_le_x1Genus_algClosed`, which is
since 2026-07-30 the single ARITHMETIC leaf of the whole `Γ₁` genus
formula — the one other residual leaf,
`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational`, is
level-free and mentions no `N`.

`HasNoFibreAffineLine` itself is `X0.lean`'s, REUSED VERBATIM — it is
level-free, and the whole point of the seam is that only the arithmetic
leaf, which mentions `N`, differs between the two layers.

TRUE.  `hmodel` makes every fibre of `strX` a smooth proper
geometrically connected curve which is the `X_1(N)` of its residue
field, and `hg` together with `hN` says its genus is `≥ 1` (the classical
formula, Diamond–Shurman Thm 3.1.1).  A nonconstant `K`-morphism
`𝔸¹_K ⟶ X` over a `K`-point of `S` lands in one such fibre `X_K` and
makes it a RATIONAL curve — birational to `𝔸¹_K` over `K`, by Lüroth —
while a curve of genus `≥ 1` is not rational, contradicting `hg`.  Hence
every such morphism is constant, which is `HasNoFibreAffineLine`.

**BOTH ARITHMETIC HYPOTHESES ARE LOAD-BEARING, AND `hN` IS WHAT THE `Γ₀`
SIBLING LACKS.**  See the VALIDITY RANGE note on `x1Genus`: the classical
formula is the genus of `X_1(N)` only for `N ≥ 5`, and outside that range
it evaluates WRONG in the dangerous direction — `x1Genus 0 = x1Genus 1 = 1`
while `X_1(1) = ℙ¹` has genus `0`.  So without `hN` this statement is
FALSE at `N = 1`: `hg` is satisfied, yet `𝔸¹ ⊂ ℙ¹ = X_1(1)` is a
nonconstant witness over every base.  `hg` is load-bearing for the same
reason inside the range, `X_1(5)` (genus `0`, and `5 ≤ 5`) being the
witness.  `hmodel` is load-bearing twice over — it supplies the curve
conditions AND it is the only thing tying the arithmetic `x1Genus N` to
the geometry of `strX`.  `N` enters only through those.

**The degenerate-level exposure that `X0.lean` carries does NOT arise
here.**  `hasNoFibreAffineLine_of_one_le_x0Genus` has no `hN`, and
`x0Genus 0 = 1`, so its prover must confront `N = 0` separately.  This
leaf inherits `hN : 5 ≤ N` from the node it was cut out of, so `N = 0`
and `N = 1` are excluded by hypothesis and no `isEmpty_of_isCoarseModuliY1`
argument is needed.

**NOT VACUOUS, and this is worth checking because the conclusion is a
negative statement.**  `HasNoFibreAffineLine` is refutable: it fails for
`X = 𝔸¹_ℚ ⊂ ℙ¹_ℚ` over `Spec ℚ` — take `K = ℚ`, `k = 𝟙`, `u` the open
immersion, which factors through no `ℚ`-point since its image is
`1`-dimensional.  So the predicate really constrains the curve, and this
leaf really consumes the genus.

**The `Γ₀` leaf does NOT imply this one**, for the reason this whole
module exists: the natural degree-`φ(N)/2` map `X_1(N) ↠ X_0(N)` would
give it by composition from `1 ≤ x0Genus N`, but `x0Genus 25 = 0`.  The
two fibrewise genus formulas are genuinely independent leaves at the level
this development needs.

**THE OLD IRREDUCIBILITY VERDICT IS WITHDRAWN, AND ITS OWN REFUTING CHECK
WAS THE WRONG CHECK.**  The previous docstring recorded this leaf as
IRREDUCIBLE "at this pin along the axis searched — the identification of
the arithmetic `x1Genus N` with an invariant of the scheme `X`, which
needs a genus of a scheme, `h¹(𝒪_X)`, or Riemann–Hurwitz", and nominated
as the check that would refute it: *does a genus, an `h¹` or a
Riemann–Hurwitz statement appear in `Fermat/`, `Mathlib` or `~/cs/FLT`?*
That axis really is exhausted and that grep really does come back empty —
and the verdict was still wrong, because **the `Γ₀` sibling
`hasNoFibreAffineLine_of_one_le_x0Genus` was PROVEN along a third axis the
verdict never considered**, using none of those three things.  A verdict
is only as wide as the axis its author searched; the check that refutes
one here is *"has the sibling leaf at the other level been closed, and
along what axis?"*, not a grep for the machinery the exhausted axis wanted.

**THE AXIS THAT CUTS: rationality of the fibre, via Lüroth.**  For a
smooth curve, "the fibre carries a nonconstant affine line" is "the fibre
is BIRATIONAL to `𝔸¹_K` over `K`" — a statement about `𝔸¹` alone, so no
`ℙ¹` is ever built — and the implication that way is **Lüroth**, which
`Mathlib` already proves.  Every level-free piece is `X0.lean`'s and is
reused here VERBATIM, with no edit to that file:

* `isDominant_of_not_exists_section` — nonconstant ⟹ dominant (PROVEN);
* `birationalOver_affineLine_of_isDominant` — Lüroth (PROVEN).  The two
  are packaged as `birationalOver_affineLine_of_not_exists_section`, which
  is what the assembly below calls;
* `not_birationalOver_affineLine_of_one_le_x1Genus` — the arithmetic half,
  cut immediately above, and the only piece that mentions `N`.

`exists_unique_extension_of_isSmoothProperCurve` — which the old docstring
flagged as "already proven, do not rebuild it", for the `𝔸¹_K ⟶ ℙ¹_K`
extension the Riemann–Hurwitz route wanted — is therefore **not used**.
That note was correct about the lemma and pointed at a route this file no
longer takes.

**THE `Γ₁` COST OF THE GENUS FORMULA IS ONE ARITHMETIC LEAF**,
`not_birationalOver_affineLine_of_one_le_x1Genus_algClosed` (2026-07-30;
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` held that place
until then and is now PROVEN over it and one LEVEL-FREE geometric leaf).
That is ONE FEWER arithmetic leaf than the `Γ₀` layer needs: that assembly
must also carry `pos_of_isX0Compactification_of_fieldPoint` (`0 < N`, a
separate sorry leaf) because `x0Genus 0 = 1` and its fibrewise leaf has no
arithmetic guard, whereas `hN : 5 ≤ N` is a hypothesis here.

**Do NOT decompose the residual leaf along the MODULAR axis**
(`dim S_2(Γ_1(N)) = x1Genus N` plus Eichler–Shimura).  That was tried on
the `Γ₀` side and RETIRED: it is a second, parallel copy of the genus
formula with a theory build attached.  The cut taken here is the
BIRATIONAL axis and is a different thing — it names the abelian variety
nowhere and asks only that some nonconstant map to one exist.

**`hchar` ADDED 2026-07-30, AND IT IS LOAD-BEARING.**  `HasNoFibreAffineLine`
quantifies over the field points of `S` internally, so the characteristic
hypothesis that the three declarations above carry per-`K` becomes here a
condition on the BASE: no field point of `S` may have characteristic
dividing `N`.  Without it the statement is FALSE, by the `Ig(11)` witness
audited on `not_birationalOver_affineLine_of_one_le_x1Genus_algClosed`
(`N = 11`, `S = Spec 𝔽̄₁₁`, whose one field point has characteristic `11`
and whose fibre `ℙ¹` does contain a nonconstant affine line).  It is
DISCHARGED at the single consumer below, whose base is `SpecQ`. -/
theorem hasNoFibreAffineLine_of_one_le_x1Genus {N : ℕ} (hN : 5 ≤ N) (hg : 1 ≤ x1Genus N)
    {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} {jY : Y ⟶ X}
    (hmodel : IsX1Compactification N strX strY jY)
    (hchar : ∀ (K : Type) [Field K], (Spec (CommRingCat.of K) ⟶ S) → (N : K) ≠ 0) :
    HasNoFibreAffineLine strX := by
  intro K _ k u hu
  by_contra hcon'
  have hcon : ∀ s : Spec (CommRingCat.of K) ⟶ X,
      u ≠ (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) ≫ s :=
    fun s hs => hcon' ⟨s, hs⟩
  haveI : SmoothOfRelativeDimension 1 strX := hmodel.smooth
  haveI : GeometricallyConnected strX := hmodel.connected
  haveI hsm : SmoothOfRelativeDimension 1 (curveBaseChangeProj strX k) := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension 1 strX›
  refine not_birationalOver_affineLine_of_one_le_x1Genus hN hg hmodel K k (hchar K k) ?_
  refine birationalOver_affineLine_of_not_exists_section hsm inferInstance
    (CategoryTheory.Limits.pullback.lift u
      (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) hu) ?_ ?_
  · exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  · intro s hs
    refine hcon (s ≫ CategoryTheory.Limits.pullback.fst strX k) ?_
    have h2 := congrArg (fun t => t ≫ CategoryTheory.Limits.pullback.fst strX k) hs
    simp only [CategoryTheory.Limits.pullback.lift_fst, Category.assoc] at h2
    exact h2

/-- **The genus formula, in its geometric form: `genus X_1(N) ≥ 1` gives
`X_1(N)` a nonconstant map to an abelian variety** (PROVEN 2026-07-28,
over `hasNoFibreAffineLine_of_one_le_x1Genus` and three level-free
theorems of `X0.lean`; formerly a bare sorry node audited as irreducible)
— the arithmetic-to-geometry bridge.  It is NO LONGER "the only place
where the computed number `x1Genus N` meets the scheme `X`": that role
has passed to `hasNoFibreAffineLine_of_one_le_x1Genus` above, which is
where the genus formula is now consumed exactly once.

TRUE: `x1Genus N` is the genus of `X` by the classical formula for
`N ≥ 5` (Diamond–Shurman, Theorem 3.1.1); a smooth proper geometrically
connected curve of genus `≥ 1` over `ℚ` with a rational point embeds in
its Jacobian by `x ↦ [x] − [o]`, which is a nonconstant pointed map to
an abelian variety.  Concretely at `N = 25` one may take `A` to be
either newform factor `A₄` or `A₈` of `J_1(25)` — `S_2(Γ_1(25)) ≠ 0` is
exactly `x1Genus 25 ≥ 1`, and its dimension `12` is the genus — and `c`
the composite of Abel–Jacobi with the quotient.

**This is the exact `Γ₁` transposition of `X0.lean`'s
`hasNonconstantAbelianMap_of_one_le_x0Genus`**, and it is stated in that
file's vocabulary rather than a parallel one: `HasNonconstantAbelianMap`
is reused VERBATIM, as are the two bridges
`subsingleton_relPoint_of_isIso` and
`exists_ne_aj_of_hasNonconstantAbelianMap` that carry it to
`not_isIso_jacobian_of_one_le_x1Genus` below.  Both bridges are proven
and level-free, so the whole `Γ₁` side of the genus formula is this one
leaf.

**The `Γ₀` leaf does NOT imply this one, and the failure is at exactly
the level this file exists for.**  There is a natural degree-`φ(N)/2`
map `X_1(N) ↠ X_0(N)`, so `1 ≤ x0Genus N` would give the conclusion by
composition — but `x0Genus 25 = 0` (`X_0(25)` is rational, which is the
whole reason `MazurTorsion.lean` cannot use the `Γ₀` layer at all).  So
the two genus formulas are genuinely independent leaves at this level,
not one leaf and a corollary.

EVERY HYPOTHESIS IS LOAD-BEARING, and two of them make the leaf FALSE if
dropped.

* `hN : 5 ≤ N` — see the VALIDITY RANGE note on `x1Genus`.  At `N = 1`
  the definition evaluates to `x1Genus 1 = 1`, so `hg` is satisfiable,
  while `X_1(1) = ℙ¹` has genus `0` and receives only constant maps to
  abelian varieties.  So the statement is FALSE without `hN`, and this
  is not a hypothetical: the `decide`-computable definition really does
  return `1` there.
* `hg` — at genus `0` the conclusion is FALSE outright, `X_1(5)` (genus
  `0`, and `5 ≤ 5`) being a witness inside the validity range.  This is
  also what makes `one_le_x1Genus_twentyFive` consumed rather than
  floating.
* `h` — `N` enters the conclusion only through `hg` and `h`; without `h`
  the curve is unrelated to `x1Genus N`.

**STRENGTH AUDIT (2026-07-27), recorded because this leaf replaced a
`jac`-carrying one and a successor should know what moved.**  The
previous statement was `¬ IsIso jstr` given `jac : IsJacobianOf strX ab
o`.  This one drops `jac`, `J`, `jstr` and `ab` entirely, and the two
are equivalent GIVEN that a Jacobian exists — which is
`exists_jacobianOf_curve`, PROVEN above, so no new obligation is
created; the proof below now uses it in exactly that way, taking `A := J`
and `c := jac.aj`.  The two directions are exactly those recorded in
the `Γ₀` sibling's own strength audit; the forward one is the proof of
`not_isIso_jacobian_of_one_le_x1Genus` immediately below.  Dropping
`jac` is a deliberate improvement: the leaf is now a statement about the
curve `X_1(N)` ALONE, so it can be discharged without first constructing
`Pic⁰`.

**PROVEN 2026-07-28, AND NOT ALONG EITHER AXIS THIS DOCSTRING NAMED.**
The old note recorded the GEOMETRIC axis as exhausted (no genus of a
scheme, no `h¹`, no Riemann–Hurwitz at this pin) and recommended the
MODULAR one — build a newform factor `A_f` of `J_1(25)` and the modular
parametrisation `X_1(25) ↠ A_f` out of the `Modularity` subtree.  **That
recommendation is withdrawn**, and it is withdrawn on evidence rather than
taste: the `Γ₀` sibling's owner TOOK the modular axis, wrote the three
leaves it calls for (`0 < N`, the dimension formula
`dim S_2(Γ_0(N)) = genus`, and Eichler–Shimura), and then RETIRED all
three — the decomposition is a **second, parallel copy of the genus
formula** with a theory build attached to it.

The axis that cuts is the one where the arithmetic-to-geometry step has
already been paid, in its base-general FIBREWISE form.  `X0.lean`'s
`HasNoFibreAffineLine` — "no fibre of the curve contains a rational
curve" — is the genus formula stated fibrewise, and it is LEVEL-FREE, so
the `Γ₁` layer needs only the one arithmetic leaf
`hasNoFibreAffineLine_of_one_le_x1Genus` above and reuses everything
else:

* `exists_jacobianOf_curve` (PROVEN above, level-free and moduli-free)
  supplies `(J, aj)`, so the witness abelian scheme is the Jacobian
  itself and `c := jac.aj`; naturality is `aj_pre` and pointedness is
  `aj_base`, both free.
* `mono_ajHom_of_hasNoFibreAffineLine` (`X0.lean`, PROVEN, base-general)
  applied to `hasNoFibreAffineLine_of_one_le_x1Genus`, plus
  `IsJacobianOf.injective_aj_of_mono`, makes `aj g` INJECTIVE at every
  test object.  Nonconstancy then needs only two DISTINCT relative
  points.
* `not_isIso_of_smoothOfRelativeDimension_one` (PROVEN 2026-07-28, and
  RELOCATED to `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`,
  above the uniqueness lemma its proof consumes; elementary and level-free)
  gives those two: the tautological point
  `𝟙 X` and the constant point `strX ≫ o` are distinct unless `o`
  inverts `strX`, i.e. unless the curve is a single `ℚ`-point.

Only the FIRST of those three is new here, and it is a genuine leaf; the
other two are `X0.lean`'s, consumed with no edit to that file.  The
`Γ₁` cost of the genus formula is therefore ONE leaf, and it is the same
theory the `Γ₀` layer already needs — not a duplicate of it, because
`x0Genus 25 = 0` makes the two levels genuinely independent.

**WHERE `hN` GOES.**  It is consumed by
`hasNoFibreAffineLine_of_one_le_x1Genus`, which carries the falsity at
`N = 1` for exactly the reason recorded above; nothing else in the proof
looks at `N`.  This is a strict improvement on the `Γ₀` side, whose
fibrewise leaf has no such guard and whose prover must confront
`x0Genus 0 = 1` by hand.

**AND `hN` NOW DOES A SECOND JOB HERE: it discharges the characteristic
hypothesis** added to the four declarations above on 2026-07-30, and this
theorem is where that chain stops.  `strX : X ⟶ SpecQ` is the first base
in the chain that is pinned, and a `ℚ`-point forces `CharZero K`
(`nonempty_ringHom_of_hom_specQ`, then
`charZero_of_injective_algebraMap`), so `(N : K) ≠ 0` follows from
`5 ≤ N` alone.  The statement of this theorem is therefore UNCHANGED by
the repair, and so is everything above it — including
`isTorsion_jacobian_x1TwentyFive`, whose level `25` is invertible on `ℚ`
by inspection.  See the FALSITY AUDIT on
`not_birationalOver_affineLine_of_one_le_x1Genus_algClosed` for the
`Ig(11)` witness that made the repair necessary. -/
theorem hasNonconstantAbelianMap_of_one_le_x1Genus (N : ℕ) (hN : 5 ≤ N)
    (hg : 1 ≤ x1Genus N) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ}
    {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY)
    (o : RelPoint strX (𝟙 SpecQ)) :
    HasNonconstantAbelianMap strX o := by
  obtain ⟨J, jstr, ab, ⟨jac⟩⟩ :=
    exists_jacobianOf_curve h.isProper h.smooth h.connected o
  refine ⟨J, jstr, ab, fun T g => jac.aj g, ?_, jac.aj_base, ?_⟩
  · intro T' T hT g g' hcomm x
    exact jac.aj_pre hT hcomm x
  · -- the tautological point and the constant point at `o` are distinct,
    -- and `aj` is injective, so they have distinct images
    have hne : (⟨𝟙 X, Category.id_comp strX⟩ : RelPoint strX strX)
        ≠ ⟨strX ≫ o.1, by rw [Category.assoc, o.2, Category.comp_id]⟩ := by
      intro hEq
      refine not_isIso_of_smoothOfRelativeDimension_one h.smooth
        ⟨o.1.base (Nonempty.some inferInstance)⟩ ?_
      exact ⟨o.1, congrArg Subtype.val hEq.symm, o.2⟩
    -- the `SpecQ` base is what discharges the characteristic hypothesis:
    -- a `ℚ`-point gives a ring map `ℚ →+* K`, hence `CharZero K`
    have hchar : ∀ (K : Type) [Field K],
        (Spec (CommRingCat.of K) ⟶ SpecQ) → (N : K) ≠ 0 := by
      intro K _ k
      haveI : CharZero K := by
        obtain ⟨ψ⟩ := nonempty_ringHom_of_hom_specQ k
        letI : Algebra ℚ K := ψ.toAlgebra
        exact charZero_of_injective_algebraMap ψ.injective
      exact Nat.cast_ne_zero.mpr (by omega)
    exact ⟨X, strX, _, _, fun hc =>
      hne (jac.injective_aj_of_mono
        (mono_ajHom_of_hasNoFibreAffineLine h.isProper h.smooth h.connected jac
          (hasNoFibreAffineLine_of_one_le_x1Genus hN hg h hchar)) strX hc)⟩

/-- **The genus formula in its geometric form: `genus X_1(N) ≥ 1` makes
the Jacobian nontrivial** (PROVEN 2026-07-27, over
`hasNonconstantAbelianMap_of_one_le_x1Genus` and the two proven bridges
of `X0.lean`) — the arithmetic-to-geometry bridge, and the ONLY place
where the computed number `x1Genus N` meets the scheme `X`.

**Why `¬ IsIso jstr` rather than a genus.**  There is no genus of a
scheme at this pin, but `dim J = 0` ⟺ `J ≅ Spec ℚ` ⟺ `IsIso jstr` for an
abelian scheme over a field.  So `¬ IsIso jstr` is a faithful,
pin-available rendering of `genus ≥ 1` needing no dimension theory — and
it is precisely the hypothesis of `X0.lean`'s
`injective_aj_of_not_isIso_jacobian`, which is where this feeds.

EVERY HYPOTHESIS IS LOAD-BEARING, and two of them make the statement
FALSE if dropped.

* `hN : 5 ≤ N` — see the VALIDITY RANGE note on `x1Genus`.  At `N = 1`
  the definition evaluates to `x1Genus 1 = 1`, so `hg` is satisfiable,
  while `X_1(1) = ℙ¹` has genus `0` and its Jacobian IS trivial.  So the
  statement is FALSE without `hN`, and this is not a hypothetical: the
  `decide`-computable definition really does return `1` there.  In the
  proof `hN` is consumed by
  `hasNonconstantAbelianMap_of_one_le_x1Genus`, which carries the
  falsity for the same reason.
* `hg` — at genus `0` the conclusion is FALSE outright, `X_1(5)` (genus
  `0`, and `5 ≤ 5`) being a witness inside the validity range.  This is
  also what makes `one_le_x1Genus_twentyFive` consumed rather than
  floating.
* `jac` — without it `J` is an arbitrary abelian scheme over `ℚ`, and
  `Spec ℚ` itself is one.
* `h` — `N` enters the conclusion only through `hg` and `h`; without `h`
  the curve is unrelated to `x1Genus N`.

The proof is the two-step reading of the `¬ IsIso` phrasing, identical
to `not_isIso_jacobian_of_one_le_x0Genus`'s.  `IsIso jstr` makes every
`RelPoint jstr g` a subsingleton (`subsingleton_relPoint_of_isIso`),
hence Abel–Jacobi constant; and `exists_ne_aj_of_hasNonconstantAbelianMap`
says Abel–Jacobi cannot be constant once ANY abelian scheme receives a
nonconstant pointed map from `X`, which is what the leaf supplies.  Both
bridges are stated for an arbitrary curve over `ℚ` and are reused here
VERBATIM, with no edit to `X0.lean`. -/
theorem not_isIso_jacobian_of_one_le_x1Genus (N : ℕ) (hN : 5 ≤ N) (hg : 1 ≤ x1Genus N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) : ¬ IsIso jstr := by
  intro hiso
  obtain ⟨T, g, x, y, hxy⟩ := exists_ne_aj_of_hasNonconstantAbelianMap jac
    (hasNonconstantAbelianMap_of_one_le_x1Genus N hN hg h o)
  haveI := subsingleton_relPoint_of_isIso hiso g
  exact hxy (Subsingleton.elim _ _)

/-- **`rank J_1(25)(ℚ) = 0` and `genus X_1(25) ≥ 1`** (PROVEN, from three
leaves stated here plus two reused VERBATIM from `X0.lean`).

The original single sorry node — "the deep one", where all the weight of
the `Γ₁` layer was said to sit — has been split along the seams its own
statement exposes, in exactly the two rounds that `X0.lean`'s
`hasRankZeroJacobian_of_kenkuLevel` was split in.  `HasRankZeroJacobian`
is a conjunction of two conditions on the Jacobian with wildly different
costs, and each of those was itself carrying two unrelated theories.

* **The genus half is CLOSED.**  `x1Genus_twentyFive` proves
  `genus X_1(25) = 12` by `decide` on the classical formula — index,
  cusps and all, computed from `N = 25` — and `numRationalCuspsX1`
  together with `exists_rationalCuspsX1` supplies the Abel–Jacobi base
  point, so no separate existence leaf for a rational point on `X_1(25)`
  is needed.
* **The rank half is PROVEN** (2026-07-27) in
  `isTorsion_jacobian_x1TwentyFive`, over the three open leaves of this
  module's Kolyvagin–Logachev subsection, of which only the `L`-value
  computation is specific to level `25`.

The leaves under this node, and the single theory each one needs.  The
first row was itself a leaf until 2026-07-27 and is now a PROVEN wrapper
(over `exists_relPicZeroOf` and `isJacobianOf_of_isRelPicZeroOf` in
`X0.lean`), so the Albanese weight has moved to that file rather than
disappearing:

| leaf | theory | level-specific? | where stated |
|---|---|---|---|
| `exists_jacobianOf_curve` | Albanese / `Pic⁰` | no | here, **PROVEN** |
| `fg_relPoint_of_abelianScheme` | Mordell–Weil | no | `X0.lean`, REUSED |
| `exists_isLFunctionOf_of_isWeightTwoEigenformOn_gamma1` | Hecke continuation, `Γ₁` half | no | here, **PROVEN** |
| `exists_frickeInvolutionOn` | the Fricke involution `W_N` | no | here, **PROVEN 2026-07-28** |
| `isBigO_atTop_axisRestrictOn` | cusp-form decay at `i∞` | no | here, **PROVEN 2026-07-28** |
| `locallyIntegrableOn_axisRestrictOn` | continuity on the axis | no | here, **PROVEN 2026-07-28** |
| `isBigO_atTop_coeffOn` | Hecke's coefficient bound | no | here, **PROVEN 2026-07-28** |
| `isTorsion_jacobian_of_lFunction_ne_zero_gamma1` | Eichler–Shimura + Kolyvagin, `Γ₁` half | no | here, **PROVEN** |
| `exists_heckeIsotypicDecomposition_gamma1` | Eichler–Shimura | no | here, **PROVEN 2026-07-28** |
| `exists_heckeAction_isotypicQuotients_gamma1` | Shimura's `A_f` + the Hecke action | no | here, **PROVEN 2026-07-28** |
| `exists_heckeCorrespondenceFamilyGamma1` | the `Γ₁` Hecke correspondence, on points | no | here |
| `exists_modularHeckeAction_gamma1` | `T_ℓ` as an endomorphism of `J_1(N)` | no | here, **PROVEN 2026-07-28** |
| `exists_isotypicQuotient_of_isWeightTwoEigenformOn_gamma1` | Shimura's `A_f`, one factor | no | here, **PROVEN 2026-07-30** over the two rows below.  (This row read "**FALSE as stated**" until 2026-07-30; that was STALE — the FALSITY AUDIT's own header records the repair, which strengthened `IsModularHeckeActionGamma1` and left this statement untouched.) |
| `isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1` | Shimura's algebraicity, no scheme in it | no | here, NEW 2026-07-30 |
| `exists_isotypicQuotient_of_isIntegral_gamma1` | Shimura's `A_f` given algebraicity | no | here, NEW 2026-07-30 — the `Γ₁` twin of `X0.lean`'s `exists_isotypicQuotient_of_isIntegral` |
| `exists_heckeIsotypicDecomposition_of_isotypicQuotients_gamma1` | multiplicities, `finite_ker`, `neben` (now under `hN : N ≠ 0`) | no | here |
| `exists_cuspForm_gamma1GL_zero_lacunary` | the lacunary level-`0` cusp form; input to the `N = 0` refutation | no | here, **PROVEN 2026-07-30** — the `LacunaryLevelZero` section, six lemmas, no theory |
| `isTorsion_factor_of_heckeIsotypic_gamma1` | Kolyvagin–Logachev | no | here |
| `lFunction_apply_one_eq_two_pi_mul_cuspPeriod_gamma1` | Hecke's Mellin transform at `s = 1` | no | here, **PROVEN 2026-07-30** — the `G = Γ₁(N)` instance of `lFunction_apply_one_eq_two_pi_mul_cuspPeriodOn_of_le` |
| `cuspPeriod_ne_zero_x1TwentyFive` | `L`-value numerics (`lFunction_apply_one_ne_zero_x1TwentyFive` is PROVEN over this and the row above) | **yes** | here |
| `injective_aj_of_not_isIso_jacobian` | Riemann–Roch | no | `X0.lean`, REUSED |
| `not_birationalOver_affineLine_of_one_le_x1Genus_algClosed` | genus formula, over `K̄`, in characteristic prime to `N` | **yes** | here, NEW 2026-07-30, RESTATED the same day (`hchar`; the unguarded form is FALSE — `Ig(11)`) |
| `exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` | `Pic⁰` + degree-`n` Abel–Jacobi | no | here, NEW 2026-07-30, LEVEL-FREE |
| `not_isIso_of_smoothOfRelativeDimension_one` | rel. dimension of a standard smooth presentation | no | `CurveCompactification.lean`, REUSED, **PROVEN 2026-07-28** |

**Only TWO of the open rows are level-specific**, and neither of them
is Kolyvagin-Logachev.  The two `Γ₁`-half rows that used to be leaves are
now PROVEN assemblies (2026-07-28): the Hecke row over the four analytic
leaves listed under it, each stated once for every `G` between `Γ₁(N)` and
`Γ₀(N)` rather than separately for the two shapes, and the
Eichler–Shimura row over `IsHeckeIsotypicDecompositionGamma1` and the two
leaves under it, with `X0.lean`'s `isTorsion_of_finite_jointKer` reused as
the third step.  THREE of the rows are `X0.lean` theorems used
verbatim with no edit to that file — the concrete cash value of the
module docstring's claim that `HasRankZeroJacobian` is shared between the
layers.  The Albanese row is a fourth such reuse, one level deeper and now
PROVEN: its proof is two more `X0.lean` theorems consumed verbatim.

**REVISED 2026-07-27.**  This paragraph used to say that the Hecke and
Kolyvagin rows were "stated here in a form that SUBSUMES the
corresponding `X0.lean` statement".  They are not, and the direction is
now inverted: both `Γ₀` statements are PROVEN in `X0.lean` /
`WeightTwoEigenform.lean` over finer cuts, and the shape-free wrappers
here CONSUME them, so what is open in this file is the `Γ₁` half of each.
See the Kolyvagin–Logachev subsection docstring for the reversal, and for
why executing the recorded "disposal" would have re-opened two closed
nodes.

**AMENDED 2026-07-28, TWICE.**  The genus row was
`hasNonconstantAbelianMap_of_one_le_x1Genus` until that node was PROVEN;
what was open there next was its fibrewise half
`hasNoFibreAffineLine_of_one_le_x1Genus`, and that has since been PROVEN
too, over `X0.lean`'s level-free Lüroth pair
(`isDominant_of_not_exists_section`,
`birationalOver_affineLine_of_isDominant`) and
`eq_comp_of_birationalOver_affineLine_toAbelianScheme`.  What was open
there next was the single arithmetic leaf
`exists_nonconstant_toAbelianScheme_of_one_le_x1Genus` — so the genus row
moved down two levels in one day and the `Γ₁` cost of the genus
formula became one leaf, one FEWER than the `Γ₀` layer's (which
additionally carries `pos_of_isX0Compactification_of_fieldPoint` for want
of an `hN`).

**AMENDED AGAIN 2026-07-30**, a third level down.  That leaf is now PROVEN
too, by separating the two theories it bundled: the genus formula over an
algebraically closed field
(`not_birationalOver_affineLine_of_one_le_x1Genus_algClosed`, arithmetic,
the only row that still mentions `N`) and the `Pic⁰`/degree-`n`
Abel–Jacobi construction
(`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational`,
LEVEL-FREE).  The `Γ₁` cost of the genus formula is therefore two leaves
again — but only one of them is arithmetic, and the other would close the
`Γ₀` sibling leaf as well if relocated into `X0.lean`.  The algebraic
closure is not decoration: the same cut over an arbitrary field is FALSE,
refuted by the pointless conic `x² + y² + z² = 0` over `ℝ`, and the
audit is on the geometric leaf.
The third reuse —
`not_isIso_of_smoothOfRelativeDimension_one` — was REFUTED as stated
(`GeometricallyConnected` is vacuous over an empty base, so `X = S = ∅`,
`f = 𝟙 ∅` satisfied every hypothesis AND `IsIso f`), RESTATED over the
strictly weaker `Nonempty X`, PROVEN, and relocated out of `X0.lean` into
`CurveCompactification.lean`.  The call site here supplies the point from
`o`, exactly as `X0.lean`'s does; nothing else moved.

So the `Γ₀` and `Γ₁` layers between them have exactly **four** distinct
open general theories (Albanese — split into representability and
autoduality — Mordell-Weil, Riemann-Roch, and the `Γ₁` halves of Hecke
continuation and Eichler-Shimura/Kolyvagin) and **four** level-specific
leaves (two `L`-value computations, two genus formulas), not ten
independent ones.

WHY THE BUDGET SITS IN THE RANK HALF AND NOT IN THE POINT COUNT.  The
level-`25` docstring in `MazurTorsion.lean` presents `#X_1(25)(𝔽_3) = 10`
alongside this as if the two were comparable inputs.  They are not: that
count is the cusp count `φ(25)/2` and its non-cuspidal half is the
elementary bound `#E(𝔽_3) ≤ 7 < 25` (see
`exists_x1Compactification_mod_prime`), whereas the rank half rests on
Eichler–Shimura and Kolyvagin–Logachev. -/
theorem hasRankZeroJacobian_x1TwentyFive {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification 25 strX strY jY) : HasRankZeroJacobian strX := by
  obtain ⟨cusp, -, -⟩ := exists_rationalCuspsX1 25 h
  let o : RelPoint strX (𝟙 SpecQ) := cusp (finCongr numRationalCuspsX1_twentyFive.symm 0)
  obtain ⟨J, jstr, ab, ⟨jac⟩⟩ := exists_jacobianOf_curve h.isProper h.smooth h.connected o
  refine ⟨J, jstr, ab, o, jac, ?_, ?_⟩
  · letI := ab.addCommGroup (𝟙 SpecQ)
    haveI := fg_relPoint_of_abelianScheme ab
    exact AddCommGroup.finite_of_fg_torsion _ (isTorsion_jacobian_x1TwentyFive h jac)
  · exact injective_aj_of_not_isIso_jacobian h.isProper h.smooth h.connected jac
      (not_isIso_jacobian_of_one_le_x1Genus 25 (by norm_num) one_le_x1Genus_twentyFive h jac)

/-- **Mazur's counting datum for `X_1(25)`, with the schemes eliminated**
(PROVEN over the leaves above — four of them as of 2026-07-27:
`exists_x1Compactification`, `exists_rationalCuspsX1`,
`exists_x1Compactification_mod_prime`, `hasRankZeroJacobian_x1TwentyFive`,
together with `exists_x1ReductionAt`.  The other two rows of this list are
now THEOREMS: `exists_inverse_of_smoothCompactification` and — through the
moduli dictionary — `exists_section_of_galoisInvariant`.)

This is the whole `Γ₁` layer as `FreyCurve/MazurTorsion.lean` consumes
it, and the point of stating it here is that its statement mentions no
scheme, no morphism and no moduli space: just two bare types, a
reduction, ten cusps, and the rule turning an elliptic curve over `ℚ`
with a rational point of order `25` into a non-cuspidal point.  That is
exactly the shape of `MazurX1Plane.IsX1TwentyFiveDatum`, so the assembly
there is elementary bookkeeping and the scheme-theoretic vocabulary stays
inside this module.

The four components correspond one-for-one to the datum's fields:
`hred` is `red_injective` (the rank-`0` reduction bound), `hcard` is
`card_ptF3`, `hcinj` is `cusp_injective` for the `φ(25)/2 = 10` rational
cusps, and the last conjunct is the moduli dictionary.

Finiteness of `PtF3` is deliberately NOT returned even though
`exists_x1Compactification_mod_prime` supplies it: `Nat.card PtF3 = 10`
already forces it (`Nat.finite_of_card_ne_zero`), and the consumer
derives it that way.  Returning both would leave one of them unconsumed. -/
theorem exists_cuspidalCountingDatum_twentyFive :
    ∃ (Pt PtF3 : Type) (red : Pt → PtF3) (cusp : Fin 10 → Pt),
      Function.Injective red ∧ Nat.card PtF3 = 10 ∧ Function.Injective cusp ∧
        ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ P : E.toAffine.Point,
          addOrderOf P = 25 → ∃ p : Pt, ∀ i, p ≠ cusp i := by
  obtain ⟨X, Y, strX, strY, jY, ⟨hX⟩⟩ := exists_x1Compactification 25 (by norm_num)
  obtain ⟨X', Y', strX', strY', jY', ⟨hX'⟩, -, hcard⟩ :=
    exists_x1Compactification_mod_prime 25 3 10 (by decide)
  obtain ⟨red, hred⟩ := exists_injective_reduction_of_rankZeroJacobian hX
    (hasRankZeroJacobian_x1TwentyFive hX) Nat.prime_three (by norm_num) (by decide) hX'
  obtain ⟨cusp, hcinj, hcusp⟩ := exists_rationalCuspsX1 25 hX
  refine ⟨RelPoint strX (𝟙 SpecQ), RelPoint strX' (𝟙 (SpecF 3)), red,
    fun i => cusp (finCongr numRationalCuspsX1_twentyFive.symm i), hred, hcard,
    fun i j hij => (finCongr numRationalCuspsX1_twentyFive.symm).injective (hcinj hij), ?_⟩
  intro E hE P hP
  haveI := hE
  obtain ⟨p, hp⟩ := exists_notCusp_of_ratPoint (N := 25) (by norm_num) hX E P hP
  refine ⟨p, fun i heq => hp ?_⟩
  rw [heq]
  exact hcusp _

end Fermat
