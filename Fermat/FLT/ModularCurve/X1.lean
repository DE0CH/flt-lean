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
public import Mathlib.NumberTheory.DirichletCharacter.Basic
-- infinite Galois theory: `InfiniteGalois.mem_range_algebraMap_iff_fixed`, the field-theoretic
-- half of `exists_specSection_of_specGal_invariant` below.  `public` because that theorem's
-- statement mentions `Field.absoluteGaloisGroup`; see the private-import trap in the doctrine.
public import Mathlib.FieldTheory.Galois.Infinite

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
Galois orbits, and the `φ(N)/2` cusps lying over the cusp `∞` of
`X_0(N)` — indexed by `(ℤ/N)ˣ/±1` — are `ℚ`-RATIONAL, the Galois action
on them being trivial.  At `N = 25` that is `10`, and the remaining `18`
are not rational (those over `0` are defined over `ℚ(ζ₂₅)⁺`, of degree
`10`).

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
| `exists_gamma1RigidifiedModuli` | Katz-Mazur 4.7.2 + 5.1.1 + 6.6.2 and the affineness parenthesis of 8.1.1: the AFFINE FINE moduli scheme of `[Γ₁(N)], [Γ(n)]`.  The one citation half of the former `exists_gamma1Rigidification`, which is PROVEN over this row and the two below it (2026-07-28), as are `exists_gamma1GITPresentation`, `nonempty_gamma1GITPresentation_of_rigidification`, `isDomain_of_`, `smoothOfRelativeDimension_of_` and `geometricallyConnected_of_gamma1GITPresentation`. | any `K`, `char K ∤ N`, `char K ∤ n` |
| `exists_gamma1FullLevelStructure_cover` | Katz-Mazur 2.3.1 / 8.1.1: the finite etale `GL₂(ℤ/n)`-torsor of full level-`n` structures.  A statement about ONE datum; names no moduli scheme. | any `K`, `char K ∤ n` |
| `exists_gamma1DeckAction` | NO citation — the deck action, `strM_invariant`, `dM_equivariant` and the coequalising clause, all consequences of the fine moduli property.  `X0.lean`'s `exists_deckAction_of_torsion` proves the `Γ₀` analogue except for the coequalising clause. | any base scheme `S` |
| `smooth_coarseRing_of_gamma1GITPresentation` | Deligne-Rapoport III.1, Katz-Mazur 8.2.1: `B = A^G` is a smooth `K`-algebra of Krull dimension one.  (`locallyStandardSmooth_of_gamma1GITPresentation` is PROVEN over it, 2026-07-28, together with the release's `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`.) | any `K`, `char K ∤ N` |
| `exists_gamma1Datum_fieldExtension` | an elliptic curve with a point of exact order `N` over SOME extension of `K` — no modular curves in it.  (`geometricComponents_of_gamma1GITPresentation` is PROVEN over this row and the two below it, 2026-07-28, and `nontrivial_A_of_gamma1GITPresentation` over this one alone.) | any `K`, `char K ∤ N` |
| `isReduced_A_of_gamma1GITPresentation` | Katz-Mazur 8.2.1: `Spec A` is smooth over `K`, hence reduced | any `K`, `char K ∤ N` |
| `transitiveMinimalPrimes_of_gamma1GITPresentation` | Deligne-Rapoport IV.5.5: `det` is onto, so `G` permutes the components of `Spec A` transitively | any `K`, `char K ∤ N` |
| `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` | Deligne-Rapoport IV.5.5 — `det` is onto for `[Γ₁(N)]`, i.e. `Frac B / K` is a regular extension (`K` algebraically closed in `Frac B`, separably generated).  `connectedSpace_tensorProduct_of_gamma1GITPresentation` is PROVEN over it, 2026-07-28. | any `K`, `char K ∤ N` |
| `exists_rationalCuspPointsX1_field` | `φ(N)/2` rational cusps of `X_1(N)` (Deligne-Rapoport VI.5).  Base field FREED 2026-07-28: this single leaf now carries the former `exists_rationalCuspPointsX1` (over `ℚ`, PROVEN over it) and the `≥` half of the former `card_cuspLocusPoints_x1_finiteField` (over `𝔽_3`) — one sentence of Deligne-Rapoport that used to be two open leaves at two bases. | any `K` with `N` invertible |
| `exists_fineGamma1Atlas` | fineness at `N ≥ 4`, `ℓ` prime, `ℓ ∤ N`: `[Γ₁(N)]` is representable, so some atlas has `M ⟶ Y` an isomorphism.  (Was `nonempty_relPoint_atlas_of_relPoint`, REFUTED and restated 2026-07-28 — see its FALSITY AUDIT; the `∀ atlas` form is false at the Katz–Mazur atlas itself.) | `𝔽_ℓ` |
| `nonempty_gamma1Datum_baseChange` | base change of a `Γ₁(N)`-datum — formal, no arithmetic | any |
| `exists_weierstrassModel_of_abelianSchemeStruct_finiteField` | **Riemann-Roch on a genus-one curve** — a Weierstrass model of an abelian scheme of relative dimension one over `Spec 𝔽_ℓ`; NO modular curves and no level structure.  Cut 2026-07-28 as the geometry half of `exists_weierstrassEquiv_of_gamma1Datum` (now PROVEN over it).  The ℚ-side chain in `EllipticScheme.lean` is hardcoded to `Spec ℚ` and its own three leaves are open, so there is nothing to instantiate. | `𝔽_ℓ` |
| `exists_relPointAddEquiv_of_weierstrassModel_finiteField` | the transport half of the same cut: given the model, the `𝔽_ℓ`-SECTIONS are `W(𝔽_ℓ)`.  The content is that the abelian scheme's group law agrees with the chord-and-tangent law (rigidity); strictly easier than the ℚ-side `exists_geomFibreAddEquiv_of_weierstrassModel`, which needs a `Γ_ℚ`-equivariant equivalence on geometric fibres. | `𝔽_ℓ` |
| `card_cuspLocusPoints_x1_finiteField_le` | the cusp count on the special fibre, UPPER bound only (2026-07-28) — the hard direction of Ogg's description, that no cusp outside the distinguished orbit is `𝔽_ℓ`-rational.  The lower bound is the row above; `card_cuspLocusPoints_x1_finiteField` is PROVEN over the two. | `𝔽_ℓ` |
| `exists_x1CurveModel_of_base` | the integral model — Deligne-Rapoport / Igusa for `Γ₁(N)`.  The reduction map is no longer part of the leaf: `exists_x1ReductionAt` is PROVEN over this plus the moduli-free `NeronReduction.lean` | `ℚ → 𝔽_ℓ` |
| `exists_section_of_galoisInvariant` | Galois descent of a rational point to a section | `ℚ` |
| `exists_heckeIsotypicDecomposition_gamma1` | Eichler-Shimura for `J_1(N)`, as a datum | `ℚ` |
| `isTorsion_factor_of_heckeIsotypic_gamma1` | Kolyvagin-Logachev on an isotypic factor | `ℚ` |
| `exists_frickeInvolutionOn` | the Fricke involution `W_N` on `Γ₁(N) ≤ G ≤ Γ₀(N)` | `ℚ` |
| `isBigO_atTop_axisRestrictOn` | a cusp form decays faster than every power at `i∞` | `ℚ` |
| `locallyIntegrableOn_axisRestrictOn` | continuity of `y ↦ f(iy/√N)` on `(0, ∞)` | `ℚ` |
| `isBigO_atTop_coeffOn` | Hecke's bound `\|aₙ\| = O(n)` | `ℚ` |
| `lFunction_apply_one_ne_zero_x1TwentyFive` | `L`-value numerics — the DEEP one | `ℚ` |
| `hasNoFibreAffineLine_of_one_le_x1Genus` | the genus formula, fibrewise — `genus X_1(N) ≥ 1` puts no rational curve in any fibre.  (`hasNonconstantAbelianMap_of_one_le_x1Genus` is PROVEN over it, 2026-07-28, together with `X0.lean`'s level-free `mono_ajHom_of_hasNoFibreAffineLine` and `not_isIso_of_smoothOfRelativeDimension_one`.) | any |

(Table regenerated at the release-10 integration, 2026-07-28, from the
compiler's `declaration uses 'sorry'` set rather than from any branch's prose;
it agrees row-for-row with a comment-stripped source scan.  Fourteen rows.
The last row was replaced 2026-07-28 when the node above it closed; a stray
duplicate of it, left by a merge, was removed at the same time.)

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
genuinely differs between the bases survives as a separate leaf:
`card_cuspLocusPoints_x1_finiteField_le`, the `≤` half, which needs the count
EXACTLY and so cannot be shared with a `ℚ` side that is a lower bound.

**Reorganised 2026-07-27, along the RESIDUE-FIELD axis at both bases.**
`nonempty_cuspLocusX1` and `card_cusp_x1_finiteField` are now THEOREMS; what
was open in them is `exists_rationalCuspPointsX1_field` and
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
| `exists_rigidifiedModuli` (leaf) | `exists_gamma1RigidifiedModuli` (leaf) |
| `exists_fullLevelStructure_cover` (leaf) | `exists_gamma1FullLevelStructure_cover` (leaf) |
| `exists_deckAction` (leaf) | `exists_gamma1DeckAction` (leaf) |
| — | `nonempty_gamma1Rigidification_of_rigidifiedModuli` (PROVEN); `exists_gamma1Rigidification` (PROVEN over the three leaves) |
| `exists_descendClassify` (PROVEN) | `exists_descendClassifyGamma1` (PROVEN) |
| `exists_gamma0Datum_baseChange` (PROVEN) | `exists_gamma1Datum_baseChange` (PROVEN) |
| `gamma0Atlas_isIso` + `isAffine_of_gamma0Atlas` (PROVEN) | not needed — see the section comment on the geometry below |
| `isDomain_of_gamma0GITPresentation` (leaf) | `geometricComponents_of_gamma1GITPresentation` (PROVEN 2026-07-28 over three leaves — `exists_gamma1Datum_fieldExtension`, `isReduced_A_of_gamma1GITPresentation`, `transitiveMinimalPrimes_of_gamma1GITPresentation`); `isDomain_of_gamma1GITPresentation` is PROVEN over it |
| `smoothOfRelativeDimension_of_gamma0GITPresentation` (leaf) | `locallyStandardSmooth_of_gamma1GITPresentation` (leaf); `smoothOfRelativeDimension_of_gamma1GITPresentation` is PROVEN over it |
| `geometricallyConnected_of_gamma0GITPresentation` (leaf) | `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` (leaf); `connectedSpace_tensorProduct_of_gamma1GITPresentation` and `geometricallyConnected_of_gamma1GITPresentation` are PROVEN over it |
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
(8.2.1, smoothness) and
`transitiveMinimalPrimes_of_gamma1GITPresentation` (IV.5.5, the
`det`-surjectivity).  The ROUTE AUDIT on the last of those records why
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
`exists_descendClassifyGamma1` consumes only the second. -/

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
  rigidifications of one datum, not merely `𝟙` and `Spec σ` for a global
  `σ : G`.  Without this field the descent below is FALSE — see the
  section comment. -/
  coequalises : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Spec (CommRingCat.of A))
    (d₁ : Gamma1Datum N Z), IsBaseChangeOfGamma1 a d₁ dM →
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
      (d₁ : Gamma1Datum N Z), IsBaseChangeOfGamma1 a d₁ dM →
      IsBaseChangeOfGamma1 b d₁ dM →
      a ≫ specInvariantsQuotient G A = b ≫ specInvariantsQuotient G A)
    (T : Scheme.{0}) (g : T ⟶ S) (d : Gamma1Datum N T) :
    ∃ c : T ⟶ Spec (CommRingCat.of ↥(FixedPoints.subring A G)),
      c ≫ str = g ∧
      ∀ (Z : Scheme.{0}) (k : Z ⟶ T) (dZ : Gamma1Datum N Z),
        IsBaseChangeOfGamma1 k dZ d →
        ∀ m : Z ⟶ Spec (CommRingCat.of A), IsBaseChangeOfGamma1 m dZ dM →
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
    rw [← Category.assoc, ← Category.assoc]
    exact hcoeq (g₁ ≫ m₀) (g₂ ≫ m₀) d₁ (b₁.comp bm) ((hb.cancel bp).comp bm)
  refine ⟨EffectiveEpi.desc p (m₀ ≫ specInvariantsQuotient G A) key, ?_, ?_⟩
  · -- the descended map is a morphism over `S`: check it after the epimorphism `p`
    refine (cancel_epi p).mp ?_
    rw [← Category.assoc, EffectiveEpi.fac, Category.assoc, hstr, hst]
  · -- independence of the cover: compare on `Z ×_T T'`
    intro Z k dZ bk m bmZ
    have hcond : Limits.pullback.fst k p ≫ k = Limits.pullback.snd k p ≫ p :=
      Limits.pullback.condition
    obtain ⟨dW, ⟨bq⟩⟩ := exists_gamma1Datum_baseChange (Limits.pullback.fst k p) dZ
    have hb : IsBaseChangeOfGamma1 (Limits.pullback.snd k p ≫ p) dW d := by
      rw [← hcond]; exact bq.comp bk
    have h1 : (Limits.pullback.fst k p ≫ m) ≫ specInvariantsQuotient G A
        = (Limits.pullback.snd k p ≫ m₀) ≫ specInvariantsQuotient G A :=
      hcoeq _ _ dW (bq.comp bmZ) ((hb.cancel bp).comp bm)
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
      (fun {_Z} a b d₁ h₁ h₂ => R.coequalises a b d₁ h₁ h₂) T g d
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
    obtain ⟨Z, p, dZ, m, hf, hs, hq, -, ⟨bp⟩, ⟨bm⟩⟩ := R.cover g' d'
    haveI := hf; haveI := hs; haveI := hq
    have h1 := hc2 T' g' d' Z p dZ bp m bm
    have h2 := hc2 T g d Z (p ≫ h) dZ (bp.comp bch) m bm
    refine (cancel_epi p).mp ?_
    rw [h1, ← Category.assoc, h2]
  · -- the classifying map of the universal family is the quotient map: read
    -- the characterisation at the trivial cover of `Spec A`, rigidified by `𝟙`.
    show c _ R.strM R.dM = Spec.map (CommRingCat.ofHom
      (algebraMap ↥(FixedPoints.subring R.A R.G) R.A))
    have h1 := hc2 _ R.strM R.dM _ (𝟙 _) R.dM (IsBaseChangeOfGamma1.refl R.dM) (𝟙 _)
      (IsBaseChangeOfGamma1.refl R.dM)
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
| the fine moduli scheme `𝔐([Γ₁(N)], [Γ(n)])`, AFFINE | `Gamma1RigidifiedModuli` / `exists_gamma1RigidifiedModuli` | **LEAF** (4.7.2 + 5.1.1 + 6.6.2, and the affineness parenthesis of 8.1.1) |
| the level-`n` torsor: every datum acquires a full level structure fpqc-locally | `exists_gamma1FullLevelStructure_cover` | **LEAF** (2.3.1 / 8.1.1) |
| the deck action `GL₂(ℤ/n) ↷ A`, its invariance over `S`, `dM_equivariant` and `coequalises` | `exists_gamma1DeckAction` | **LEAF** (formalisation only; no new citation — see its docstring) |
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
to `Γ₁` unchanged.  That single edit turns `exists_gamma1DeckAction` from
a leaf into a transcription of `exists_deckAction_of_torsion` whose only
genuinely open step is the coequalising clause. -/

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

/-- **The rigidified moduli scheme of `[Γ₁(N)], [Γ(n)]` over a field in
which `N` and `n` are invertible exists, and is AFFINE** (sorry leaf,
opened 2026-07-28) — Katz–Mazur, and NOTHING else.  This is the one
citation half of `exists_gamma1Rigidification`.

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
  sorry

/-- **Every `Γ₁(N)`-datum over a `K`-scheme acquires a full level-`n`
structure after an fpqc cover** (sorry leaf, opened 2026-07-28) — the
`Γ₁` analogue of `X0.lean`'s `exists_fullLevelStructure_cover`, and
Katz–Mazur's finite étale `GL₂(ℤ/n)`-torsor `[Γ(n)]`.

This is a statement about ONE datum: it names no moduli scheme, no deck
group and no rigidification, which is what lets it be dispatched
independently of everything else in this block.

## The route

`E[n] ⟶ T` is finite étale of rank `n²` because `n` is invertible on `T`
(5.1.1's last sentence, or directly: `[n] : E ⟶ E` is finite étale away
from `char ∣ n`), and the sheaf of bases of `E[n]` is a
`GL₂(ℤ/n)`-torsor over `T`, hence has a section after a finite étale —
in particular flat, surjective, quasi-compact — cover.  `X0.lean` splits
its `Γ₀` analogue further, into `exists_gamma0Datum_baseChange` (PROVEN),
the geometric-fibre citation `exists_torsionBasis_geomPoint`, the torsor
proper `exists_torsionBasis_cover_of_geomPoint`, and the PROVEN transport
`nonempty_fullLevelStructure_of_geomBasis`.  **All four are stated for a
bare abelian scheme of relative dimension one and none of them mentions
`Gamma0Datum` except through `d.ab`** — so once `Gamma1BaseChange`
supplies `nonempty_gamma1Datum_baseChange` (already a leaf in this file),
this node reduces to them without new mathematics.

## Faithfulness

`hchar` is load-bearing for TRUTH, not merely for the intended proof: in
characteristic `p ∣ n` the scheme `E[n]` is not étale, its geometric
fibres are not `(ℤ/n)²`, and `geom_basis` is unsatisfiable — no cover
helps.  `g` is therefore load-bearing too: it is what makes `T` a
`K`-scheme, and without it the statement is false at a base of bad
characteristic.  `hn` is load-bearing at `n = 0`, where
`AbelianFullLevelStructure 0` is unsatisfiable. -/
theorem exists_gamma1FullLevelStructure_cover {N : ℕ} (n : ℕ) (hn : 3 ≤ n)
    (K : Type) [Field K] (hchar : ¬ ringChar K ∣ n)
    {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of K)) (d : Gamma1Datum N T) :
    ∃ (T' : Scheme.{0}) (p : T' ⟶ T) (d' : Gamma1Datum N T'),
      AlgebraicGeometry.Flat p ∧ AlgebraicGeometry.Surjective p ∧ QuasiCompact p ∧
      Nonempty (IsBaseChangeOfGamma1 p d' d) ∧
      Nonempty (AbelianFullLevelStructure n d'.ab) :=
  sorry

/-- **The deck group acts on the rigidified coordinate ring, over the
base, equivariantly, and its quotient map coequalises rigidifications**
(sorry leaf, opened 2026-07-28) — the formalisation half of
`exists_gamma1Rigidification`.  **It carries no citation**: everything it
asserts is a consequence of `R.universal`, and the Katz–Mazur input is
`R` itself.

## STATUS: this is the `Γ₁` transcription of a node that is ALREADY PROVEN

`X0.lean`'s `exists_deckAction_of_torsion` proves the corresponding `Γ₀`
statement in full except for the coequalising clause, which it leaves as
a sorried `have` inside the proof.  The argument transcribes verbatim,
because it touches the level structure only through the twist API:

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
safe. -/
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
        IsBaseChangeOfGamma1 a d₁ R.dM → IsBaseChangeOfGamma1 b d₁ R.dM →
        a ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A
          = b ≫ specInvariantsQuotient (gamma0DeckGroup n) R.A :=
  sorry

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
            coequalises := fun {Z} a b d₁ ha hb => hcoeq a b d₁ ha hb }⟩
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
| `geometricallyConnected_of_gamma1GITPresentation` | `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation` | `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` + `pullbackSpecIso`, then (2026-07-28) `isDomain_tensorProduct_of_injective` |

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

/-- **A ring of invariants is a DOMAIN as soon as the group permutes the
minimal primes transitively** (PROVEN 2026-07-27, pure commutative
algebra — no moduli problem, no base field, mathlib-facing).

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
    obtain ⟨σ, hσ⟩ := htrans p hp q hq
    rw [← hσ, Ideal.mem_comap]
    have hfix : MulSemiringAction.toRingHom G A σ (algebraMap B A y) = algebraMap B A y := by
      simp [MulSemiringAction.toRingHom]
    rw [hfix]
    exact hbp
  exact NoZeroDivisors.to_isDomain B

/-- **`[Γ₁(N)]` is nonempty over SOME field extension of `K`** (sorry
leaf, cut 2026-07-28 out of `geometricComponents_of_gamma1GITPresentation`)
— an elliptic curve carrying a point of exact order `N`, over some
extension field of `K`.

TRUE and elementary, and much weaker than anything about modular curves:
`L := AlgebraicClosure K` already works.  Over an algebraically closed
field of characteristic prime to `N` one has `E[N] ≅ (ℤ/N)²` for every
elliptic curve `E`, so a point of exact order `N` exists; and its order
does not change under further base change to an algebraically closed
field, which is what `PointOfExactOrder.geom_order` asks.  Concretely one
may also take the Tate normal form
`y² + (1 − c)xy − by = x³ − bx²` with the point `(0, 0)`, whose exact
order is `N` on the level-`N` locus.

This is deliberately the WEAKEST form that its consumer
`nontrivial_A_of_gamma1GITPresentation` needs: no algebraic closedness,
no rationality over `K` itself — and rationality over `K` would be FALSE,
since `Y_1(N)(K)` can be empty (`isEmpty_gamma1Datum_finiteField` is the
extreme case, and the whole point of this module is that `Y_1(25)(ℚ)`
contains no non-cuspidal point).

Note the ORDER of quantifiers: `L` may depend on `K` and `N`.  Nothing
downstream sees `L`; it is consumed immediately by `classify` and
discarded.

The hypotheses are REQUIRED: at `char K ∣ N` the group scheme `E[N]` is
not étale and a section of exact order `N` need not exist at all (at
`N = p = char K` and `E` supersingular there is none over any
extension). -/
theorem exists_gamma1Datum_fieldExtension (N : ℕ) (_hN : 4 ≤ N)
    (K : Type) [Field K] (_hchar : ¬ ringChar K ∣ N) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L),
      Nonempty (Gamma1Datum N (Spec (CommRingCat.of L))) :=
  sorry

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

/-- **The rigidified moduli scheme is reduced** (sorry leaf, cut
2026-07-28 out of `geometricComponents_of_gamma1GITPresentation`) —
Katz–Mazur 8.2.1.

TRUE and classical: `𝔐([Γ₁(N)], [Γ(n)])` is SMOOTH over `ℤ[1/Nn]`
(8.2.1), hence smooth over every field `K` in which `N` is invertible,
and a smooth algebra over a field is reduced (it is even regular).  This
is the SAME geometric input as `locallyStandardSmooth_of_gamma1GITPresentation`
— which states smoothness of the invariants `B` rather than of `A` — and
whoever proves either of them should look at the other: over a field, `A`
smooth gives `B = A^G` normal by descent, and the two leaves are two
readings of Katz–Mazur 8.2.1.

Reducedness rather than smoothness is stated because reducedness is all
that `isDomain_of_minimalPrimes_transitive` consumes; asking for
`IsSmooth` here would make the leaf carry 8.2.1 a second time.

The hypotheses are REQUIRED: at `char K ∣ N` the moduli problem is not
smooth (`[Γ₁(p)]` in characteristic `p` is not étale over the
`j`-line) and `Spec A` acquires nilpotents. -/
theorem isReduced_A_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; IsReduced P.A :=
  sorry

/-- **The deck group permutes the components of the rigidified moduli
scheme transitively** (sorry leaf, cut 2026-07-28 out of
`geometricComponents_of_gamma1GITPresentation`) — Deligne–Rapoport
IV.5.5, Katz–Mazur (8.1.1).

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
i.e. only downstream of `isReduced_A_of_gamma1GITPresentation`
strengthened to smoothness, or with the Weil-pairing map carried as a
FIELD of `Gamma1Rigidification` / `Gamma1GITPresentation` (the level-`n`
torsor and its `det`-equivariant pairing, which is what Katz–Mazur
(8.1.1) actually constructs).  That structural repair is the recommended
route, and it is the same shape as the `coequalises` field: a clause the
construction supplies for free and that no abstract presentation implies.
*Refuting check*: produce a finite `K`-subalgebra of the above `A`
separating `(x)` from `(y)`.

The hypotheses are REQUIRED: at `N = 0`, or at `char K ∣ N`, the moduli
problem is not representable by a nonempty smooth scheme and
`minimalPrimes A` is not the component set of anything. -/
theorem transitiveMinimalPrimes_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_A; letI := P.group_G; letI := P.action_GA;
    ∀ p ∈ minimalPrimes P.A, ∀ q ∈ minimalPrimes P.A,
      ∃ σ : P.G, Ideal.comap (MulSemiringAction.toRingHom P.G P.A σ) p = q :=
  sorry

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

/-- **The coarse ring `B = A^G` is a SMOOTH `K`-algebra of Krull dimension
one** (sorry leaf, opened 2026-07-28 as the whole modular content of
`locallyStandardSmooth_of_gamma1GITPresentation`, which is now a theorem
over it) — Deligne–Rapoport III.1, Katz–Mazur 8.2.1.

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

## THE ROUTE FROM `A`, AND EXACTLY WHAT IS MISSING FOR IT

A prover who wants to push this one step further down, onto the
rigidified ring `A` where Katz–Mazur actually applies, needs three
things, of which two already exist:

1. *`Algebra.FiniteType K B` from `Algebra.FiniteType K A`* — PROVEN, as
   `Algebra.IsInvariant.finiteType_of_isInvariant`
   (`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`).  It needs
   only `Finite G` and `P.injective_algebraMap`, no domain hypothesis.
2. *`ringKrullDim B = ringKrullDim A`* — the pieces are
   `dimensionLEOne_of_isInvariant` and `ringKrullDim_eq_one_of_isInvariant`
   in the same file, but **both carry `[IsDomain S]`, i.e. `IsDomain A`,
   which is FALSE here** — see the docstring of
   `geometricComponents_of_gamma1GITPresentation`: as soon as `ζ_n ∈ K`
   the scheme `𝔐([Γ₁(N)], [Γ(n)])` has `φ(n)` components.  The domain
   hypothesis is used in exactly one place, the appeal to
   `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`, and
   `Ideal.exists_ideal_over_prime_of_isIntegral`
   (`Mathlib/RingTheory/Ideal/GoingUp.lean`) is the general going-up
   statement that replaces it, its side condition `ker ⊆ p` being free
   from `P.injective_algebraMap`.  *The check that would refute this*:
   read the proof of `dimensionLEOne_of_isInvariant` and find a second
   use of `IsDomain S`.
3. *Descent of smoothness along the `G`-torsor `Spec A → Spec B`* — this
   is the genuinely missing one.  It is Stacks `02VL` ("if `X → Y` is
   surjective, flat and locally of finite presentation and `X → S` is
   smooth, then `Y → S` is smooth"), and mathlib's descent at this pin
   goes the other way: `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`
   and `RingHom.Smooth.codescendsAlong_faithfullyFlat`
   (`Mathlib/RingTheory/Etale/Descent.lean`) descend along a faithfully
   flat extension of the BASE, not along a cover of the target.  *The
   check that would refute this*: a lemma in
   `Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/Morphisms/`
   concluding `Smooth R B` from `Smooth R A` and flatness of `B → A`.

Until item 3 exists, cutting this leaf onto `A` would trade one modular
leaf for one modular leaf plus a missing descent theorem, which is why it
is stated about `B`.

## FAITHFULNESS

`hchar` is load-bearing: at `char K ∣ N` the moduli problem is not smooth
over `K` and `[Γ₁(N)]` degenerates.  `hN` is inherited rather than
strictly needed for the CONCLUSION — a coarse space of a tame quotient is
still a smooth curve — but it is what makes the free-action route above
available, and it is required by every consumer, so it is kept.

`ringKrullDim B = 1` needs `Spec B` NONEMPTY, which is the same input as
`Nontrivial P.A` in `geometricComponents_of_gamma1GITPresentation`: at
`N = 0`, or at `char K ∣ N`, `B` would be the zero ring and its Krull
dimension `⊥ ≠ 1`.  So the two leaves of this block agree about when the
moduli space exists, and neither is vacuous.

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
theorem smooth_coarseRing_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K))) :
    letI := P.commRing_B; letI := P.algebraB;
    Algebra.Smooth K P.B ∧ ringKrullDim P.B = (1 : ℕ) :=
  sorry

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

/-- **`Frac B` is a REGULAR field extension of `K`** (sorry leaf, cut
2026-07-28 out of `connectedSpace_tensorProduct_of_gamma1GITPresentation`) —
Deligne–Rapoport IV.5.5, in the function-field form.

For every field extension `L/K` the ring `Frac B ⊗[K] L` is a domain.  That
is the classical statement that `Frac B / K` is a **regular** field
extension — equivalently, by MacLane's criterion, that `K` is algebraically
closed in `Frac B` and `Frac B / K` is separably generated; equivalently
again, that `Y_1(N)` is geometrically INTEGRAL over `K`.

TRUE and classical, and this is where the second genuinely modular
geometric input now sits.  The criterion is that the subgroup of `GL₂(ℤ/N)`
attached to the level structure surjects onto `(ℤ/N)ˣ` under `det`; for
`[Γ₁(N)]` that subgroup is `{[[1, b], [0, d]]}`, whose determinant is `d`,
so `det` IS surjective, `K` is algebraically closed in `Frac B`, and the
geometric fibres of `Y_1(N)` over `ℤ[1/N]` are connected.  That is the
q-expansion-principle content of IV.5.5.

## Why `IsDomain P.B` is a HYPOTHESIS here and not a consequence

Without `_hB` this statement would carry integrality a second time: at
`L := K` it reads `IsDomain (Frac B)`, which forces `IsDomain B`.  This
development obtains integrality from
`geometricComponents_of_gamma1GITPresentation` instead — from the components
of the RIGIDIFIED scheme, which is where Katz–Mazur (8.1.1) actually leaves
it — so taking `_hB` as an input confines this leaf to the
regular-extension content alone: given `_hB` the `L := K` case is trivial,
and the leaf therefore cannot be used to re-derive its sibling.  That is the
deliberate asymmetry with the `Γ₀` side recorded on the consumer below,
preserved rather than quietly dropped.

## The `Γ₀` sibling of this leaf exists, and CANNOT be reused verbatim

`isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot`
(`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`, itself a sorry
leaf) has exactly this conclusion, with the modular input replaced by the
hypotheses `[IsIntegrallyClosed B]`, `∀ x : B, IsAlgebraic k x → x ∈ ⊥` —
and **`[CharZero k]`**.  The `CharZero` is what blocks reuse: this leaf
quantifies over an arbitrary `K` with `char K ∤ N`, and the `𝔽_ℓ` case is
not decoration, it is what `exists_x1Compactification_finiteField` consumes.
Nor is that hypothesis lazy over there — its own faithfulness note gives the
counterexample (`k = 𝔽_p(u)`, `B = L = k(u^{1/p})`, where `L ⊗[k] L` carries
the nonzero nilpotent `u^{1/p} ⊗ 1 - 1 ⊗ u^{1/p}`).  So a shared, char-free
form of that leaf would need a SEPARABILITY input in place of `CharZero`,
and producing one is a strictly larger job than this leaf; it is recorded
here as the merge worth making if anyone generalises that file.

## Route for whoever proves this, in two independent halves

1. `K` is algebraically closed in `Frac B` — the modular half, IV.5.5 as
   above.
2. `Frac B / K` is separably generated — NOT modular, and free in
   characteristic `0`.  In characteristic `p` it follows from
   `locallyStandardSmooth_of_gamma1GITPresentation`: smooth over `K` implies
   geometrically reduced, which implies a separably generated function
   field.

MacLane's criterion turns 1 + 2 into regularity, and regularity gives the
conclusion for every `L` at once.

**What is missing from the pin, re-checked 2026-07-28.**  Mathlib has the
linear-disjointness theory (`Mathlib/FieldTheory/LinearDisjoint.lean` —
`IntermediateField.LinearDisjoint.isDomain`, `.isDomain'`,
`.exists_field_of_isDomain`, `.isField_of_forall`) and the relative
algebraic closure (`Mathlib/FieldTheory/AlgebraicClosure.lean`), but no
notion of a regular or primary extension, and nothing relating
`algebraicClosure` to base change.  *The checks that would refute this*:
`grep -rn "IsRegularExtension\|IsPrimaryExtension" .lake/packages/mathlib/Mathlib/`
returning anything, or a mathlib lemma whose conclusion is
`IsDomain (F ⊗[k] L)` and whose hypothesis mentions `algebraicClosure`.
`Mathlib/FieldTheory/SeparablyGenerated.lean` is the handle for half 2.

The hypotheses are REQUIRED: at `N = 0` or at `char K ∣ N` the moduli
problem is not representable by a nonempty smooth curve, and `Frac B` is
then not a regular extension of `K` — indeed `_hB` itself fails. -/
theorem isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation {N : ℕ} (_hN : 4 ≤ N)
    {K : Type} [Field K] (_hchar : ¬ ringChar K ∣ N)
    (P : Gamma1GITPresentation N (Spec (CommRingCat.of K)))
    (_hB : letI := P.commRing_B; IsDomain P.B)
    (L : Type) [Field L] [Algebra K L] :
    letI := P.commRing_B; letI := P.algebraB;
    IsDomain (TensorProduct K (FractionRing P.B) L) :=
  sorry

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

The five conclusions are exactly the hypotheses of
`AlgebraicGeometry.exists_isSmoothCompactification`, and none is
decoration: `QuasiCompact` and `IsSeparated` are what Nagata's
compactification consumes, `IsIntegral` is what makes the relative
normalization integral, `SmoothOfRelativeDimension 1` pins the relative
dimension of the compactification, and `GeometricallyConnected` is what
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
`AlgebraicGeometry.exists_isSmoothCompactification` and is not modular),
and, as of 2026-07-27, the GIT axis: the `Γ₁` analogue of
`exists_gamma0AffineModel` is now built above, the previous "NOT
searched" note is DISCHARGED.  What remains open below this node is a
representability statement plus three properties of one curve, in place of
one statement asserting a curve with five properties exists — and (release
14, 2026-07-28) each of the three has itself been cut once more, so the
LIVE leaves are:

* representability — `exists_gamma1RigidifiedModuli`,
  `exists_gamma1FullLevelStructure_cover`, `exists_gamma1DeckAction`
  (`exists_gamma1Rigidification` and `exists_gamma1GITPresentation` are
  PROVEN over them);
* the domain property — `exists_gamma1Datum_fieldExtension`,
  `isReduced_A_of_gamma1GITPresentation`,
  `transitiveMinimalPrimes_of_gamma1GITPresentation`
  (`geometricComponents_of_gamma1GITPresentation` and
  `isDomain_of_gamma1GITPresentation` are PROVEN over them);
* smoothness — `smooth_coarseRing_of_gamma1GITPresentation`
  (`locallyStandardSmooth_of_gamma1GITPresentation` and
  `smoothOfRelativeDimension_of_gamma1GITPresentation` are PROVEN over it);
* geometric connectedness —
  `isDomain_fractionRing_tensorProduct_of_gamma1GITPresentation`, which
  replaced `connectedSpace_tensorProduct_of_gamma1GITPresentation` (now
  PROVEN over it).

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
instead of the general `exists_isSmoothCompactification`, and so avoid the
open Nagata gluing induction
`AlgebraicGeometry.exists_isOpenImmersion_isProper_of_affineCase` — the
hardest leaf of `CurveCompactification.lean` — entirely.

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

/-- **`X_1(N)` has `φ(N)/2` cusps rational over ANY field `K` in which `N`
is invertible** (sorry leaf — Deligne–Rapoport VI.5, and ALL that is left
of the cusp route on BOTH sides).

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
identified as `ℚ(ζ_{gcd(d, N/d)})`; this one asks only for `φ(N)/2` points
of `X ∖ Y` with residue field `K`, and says nothing whatever about the
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
theorem exists_rationalCuspPointsX1_field (N : ℕ) (K : Type) [Field K]
    (_hNK : IsUnit ((N : ℕ) : K))
    {X Y : Scheme.{0}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strY : Y ⟶ Spec (CommRingCat.of K)} {jY : Y ⟶ X}
    (_h : IsX1Compactification N strX strY jY) :
    ∃ ε : Fin (numRationalCuspsX1 N) → ((Set.range jY.base)ᶜ : Set X),
      Function.Injective ε ∧ ∀ i, residueDegreeOver K strX (ε i).1 = 1 :=
  sorry

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

/-- **There is a FINE Katz–Mazur atlas over `𝔽_ℓ`: one whose atlas map
`M ⟶ Y` lifts every `𝔽_ℓ`-point of `Y`** (sorry leaf — this is where the
whole fineness content of the `Γ₁` point count now sits).

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
scheme. -/
theorem exists_fineGamma1Atlas (N ℓ : ℕ) (_hN : 4 ≤ N) (_hℓ : ℓ.Prime)
    (_hℓN : ¬ ℓ ∣ N) :
    ∃ A : Gamma1Atlas N (SpecF ℓ),
      ∀ y : RelPoint A.str (𝟙 (SpecF ℓ)),
        ∃ m : RelPoint A.strM (𝟙 (SpecF ℓ)),
          m.1 ≫ (A.classify A.strM A.dM).1 = y.1 :=
  sorry

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
Weierstrass presentation of a given abelian scheme — and it exists
nowhere in this tree, in mathlib, or in `~/cs/FLT`.  That converse is now
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
to be pushed back down again. -/
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

/-- **AT MOST `m` points of the cusp locus of `X_1(N)_{𝔽_ℓ}` have residue
degree one, at the witness rows** (sorry leaf — the ONE genuinely modular
half of the `(25, 3, 10)` row, and all that is left of
`card_cusp_x1_finiteField`).

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
only on the half that is still here.  The WITNESS-TABLE axis is refuted by
`x1WitnessTable` having one row: generalising to all `(N, ℓ)` would demand
the full `Γ₁` cusp classification and its reduction behaviour, which is
strictly more than the route needs. -/
theorem card_cuspLocusPoints_x1_finiteField_le (N ℓ m : ℕ)
    (_htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (_h : IsX1Compactification N strX strY jY) :
    Nat.card {c : ((Set.range jY.base)ᶜ : Set X) // residueFDegree strX c.1 = 1} ≤ m :=
  sorry

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
* `card_cuspLocusPoints_x1_finiteField_le` — half 2, the cusp count on the
  special fibre, and since 2026-07-28 only its UPPER bound.  STILL OPEN, and
  the only one of the four that is Deligne-Rapoport at this base.
  (`card_cusp_x1_finiteField` is PROVEN through `cuspEquivResidueDegreeOne`
  and `card_cuspLocusPoints_x1_finiteField`, which is itself PROVEN over this
  leaf together with `exists_rationalCuspPointsX1_field` at `K = 𝔽_ℓ`; the
  open statement is about the POINTS of `X ∖ Y` and their residue degrees,
  not about sections of `strX`.)

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

/-- **Deligne–Rapoport / Igusa for `Γ₁(N)`: `X_1(N)` has good reduction at
every `ℓ ∤ N`** (sorry leaf — and after the hoist below this is ALL that is
left of the rank-`0` criterion's geometry).

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
  `exists_isX0Compactification_specialFibre`, bundled in rather than split
  off because a producer builds the model and recognises its special fibre
  in one construction; splitting them would require naming the model twice.

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
theorem exists_x1CurveModel_of_base (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓN : ¬ ℓ ∣ N)
    (R : Subring ℚ) (toF : R →+* ZMod ℓ) (_hbase : IsReductionBase ℓ R toF)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (_hX : IsX1Compactification N strX strY jY) :
    ∃ (X' Y' XZ : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (strY' : Y' ⟶ SpecF ℓ)
      (jY' : Y' ⟶ X') (xstr : XZ ⟶ SpecLoc R),
      Nonempty (IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) ∧
        Nonempty (IsX1Compactification N strX' strY' jY') :=
  sorry

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
`hasNoFibreAffineLine_of_one_le_x1Genus`, and that is the sorry node
(`hasNonconstantAbelianMap_of_one_le_x1Genus` was that node until
2026-07-28 and is now PROVEN over it) — exactly the split `X0.lean`
makes between `x0Genus` and `hasNoFibreAffineLine_of_one_le_x0Genus`. -/
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
below; **whichever pair is proven first, the other should be derived and
not reproved**, since the classical proof of each is uniform in `G` and
specializing it to one group makes it no easier.

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

/-- **The Fricke involution `W_N` on a group between `Γ₁(N)` and `Γ₀(N)`**
(sorry leaf) — the ONE piece of modular input that carries the
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

What has to be built, none of which exists at this pin (checked by
`grep -rn "Fricke\|AtkinLehner\|atkinLehner" Fermat/ .lake/packages/mathlib/
~/cs/FLT/`, 2026-07-27: no hits): `W_N` as an element of `GL(2, ℝ)`, the
conjugation `W_N⁻¹ G W_N = G`, and the fact that slashing by a normalising
element preserves `CuspForm` — for the last the cusp condition is the only
real work, since `W_N γ` for `γ ∈ SL(2, ℤ)` is integral of determinant `N`
and must be put in Hermite normal form to see that zero-at-`∞` survives.

`WeightTwoEigenform.lean`'s `exists_frickeInvolution` is the
`G = Γ₀(N)` instance of this; see the subsection docstring. -/
theorem exists_frickeInvolutionOn (N : ℕ) (hN : N ≠ 0) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (h0 : G ≤ Gamma0GL N) (f : CuspForm G 2) :
    ∃ g : CuspForm G 2, ∀ y : ℝ, 0 < y →
      axisRestrictOn G N f (1 / y) = -((y ^ (2 : ℝ) : ℝ) : ℂ) * axisRestrictOn G N g y :=
  sorry

/-- **A cusp form decays faster than every power at `i∞`** (sorry leaf).

TRUE and elementary given the `q`-expansion, which is what `h1` supplies:
`Γ₁(N) ≤ G` puts `T = ![![1, 1], ![0, 1]]` in `G`, so `f` is `1`-periodic,
and `CuspForm`'s zero-at-`∞` condition then makes the expansion start at
`n = 1`; hence `f(i y/√N) = O(e^{-2πy/√N})`, which beats `y ^ r` for every
real `r`.  Stated for an arbitrary cusp form rather than for an eigenform
because the Fricke partner `g` above needs it too and is not known to be
an eigenform. -/
theorem isBigO_atTop_axisRestrictOn (N : ℕ) (G : Subgroup (GL (Fin 2) ℝ))
    (h1 : Gamma1GL N ≤ G) (f : CuspForm G 2) (r : ℝ) :
    axisRestrictOn G N f =O[atTop] fun y : ℝ => y ^ r :=
  sorry

/-- **`f` restricted to the imaginary axis is locally integrable on
`(0, ∞)`** (sorry leaf) — it is continuous there, `f` being holomorphic;
the only content is transporting continuity through the `ℍ`-coercion, and
no hypothesis on `G` is used. -/
theorem locallyIntegrableOn_axisRestrictOn (N : ℕ) (G : Subgroup (GL (Fin 2) ℝ))
    (f : CuspForm G 2) :
    LocallyIntegrableOn (axisRestrictOn G N f) (Set.Ioi 0) :=
  sorry

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

/-- **Hecke's bound `|aₙ| = O(n)`** (sorry leaf).

TRUE for every weight-two cusp form, by the contour-integral estimate
`aₙ = ∫₀¹ f(x + i/n) e^{-2πin(x+i/n)} dx` together with the fact that the
Petersson function `y |f(x+iy)|` of a cusp form is bounded on `ℍ` —
mathlib has `petersson` but not its boundedness.  `h1` is what makes that
bound available: `y|f|` is `G`-invariant and `G ⊇ Γ₁(N)` has finite index
in `SL(2, ℤ)`, so a bound on a fundamental domain is a bound everywhere.
Deligne's `|aₙ| ≤ d(n) √n` is *not* needed, which is why the half plane in
`IsLFunctionOf` is `Re s > 2` rather than `Re s > 3/2`. -/
theorem isBigO_atTop_coeffOn {N : ℕ} {G : Subgroup (GL (Fin 2) ℝ)} {χ : DirichletCharacter ℂ N}
    {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) :
    a =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 - 1 : ℝ) :=
  sorry

/-- The Dirichlet series of a weight-two cusp form converges absolutely on
`Re s > 2` (PROVEN, from `isBigO_atTop_coeffOn`). -/
theorem lSeriesSummable_of_isWeightTwoEigenformOn {N : ℕ} {G : Subgroup (GL (Fin 2) ℝ)}
    {χ : DirichletCharacter ℂ N} {f : CuspForm G 2} {a : ℕ → ℂ} (h1 : Gamma1GL N ≤ G)
    (hf : IsWeightTwoEigenformOn G N χ f a) {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable a s :=
  LSeriesSummable_of_isBigO_rpow hs (isBigO_atTop_coeffOn h1 hf)

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
  have hsummable : LSeriesSummable a s := lSeriesSummable_of_isWeightTwoEigenformOn h1 hf hs
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
this at `.gamma1`.  **The duplication is in the leaves only, and it is
removable in one direction**: the four `Γ₀` statements there and the four
`G`-generic statements here have the same classical proof, so whichever
pair lands first should discharge the other by citation.

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

**WHAT IS NOT PINNED, and it is the crux.**  `T` is an ARBITRARY family
of endomorphisms; nothing here says it is the family of genuine Hecke
correspondences.  That is why `isTorsion_factor_of_heckeIsotypic_gamma1`
below keeps the FULL analytic hypothesis rather than the single value
`L(form i, 1) ≠ 0` — see its docstring for the counterexample, which is
`X0.lean`'s and transfers unchanged. -/
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

/-- **EICHLER–SHIMURA for `Γ₁(N)`: the Hecke-isotypic decomposition
exists** (sorry node, new 2026-07-28) — the first of the two leaves
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
its flatness (`Modularity/AbelianSchemeIsogeny.lean`).  **So this leaf and
its `Γ₀` sibling are gated on the SAME missing theory** and should be
taken together by whoever builds it — the `Γ₁` case needs, additionally,
only the decomposition of `S₂(Γ₁(N))` by nebentypus, which is a statement
about the finite abelian group `(ℤ/N)ˣ` acting on a finite-dimensional
space. -/
theorem exists_heckeIsotypicDecomposition_gamma1 (N : ℕ)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : ModularLevelShape.IsCompactification .gamma1 N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) :
    Nonempty (IsHeckeIsotypicDecompositionGamma1 N h jac) :=
  sorry

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
statement is **FALSE** — `X0.lean`'s `N = 37` counterexample (swap the
eigensystems of `E_{37a}` and `E_{37b}`, which no field of the structure
can see) transfers verbatim, since it uses nothing about the level
structure.  With the full `hL` the statement is TRUE for any `T`
whatsoever, because `hL` already forces `J_1(N)(ℚ)` to be torsion and
`u_surj` bounds the rank of a factor: by Poincaré reducibility there is
`v : A i ⟶ J` with `u i ∘ v = [m]` for some `m ≠ 0`, so `m • x` is torsion
for every `x ∈ A i(ℚ)`, hence so is `x`.  As on the `Γ₀` side, the honest
reading is that **this leaf is stated at the strength its hypotheses can
support, and becomes the sharp Kolyvagin–Logachev statement the moment `T`
is pinned**; sharpening it is a cut-level repair gated on the same missing
input, and it should be done rather than routed around.

`D.u_surj`, `D.isotypic`, `D.cover`, `D.equivariant` and `D.integral` are
all available to a prover and none is decoration. -/
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
  have hL' : ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1GL N) 2) (a : ℕ → ℂ),
      IsWeightTwoEigenformOn (Gamma1GL N) N χ f a →
      ∀ L : ℂ → ℂ, IsLFunctionOf a L → L 1 ≠ 0 := by
    intro χ f a hf L hLf
    obtain ⟨L₀, hL₀, hne⟩ := hL χ f a hf
    rw [isLFunctionOf_apply_eq hLf hL₀ 1]
    exact hne
  obtain ⟨D⟩ := exists_heckeIsotypicDecomposition_gamma1 N h jac
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

/-- **Hecke's Mellin transform at `s = 1` on `Γ₁(N)`:
`L(f, 1) = 2π ∫₀^∞ f(iy) dy`** (sorry leaf, NEW 2026-07-28) — the `Γ₁`
transposition of `X0.lean`'s **PROVEN**
`lFunction_apply_one_eq_two_pi_mul_cuspPeriod`.  LEVEL-FREE and
NEBENTYPUS-FREE: it is the whole of the *analysis* under
`lFunction_apply_one_ne_zero_x1TwentyFive` below, and `25` does not
appear in it.

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

### WHY THIS IS A LEAF AND NOT AN APPLICATION OF THE `Γ₀` THEOREM

`X0.lean`'s theorem is proven, and **its proof uses nothing about
`Γ₀(N)` beyond the TYPE of `f`.**  All of it — `axisPoint`,
`axisRestrict`, `cuspFEPair`, `hasSum_axisRestrict`,
`mellin_axisRestrict`, `isStrongFEPair_cuspFEPair` and the identity-
theorem assembly itself — is written against `CuspForm (Gamma0GL N) 2`
purely because that is the type it was first needed at.  So the two
statements cannot be shared TODAY (a `Γ₁(N)` cusp form is not a `Γ₀(N)`
cusp form unless `χ = 1`), and they will be ONE statement the moment the
machinery upstream is group-generic.

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
  sorry

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
and none of that exists at this pin: `grep -rn "newform\|Newform\|
oldform\|degeneracy\|eigenbasis" Fermat/ .lake/packages/mathlib/
~/cs/FLT/` is the check that would refute it, and it returned nothing on
2026-07-28.  This is the same missing theory that `X0.lean` names as "the
axis not searched" on its own period leaf, and closing it closes both.

**The axis searched, so the next reader need not redo it.**  A cut on the
character `χ` (eight cases) is mechanically available and is *not* a
decomposition: it moves no theory and multiplies the frontier by eight.
A cut that isolates the Fricke sign `ε` is a real decomposition but is
worth nothing on its own, because the sum above still needs the certified
`aₙ`; it becomes worth writing at the moment the basis does. -/
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

/-- **The genus formula, fibrewise, at `Γ₁`: `genus X_1(N) ≥ 1` puts no
rational curve in any fibre of `X_1(N)`** (sorry leaf, 2026-07-28) — the
`Γ₁` transposition of `X0.lean`'s `hasNoFibreAffineLine_of_one_le_x0Genus`,
and after the cut below the ONLY place where the computed number
`x1Genus N` meets the scheme `X`.

`HasNoFibreAffineLine` itself is `X0.lean`'s, REUSED VERBATIM — it is
level-free, and the whole point of the seam is that only this leaf, which
mentions `N`, differs between the two layers.

TRUE.  `hmodel` makes every fibre of `strX` a smooth proper
geometrically connected curve which is the `X_1(N)` of its residue
field, and `hg` together with `hN` says its genus is `≥ 1` (the classical
formula, Diamond–Shurman Thm 3.1.1).  A nonconstant `K`-morphism
`𝔸¹_K ⟶ X` over a `K`-point of `S` lands in one such fibre `X_K`; it
extends to `ℙ¹_K ⟶ X_K` because `𝔸¹_K` is a dense open of the smooth
proper curve `ℙ¹_K` and `X_K` is proper, and a nonconstant morphism of
smooth proper curves is finite surjective, so Riemann–Hurwitz gives
`genus X_K ≤ genus ℙ¹_K = 0` — contradicting `hg`.  Hence every such
morphism is constant, which is `HasNoFibreAffineLine`.

**THE EXTENSION STEP IS ALREADY PROVEN AND IN THIS FILE'S CONE** — do not
rebuild it.  `exists_unique_extension_of_isSmoothProperCurve`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, reaching here
through `X0.lean`, proven outright from `Mathlib` by the valuative
criterion) extends a morphism from a dense open of a smooth proper curve
over a field into any PROPER target, which is exactly "`𝔸¹_K ⟶ X_K`
extends to `ℙ¹_K ⟶ X_K`" once `ℙ¹_K` is written down.  What is still
missing is therefore only `ℙ¹` itself and the genus, not the extension.

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

IRREDUCIBLE at this pin along the axis searched — the identification of
the arithmetic `x1Genus N` with an invariant of the scheme `X`, which
needs a genus of a scheme, `h¹(𝒪_X)`, or Riemann–Hurwitz for the
degree-`μ₁(N)` map to the `j`-line, none of which exists in `Mathlib`, in
`~/cs/FLT`, or here.  **The check that would refute this verdict**: a
genus, an `h¹`, or a Riemann–Hurwitz statement appearing in any of the
three trees — `grep -rn "arithmeticGenus\|Riemann.*Roch\|Riemann.*Hurwitz"
Fermat/ .lake/packages/mathlib/ ~/cs/FLT/`.

**Do NOT decompose this along the MODULAR axis** (`dim S_2(Γ_1(N)) =
x1Genus N` plus Eichler–Shimura).  That was tried on the `Γ₀` side and
RETIRED: it is a second, parallel copy of the genus formula with a theory
build attached, and the copy it duplicates is this leaf.  See the note on
`hasNonconstantAbelianMap_of_one_le_x1Genus` below. -/
theorem hasNoFibreAffineLine_of_one_le_x1Genus {N : ℕ} (hN : 5 ≤ N) (hg : 1 ≤ x1Genus N)
    {X Y S : Scheme.{0}} {strX : X ⟶ S} {strY : Y ⟶ S} {jY : Y ⟶ X}
    (hmodel : IsX1Compactification N strX strY jY) :
    HasNoFibreAffineLine strX :=
  sorry

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
`x0Genus 0 = 1` by hand. -/
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
    exact ⟨X, strX, _, _, fun hc =>
      hne (jac.injective_aj_of_mono
        (mono_ajHom_of_hasNoFibreAffineLine h.isProper h.smooth h.connected jac
          (hasNoFibreAffineLine_of_one_le_x1Genus hN hg h)) strX hc)⟩

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
| `exists_frickeInvolutionOn` | the Fricke involution `W_N` | no | here |
| `isBigO_atTop_axisRestrictOn` | cusp-form decay at `i∞` | no | here |
| `locallyIntegrableOn_axisRestrictOn` | continuity on the axis | no | here |
| `isBigO_atTop_coeffOn` | Hecke's coefficient bound | no | here |
| `isTorsion_jacobian_of_lFunction_ne_zero_gamma1` | Eichler–Shimura + Kolyvagin, `Γ₁` half | no | here, **PROVEN** |
| `exists_heckeIsotypicDecomposition_gamma1` | Eichler–Shimura | no | here |
| `isTorsion_factor_of_heckeIsotypic_gamma1` | Kolyvagin–Logachev | no | here |
| `lFunction_apply_one_ne_zero_x1TwentyFive` | `L`-value numerics | **yes** | here |
| `injective_aj_of_not_isIso_jacobian` | Riemann–Roch | no | `X0.lean`, REUSED |
| `hasNoFibreAffineLine_of_one_le_x1Genus` | genus formula, fibrewise | **yes** | here |
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

**AMENDED 2026-07-28.**  The genus row was
`hasNonconstantAbelianMap_of_one_le_x1Genus` until that node was PROVEN;
what is open there now is its fibrewise half
`hasNoFibreAffineLine_of_one_le_x1Genus`.  The third reuse —
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
