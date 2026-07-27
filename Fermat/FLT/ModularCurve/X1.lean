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

* **`hasRankZeroJacobian_x1TwentyFive`** (stated in `MazurTorsion.lean`,
  over `X0.lean`'s `HasRankZeroJacobian`) is the deep input, and it is
  where essentially all of the level's weight sits.
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
| `exists_isCoarseModuliY1_isSmoothCurve` | `Y_1(N)` is a smooth geometrically connected curve (Katz–Mazur 4.7/8.2) | any `K`, `char K ∤ N` |
| `nonempty_cuspLocusX1` | the cusp locus of `X_1(N)` (Deligne–Rapoport VI.6) | `ℚ` |
| `exists_gamma1Datum_of_relPoint` | fineness at `N ≥ 4` / Lang | `𝔽_ℓ` |
| `isEmpty_gamma1Datum_finiteField` | `#E(𝔽_ℓ) ≤ 2ℓ + 1` — NO modular curves | `𝔽_ℓ` |
| `card_cusp_x1_finiteField` | the cusp count on the special fibre | `𝔽_ℓ` |
| `exists_injective_reduction_of_rankZeroJacobian` | Abel–Jacobi, Mordell–Weil, formal groups | `ℚ → 𝔽_ℓ` |
| `nonempty_gamma1Datum_of_ratPoint` | Galois descent of a rational point to a section | `ℚ` |
| `hasRankZeroJacobian_x1TwentyFive` | Kolyvagin–Logachev — the DEEP one | `ℚ` |

Everything else in this file — the compactification geometry, the
finiteness of `X_1(N)(𝔽_ℓ)`, the passage from the cusp locus to indexed
rational cusps, and all three assemblies — is now sorry-free. -/

/-- **SOME coarse moduli space of the `Γ₁(N)`-problem is a geometrically
connected smooth curve over `K`, for `4 ≤ N` and `char K ∤ N`** (sorry
leaf — and the ONLY modular input to the existence of `X_1(N)`, over
BOTH base fields this file uses).

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

AXIS SEARCHED: the BASE-FIELD axis (taken — one leaf for `ℚ` and `𝔽_ℓ`
at once) and the COMPACTIFICATION axis (taken — the whole
Nagata/normalization half is now
`AlgebraicGeometry.exists_isSmoothCompactification` and is not modular).
NOT searched: the GIT axis, i.e. the `Γ₁` analogue of
`exists_gamma0AffineModel`, which exhibits the Katz–Mazur affine model as
`Spec` of a ring of invariants and reads `smooth`/`connected` off it.
That is how `X0.lean` cut the corresponding leaf one step further, and it
is what a successor should try next; it needs a `Gamma1Atlas`/GIT
presentation that does not exist here yet.  This note is refuted by
exhibiting a `Γ₁(N)`-affine model, or any construction of `Y_1(N)`, in
`Fermat/`, `.lake/packages/mathlib/` or `~/cs/FLT/`; as of 2026-07-27
`grep` over all three finds none. -/
theorem exists_isCoarseModuliY1_isSmoothCurve (N : ℕ) (_hN : 4 ≤ N) (K : Type) [Field K]
    (_hchar : ¬ ringChar K ∣ N) :
    ∃ (Y : Scheme.{0}) (strY : Y ⟶ Spec (CommRingCat.of K)) (_hc : IsCoarseModuliY1 N strY),
      IsIntegral Y ∧ QuasiCompact strY ∧ IsSeparated strY ∧
        SmoothOfRelativeDimension 1 strY ∧ GeometricallyConnected strY :=
  sorry

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
* `AlgebraicGeometry.exists_isSmoothCompactification` and
  `AlgebraicGeometry.geometricallyConnected_of_isSmoothCompactification`
  supply the compactification itself, from
  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.

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
  obtain ⟨Y, strY, hc, hint, hqc, hsep, hsmd, hconn⟩ :=
    exists_isCoarseModuliY1_isSmoothCurve N hN K hchar
  haveI := hint; haveI := hqc; haveI := hsep; haveI := hsmd; haveI := hconn
  obtain ⟨X, strX, jY, hX⟩ := exists_isSmoothCompactification (K := K) strY
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

/-- **The cusp locus of `X_1(N)` exists** (sorry leaf — Deligne–Rapoport,
and all that is left of `exists_rationalCuspsX1`).

TRUE and classical (Ogg 1973; Deligne–Rapoport VI.6; Diamond–Shurman
§3.8 for the cusp count and §9.3 for the rationality): the cusps of
`X_1(N)` over `ℚ̄` are `Γ_1(N)\ℙ¹(ℚ)`, of which there are
`½ Σ_{d ∣ N} φ(d)φ(N/d)` for `N ≥ 5` (`28` at `N = 25`); they fall into
Galois orbits, and the `φ(N)/2` cusps of one distinguished orbit are
individually `ℚ`-rational, the Galois action on them being trivial.

WHAT REMAINS, precisely: the identification of `X ∖ Y` with the cuspidal
part of the Deligne–Rapoport model — i.e. the uniformisation
`X_1(N)(ℂ) ≅ Γ_1(N)∖ℍ*` together with its `ℚ`-structure.
`IsX1Compactification` supplies only that the complement is finite, so
nothing weaker than that identification can produce a single cusp: the
structure's fields do not by themselves forbid `jY` from being an
isomorphism with no cusps at all, and that is excluded only because
`coarse` pins `Y` as the affine curve `Y_1(N)`, which is moduli input
rather than scheme-theoretic bookkeeping.

**This leaf is the `Γ₁` sibling of `X0.lean`'s `nonempty_cuspLocus`**,
field for field, and both are the same theorem of Deligne–Rapoport with
different level structure.  A successor building the uniformisation
should expect to close both.

`hN` is NOT carried, unlike on the `Γ₀` side.  `numRationalCuspsX1 N =
φ(N)/2` is already `0` at `N ∈ {0, 1, 2}`, so `infty` is vacuous there
and no degenerate-level case has to be split off; the remaining fields
are a statement about `X ∖ Y` that is meaningful at every `N`.

AXES SEARCHED, each with the check that would refute it.

1. *The count* — weakening to a lower bound.  Already done upstream:
   `numRationalCuspsX1` is a lower bound by construction and this
   structure asks only for `φ(N)/2` rational cusps, not for all of them.
   It does not help — the difficulty is producing cusps, not bounding
   them.
2. *The index set* — `Fin (φ(N)/2)` against `(ℤ/N)ˣ/±1`.  Exhausted: the
   two are interderivable and moving the index around cannot make either
   side smaller.  `Fin` is taken so that no consumer inherits a
   `Nat.card ((ZMod N)ˣ ⧸ ±1) = φ(N)/2` obligation.
3. *The `j`-map dictionary* — characterise a cusp as a pole of an
   extended `j`-map.  DEAD, by `X0.lean`'s axis-3 argument verbatim: such
   an extension is definable from `IsCusp` itself, unconditionally, hence
   carries no information about it and has a model with no rational cusp
   at all.  Refuted by a `j`-map field that is not a function out of a
   point set — e.g. a section of the extended map over `∞`.
4. *An invariant-first cut* — peel the cusp invariant off as one leaf and
   "each value is attained" as another.  UNSAFE for the reason `X0.lean`
   records at its axis 4: quantified over an arbitrary invariant the
   existence half is FALSE by a constant junk witness.
5. *The RESIDUE-FIELD axis* — TAKEN; it is why this leaf carries the whole
   obstruction while `exists_rationalCuspsX1` is proven.  Refuted by
   exhibiting a model of `CuspLocus` over some `IsX1Compactification`
   whose cusps are not those of `X_1(N)`; `cover` is the field that is
   supposed to forbid it. -/
theorem nonempty_cuspLocusX1 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY) :
    Nonempty h.CuspLocus :=
  sorry

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

/-- **An `𝔽_ℓ`-point of the coarse space `Y_1(N)_{𝔽_ℓ}` comes from an
actual `Γ₁(N)`-datum over `𝔽_ℓ`, for `N ≥ 4`** (sorry leaf — the
fineness/Lang half of the `𝔽_ℓ` point count).

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
whole content of the coarse/fine distinction. -/
theorem exists_gamma1Datum_of_relPoint (N ℓ : ℕ) (_hN : 4 ≤ N) {Y : Scheme.{0}}
    {strY : Y ⟶ SpecF ℓ} (_hc : IsCoarseModuliY1 N strY)
    (_y : RelPoint strY (𝟙 (SpecF ℓ))) :
    Nonempty (Gamma1Datum N (SpecF ℓ)) :=
  sorry

/-- **There is no `Γ₁(N)`-datum over `𝔽_ℓ` once `N` exceeds the crude
point bound `2ℓ + 1`** (sorry leaf — the elementary arithmetic half of
the `𝔽_ℓ` point count, and the one that needs NO modular curves).

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

WHAT REMAINS is not the arithmetic but the passage from the scheme-level
datum to a Weierstrass model: `Gamma1Datum N (SpecF ℓ)` presents `E` as
an abelian scheme of relative dimension one over `Spec 𝔽_ℓ` with a
section, and a bound on its `𝔽_ℓ`-points needs that presented as a plane
cubic.  That is the `Γ₁`-side use of the converse of
`exists_ellipticScheme_of_weierstrass` (`X0.lean`), which goes the other
way; the direction needed here does not exist in this tree.

Note the statement is about `Gamma1Datum` alone — no compactification, no
coarse space, no cusp.  That is deliberate: it is the half a successor
can attack with elliptic-curve theory and nothing else. -/
theorem isEmpty_gamma1Datum_finiteField (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hN : 2 * ℓ + 1 < N) :
    IsEmpty (Gamma1Datum N (SpecF ℓ)) :=
  sorry

/-- **`Y_1(N)` has no `𝔽_ℓ`-point once `2ℓ + 1 < N`** (PROVEN 2026-07-27,
by joining the two halves above).

`X_1(N)` has no non-cuspidal `𝔽_ℓ`-point: a rational point of the coarse
space gives a datum (`exists_gamma1Datum_of_relPoint`), and there is no
datum (`isEmpty_gamma1Datum_finiteField`).  The join is trivial because
the two halves were stated to meet at `Gamma1Datum N (SpecF ℓ)`. -/
theorem isEmpty_relPoint_y1_finiteField (N ℓ : ℕ) (hN4 : 4 ≤ N) (hℓ : ℓ.Prime)
    (hN : 2 * ℓ + 1 < N)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    IsEmpty (RelPoint strY (𝟙 (SpecF ℓ))) :=
  ⟨fun y => (isEmpty_gamma1Datum_finiteField N ℓ hℓ hN).elim
    (exists_gamma1Datum_of_relPoint N ℓ hN4 h.coarse y).some⟩

/-- **The cusps of `X_1(N)` over `𝔽_ℓ` number exactly `m`, at the witness
rows** (sorry leaf — the ONE genuinely modular half of the `(25, 3, 10)`
row).

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
subtype is an isomorphism invariant, so the count does not depend on
which model is supplied; non-vacuity is supplied by
`exists_x1Compactification_finiteField`.

**Where the level-`25` weight really sits.**  This leaf and
`nonempty_cuspLocusX1` are both Deligne–Rapoport cusp theory, at the two
bases; neither is Eichler–Shimura.  `X_1(25)` has genus `12`, so the
Eichler–Shimura count `ℓ + 1 − Tr(T_ℓ ∣ S_2(Γ_1(25)))` looks forbidding,
but the answer `10` is exactly `φ(25)/2 = numRationalCuspsX1 25`, so no
Hecke operator is needed anywhere on this route.  Contrast
`X0.lean`'s `card_relPoint_x0_finiteField`, whose counts genuinely ARE
Eichler–Shimura and which is blocked on a module cycle through
`Modularity/Interface.lean`; this leaf inherits none of that. -/
theorem card_cusp_x1_finiteField (N ℓ m : ℕ) (_htable : (N, ℓ, m) ∈ x1WitnessTable)
    {X Y : Scheme.{0}} {strX : X ⟶ SpecF ℓ} {strY : Y ⟶ SpecF ℓ} {jY : Y ⟶ X}
    (h : IsX1Compactification N strX strY jY) :
    Nat.card {x : RelPoint strX (𝟙 (SpecF ℓ)) // h.IsCusp x} = m :=
  sorry

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
  obtain ⟨hN4, hℓ, -, hNℓ⟩ := x1WitnessTable_spec htable
  have hempty : IsEmpty (RelPoint strY (𝟙 (SpecF ℓ))) :=
    isEmpty_relPoint_y1_finiteField N ℓ hN4 hℓ hNℓ h
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
  — half 1, now two OPEN leaves, neither of which mentions a modular
  curve;
* `card_cusp_x1_finiteField` — half 2, the cusp count on the special
  fibre.  STILL OPEN, and the only one of the four that is
  Deligne–Rapoport.

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

/-- **The rank-`0` reduction INJECTION, `X_1(N)(ℚ) ↪ X_1(N)(𝔽_ℓ)`** (sorry
node — this is the criterion).

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
mention it.  So a successor closing either one closes both. -/
theorem exists_injective_reduction_of_rankZeroJacobian {N : ℕ} {X Y : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX1Compactification N strX strY jY) (hJ : HasRankZeroJacobian strX)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓN : ¬ ℓ ∣ N)
    {X' Y' : Scheme.{0}} {strX' : X' ⟶ SpecF ℓ} {strY' : Y' ⟶ SpecF ℓ}
    {jY' : Y' ⟶ X'} (hX' : IsX1Compactification N strX' strY' jY') :
    ∃ red : RelPoint strX (𝟙 SpecQ) → RelPoint strX' (𝟙 (SpecF ℓ)),
      Function.Injective red :=
  sorry

/-- **A rational point of exact order `N` on an elliptic curve over `ℚ`
gives a `Γ₁(N)`-structure over `Spec ℚ`** (sorry node).

TRUE.  This is the `Γ₁` analogue of `nonempty_gamma0Datum_of_stable`, and
it is where the elliptic-curve side and the moduli side meet.

WHAT IT NEEDS, in dependency order.

1. `exists_ellipticScheme_of_weierstrass` — PROVEN in `X0.lean` (over
   the five leaves of `EllipticScheme.lean`) — gives an abelian scheme
   `f : A ⟶ Spec ℚ` of relative dimension `1` together with a
   Galois-equivariant `≃+` from `(E⁄ℚ̄).Point` to the geometric fibre.
2. **Galois descent of the point to a SECTION.**  `P` is `ℚ`-rational, so
   its image in the geometric fibre is fixed by `Γ_ℚ`; and for a scheme
   separated over `ℚ` the `ℚ`-points are the Galois-fixed `ℚ̄`-points, so
   the fixed geometric point is a section `Spec ℚ ⟶ A`.  This is the only
   genuinely missing step, and it is the exact analogue of the descent
   carried out for subgroup SCHEMES in
   `exists_cyclicSubgroupOfOrder_of_galoisStable` — which is PROVEN in
   `X0.lean`, over the `spanScheme` machinery there.  A successor should
   look there first: the same `exists_geomPt_factor_span` /
   `exists_specGal_factor_span` apparatus applies, and the section case
   is strictly easier than the subgroup case since no closure under the
   group law has to be transported.
3. Order transport.  `Affine.Point.map` along `ℚ → ℚ̄` is an injective
   additive map, so `addOrderOf P` is unchanged; and the `≃+` of step 1
   preserves it by `AddEquiv.addOrderOf_eq`.  Both are one-line facts
   once step 2 is available — see the corresponding `have hord` in
   `nonempty_gamma0Datum_of_stable`, which is exactly this argument.

`hN : N ≠ 0` is load-bearing, by the same propagation recorded in the
FALSITY AUDIT of `exists_cyclicSubgroupOfOrder_of_galoisStable`: at
`N = 0` a point of infinite order on a positive-rank curve satisfies
`hP`, while `PointOfExactOrder ab 0` demands a section of infinite order
on every geometric fibre — impossible on a proper fibre, where the group
of points is torsion in every relevant sense.  So the statement would be
FALSE without it.

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
    {N : ℕ} (hN : N ≠ 0) (P : E.toAffine.Point) (hP : addOrderOf P = N) :
    Nonempty (Gamma1Datum N SpecQ) :=
  sorry

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

/-! ### Level `25`, packaged for `FreyCurve/MazurTorsion.lean` -/

/-- **`rank J_1(25)(ℚ) = 0` and `genus X_1(25) ≥ 1`** (sorry node — the
DEEP input of level `25`, and the one place essentially all of the
level's weight sits).

TRUE.  `X_1(25)` has genus `12`; `J_1(25)` is `ℚ`-isogenous to
`A₄ × A₈`, and evaluating the `L`-function of each factor at `1` gives
`LRatio(A₄, 1) = 1/5041` and `LRatio(A₈, 1) = 1/10272025`, both NONZERO.
So `J_1(25)` has analytic rank `0`, hence Mordell–Weil rank `0` by
Kolyvagin–Logachev (or Kato), hence `J_1(25)(ℚ)` is finite.  Positivity of
the genus is classical and generous here — `12 ≥ 1`.

Both conjuncts are load-bearing in `HasRankZeroJacobian`, and its
docstring in `X0.lean` records why: without finiteness a positive-rank
Jacobian gives infinitely many rational points already in genus `1`, and
without injectivity of Abel–Jacobi a genus-`0` curve refutes the
criterion outright.

IRREDUCIBLE at this pin, and the deepest leaf of this file: it needs
`S_2(Γ_1(25))`, the Hecke algebra, `L`-functions of modular abelian
varieties and Gross–Zagier/Kolyvagin.  **It is the exact `Γ₁` sibling of
`X0.lean`'s `hasRankZeroJacobian_of_kenkuLevel`** — same four theories,
same shape, different level structure — so a successor building that
machinery should expect to close both, and `HasRankZeroJacobian` is
literally the same definition in both statements.

WHY THE BUDGET SITS HERE AND NOT IN THE POINT COUNT.  The level-`25`
docstring in `MazurTorsion.lean` presents `#X_1(25)(𝔽_3) = 10` alongside
this as if the two were comparable inputs.  They are not:  that count is
the cusp count `φ(25)/2` and its non-cuspidal half is the elementary
bound `#E(𝔽_3) ≤ 7 < 25` (see `exists_x1Compactification_mod_prime`),
whereas this leaf is Kolyvagin–Logachev.  Budget accordingly. -/
theorem hasRankZeroJacobian_x1TwentyFive {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (h : IsX1Compactification 25 strX strY jY) : HasRankZeroJacobian strX :=
  sorry

/-- **Mazur's counting datum for `X_1(25)`, with the schemes eliminated**
(PROVEN over the five leaves above).

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
