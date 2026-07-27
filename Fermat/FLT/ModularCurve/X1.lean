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

/-! ### The four leaves

These are the `Γ₁`-specific inputs.  Every one of them is TRUE and
classical; none of them is available at this pin, and the module
docstring records which are deep and which are not. -/

/-- **Existence of the compactified coarse moduli space `X_1(N)` over
`ℚ`** (sorry node).

TRUE and classical: `Y_1(N)` is a smooth affine curve over `ℚ` — for
`N ≥ 4` a FINE moduli space, since a pair `(E, P)` with `P` of order
`≥ 4` has no nontrivial automorphism — and every smooth curve over a
field has a unique smooth projective compactification; for `Y_1(N)` it is
the modular curve `X_1(N)` of Deligne–Rapoport, obtained directly as the
coarse space of the moduli problem of GENERALISED elliptic curves with
`Γ₁(N)`-structure, the added points being the cusps.

`hN : 4 ≤ N` rather than `0 < N`.  At `N ≤ 3` the pair `(E, P)` has extra
automorphisms and the coarse space is not fine, and — more to the point
here — at `N = 0` the problem is empty over a nonempty base, exactly as
`isEmpty_of_gamma0Datum_zero` records on the `Γ₀` side: a section of
infinite order on every geometric fibre cannot exist on a proper fibre.
Only `N = 25` is used, so the stronger hypothesis costs nothing.

IRREDUCIBLE at this pin, and for the same reason as
`exists_x0Compactification`: neither modular curves nor a
smooth-compactification theorem for curves exists anywhere in `Mathlib`,
in `~/cs/FLT`, or in this project.  Refuting check for that claim: a
`grep` over all three for `ModularCurve`, `coarse moduli`, or a
compactification theorem for smooth curves.

**This leaf is genuinely SHARED with `exists_x0Compactification`** up to
the level structure — the compactification half is identical, and only
the `coarse` field differs.  A successor building Deligne–Rapoport should
close both together rather than either alone. -/
theorem exists_x1Compactification (N : ℕ) (hN : 4 ≤ N) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecQ) (strY : Y ⟶ SpecQ) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) :=
  sorry

/-- **`X_1(N)` has at least `φ(N)/2` distinct `ℚ`-rational cusps** (sorry
node).

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
action; as of 2026-07-27 `grep` over all three finds neither. -/
theorem exists_rationalCuspsX1 (N : ℕ) {X Y : Scheme.{0}} {strX : X ⟶ SpecQ}
    {strY : Y ⟶ SpecQ} {jY : Y ⟶ X} (h : IsX1Compactification N strX strY jY) :
    ∃ cusp : Fin (numRationalCuspsX1 N) → RelPoint strX (𝟙 SpecQ),
      Function.Injective cusp ∧ ∀ i, h.IsCusp (cusp i) :=
  sorry

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

/-- **The reduction `X_1(N)_{𝔽_ℓ}` and its point count, at the witness
primes** (sorry node).

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

The two halves are not stated separately because half 1 alone is not
consumed by anything — stating it would be free-floating — and because
the join needs `X'(𝔽_3) = Y'(𝔽_3) ⊔ cusps`, which is a fact about this
structure rather than about either half.

IRREDUCIBLE at this pin only through half 2: neither the integral model
of `X_1(N)` nor its reduction exists here. -/
theorem exists_x1Compactification_mod_prime (N ℓ m : ℕ)
    (h : (N, ℓ, m) ∈ x1WitnessTable) :
    ∃ (X Y : Scheme.{0}) (strX : X ⟶ SpecF ℓ) (strY : Y ⟶ SpecF ℓ) (jY : Y ⟶ X),
      Nonempty (IsX1Compactification N strX strY jY) ∧
        Finite (RelPoint strX (𝟙 (SpecF ℓ))) ∧
        Nat.card (RelPoint strX (𝟙 (SpecF ℓ))) = m :=
  sorry

/-! ### Uniqueness of `X_1(N)` over `𝔽_ℓ`, and the reduction datum

The two subsections here are what turns the rank-`0` criterion below from
a single `sorry` into an assembly.  They mirror, declaration for
declaration, the chain that PROVES `card_le_of_rankZeroJacobian` in
`X0.lean`:

| `X0.lean` | here |
|---|---|
| `IsCoarseModuliY0.exists_inverse` (PROVEN) | `IsCoarseModuliY1.exists_inverse` (PROVEN) |
| `exists_inverse_of_isX0Compactification` (leaf) | `exists_inverse_of_smoothCompactification` (leaf, and it SUBSUMES the `Γ₀` one) |
| `nonempty_relPointEquiv_of_isX0Compactification` (PROVEN) | `nonempty_relPointEquiv_of_isX1Compactification` (PROVEN) |
| `exists_x0NeronDatum` + `exists_isX0Compactification_specialFibre` + `neronReduction_injective` | `exists_x1ReductionAt` (one leaf) |

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
determined by a dense open** (sorry leaf).

TRUE, and classical: two smooth proper geometrically connected curves
over a field containing a common dense open glue along it, the closure of
the graph in `X₁ ×_k X₂` being proper and birational over both, hence an
isomorphism.  This is what `IsX1Compactification`'s docstring means by
"`finite_compl` is what pins `X` as the genuine `X_1(N)`".

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

**NOT VACUOUS, despite every hypothesis being underscore-prefixed.**  The
underscores mean only that a `sorry` consumes nothing; every one of them
is load-bearing for the conclusion:

* drop properness of `strX₁` and take `X₁ = Y₁` an affine curve, `X₂` its
  smooth compactification — then `Y₁ ≅ Y₂` but `X₁ ≇ X₂`;
* drop smoothness and `X₂` may be any singular curve with the same
  function field, e.g. a nodal model, again not isomorphic to `X₁`;
* drop finiteness of the complements and `Y` need not be dense in `X`, so
  `X₁` may carry a whole extra component that `X₂` lacks;
* drop `_hu`/`_hv` and the isomorphism `Y₁ ≅ Y₂` is not over the base, so
  no `w` over the base can exist;
* the conclusion's last conjunct `jY₁ ≫ w = u ≫ jY₂` is what says `w`
  EXTENDS `u` rather than being some unrelated isomorphism, and it is
  what a consumer that cares about cusps needs.

`_hℓ` is carried because the argument wants a FIELD base: over a
non-normal or non-reduced base the closure-of-the-graph argument fails,
and stating the leaf there would risk a false statement for a generality
nothing consumes.  Refuting check for the claim that this is absent from
the pin: a declaration in `Mathlib`, `~/cs/FLT` or `Fermat/` producing an
isomorphism of smooth proper curves from an isomorphism of dense opens;
as of 2026-07-27 `grep` over all three finds none. -/
theorem exists_inverse_of_smoothCompactification {ℓ : ℕ} (_hℓ : ℓ.Prime)
    {X₁ Y₁ X₂ Y₂ : Scheme.{0}} {strX₁ : X₁ ⟶ SpecF ℓ} {strY₁ : Y₁ ⟶ SpecF ℓ}
    {jY₁ : Y₁ ⟶ X₁} {strX₂ : X₂ ⟶ SpecF ℓ} {strY₂ : Y₂ ⟶ SpecF ℓ} {jY₂ : Y₂ ⟶ X₂}
    (_hc₁ : jY₁ ≫ strX₁ = strY₁) (_hc₂ : jY₂ ≫ strX₂ = strY₂)
    (_ho₁ : IsOpenImmersion jY₁) (_ho₂ : IsOpenImmersion jY₂)
    (_hp₁ : IsProper strX₁) (_hp₂ : IsProper strX₂)
    (_hs₁ : SmoothOfRelativeDimension 1 strX₁) (_hs₂ : SmoothOfRelativeDimension 1 strX₂)
    (_hg₁ : GeometricallyConnected strX₁) (_hg₂ : GeometricallyConnected strX₂)
    (_hf₁ : (Set.range jY₁.base)ᶜ.Finite) (_hf₂ : (Set.range jY₂.base)ᶜ.Finite)
    {u : Y₁ ⟶ Y₂} {v : Y₂ ⟶ Y₁} (_hu : u ≫ strY₂ = strY₁) (_hv : v ≫ strY₁ = strY₂)
    (_huv : u ≫ v = 𝟙 Y₁) (_hvu : v ≫ u = 𝟙 Y₂) :
    ∃ (w : X₁ ⟶ X₂) (w' : X₂ ⟶ X₁),
      w ≫ strX₂ = strX₁ ∧ w' ≫ strX₁ = strX₂ ∧
      w ≫ w' = 𝟙 X₁ ∧ w' ≫ w = 𝟙 X₂ ∧ jY₁ ≫ w = u ≫ jY₂ :=
  sorry

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

/-- **The Néron reduction datum for `X_1(N)` at a good odd prime** (sorry
leaf — this is where the arithmetic of the rank-`0` criterion sits).

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

They are bundled into ONE leaf here rather than mirrored one-for-one
because only the first is `Γ₁`-specific: `IsX0NeronDatum`'s single
moduli-carrying field is `model : IsX0Compactification N xstr ystr jZ`,
and everything else in that 200-line structure — the base, the four fibre
identifications, their naturality, additivity, compatibility with
Abel–Jacobi, the Néron mapping property, the valuative criterion — is
moduli-free and would be copied character for character.  A successor
should therefore NOT re-mirror `IsX0NeronDatum`; the honest work is
either to prove Deligne–Rapoport for `Γ₁` and reuse the `Γ₀` machinery,
or (better) to hoist that structure to a moduli-free form in `X0.lean`
and instantiate it twice.

**Every hypothesis is load-bearing**, and each fails the conclusion on
its own — the underscore prefixes record only that a `sorry` consumes
nothing:

* `_hfin` is rank `0`.  Without it `J_1(N)(ℚ)` is infinite, hence not
  torsion, and `redJ_inj` is false: the kernel of reduction is exactly
  where the non-torsion points go.
* `_hℓ2` is the formal-group hypothesis.  At `ℓ = 2` the kernel of
  reduction can contain `2`-torsion and `redJ_inj` fails.
* `_hℓN` is good reduction.  At `ℓ ∣ N` the special fibre is not a smooth
  curve, so no `IsX1Compactification` over `𝔽_ℓ` is produced.
* `_hX` is what makes the statement about `X_1(N)` rather than an
  arbitrary curve, and it is what supplies the moduli input to the
  integral model.
* `jac` is EXPLICIT because the conclusion mentions it: without it
  `IsX0ReductionAt` has nothing to be a reduction *of*, and `red_aj`
  would be unstateable.

**Non-vacuity.**  `IsX0ReductionAt jac jac'` carries `redJ_inj` and
`red_aj`, and those two together already force
`#(jac.aj '' X_1(N)(ℚ)) ≤ #J_1(N)(𝔽_ℓ)`; no junk witness discharges it,
because `jac'` pins `J'` as the genuine Jacobian of the produced curve by
its own initiality field.  That implication is not a remark: it is the
proof of `exists_injective_reduction_of_rankZeroJacobian` below, so the
compiler certifies that this leaf is at least as hard as the criterion it
stands in for. -/
theorem exists_x1ReductionAt (N ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓ2 : ℓ ≠ 2) (_hℓN : ¬ ℓ ∣ N)
    {X Y J : Scheme.{0}} {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (_hX : IsX1Compactification N strX strY jY) (jac : IsJacobianOf strX ab o)
    (_hfin : Finite (RelPoint jstr (𝟙 SpecQ))) :
    ∃ (X' Y' J' : Scheme.{0}) (strX' : X' ⟶ SpecF ℓ) (strY' : Y' ⟶ SpecF ℓ)
      (jY' : Y' ⟶ X') (jstr' : J' ⟶ SpecF ℓ) (ab' : AbelianSchemeStruct jstr')
      (o' : RelPoint strX' (𝟙 (SpecF ℓ))) (jac' : IsJacobianOf strX' ab' o'),
      Nonempty (IsX1Compactification N strX' strY' jY') ∧
        Nonempty (IsX0ReductionAt jac jac') :=
  sorry

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

/-- **A Galois-invariant geometric point of an abelian scheme over `ℚ` is
a section** (sorry leaf).

TRUE, and it is Galois descent for points in its most basic form: for any
scheme `A` over a field `k` with separable closure `k^s`, the natural map
`A(k) → A(k^s)^{Γ_k}` is a bijection.  A `Γ_ℚ`-fixed `ℚ̄`-point has image
a closed point of `A` whose residue field is fixed by `Γ_ℚ`, hence equal
to `ℚ`, so the point is already defined over `ℚ`; and `A` is separated
over `ℚ` (it is proper, by `ab.proper`), so the descended morphism is
unique.

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

The `spanScheme` apparatus is nevertheless the right place to look for a
proof.  `ratPoint_liesIn_spanScheme` shows the shape the argument takes
in this development — a comparison of KERNEL IDEAL SHEAVES, closed by
`app_injective_specAlgClos` (every `app` of `Spec ℚ̄ ⟶ Spec ℚ` is
injective) — and `exists_specGal_factor_span` is where the Galois action
is turned into an equality of kernels.  A successor should build the
descent as: the scheme-theoretic image of `y` is a closed subscheme of
`A` finite over `ℚ`, Galois-invariance makes its kernel ideal sheaf
`Γ_ℚ`-stable, hence defined over `ℚ` with residue field `ℚ`, and the
factorisation of `y` through it descends.

**`_hinv` is INVARIANCE, not stability, and the difference is the whole
`Γ₀`/`Γ₁` distinction.**  `exists_cyclicSubgroupOfOrder_of_galoisStable`
asks only `galSMul σ y ∈ zmultiples y`, which is what a rational
SUBGROUP needs; asking only that here would make the statement FALSE —
take `y` a `ℚ̄`-point of order `3` on a curve with no rational `3`-torsion
whose subgroup `⟨y⟩` is `Γ_ℚ`-stable (`X_0(3)` has rational points, so
such curves exist), and no section of `A` over `ℚ` restricts to it.

Note that no hypothesis on the ORDER of `y` appears: descent of a point
has nothing to do with torsion, and the order is transported separately
by `exists_pointOfExactOrder_of_geomPt` below.  Nor is `ab` used for its
group law — only `A` and `f` matter — but it is taken because the
consumer has it and because properness of `f`, which the argument needs,
is one of its fields. -/
theorem exists_section_of_galoisInvariant {A : Scheme.{0}} {f : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct f) (y : GeomFibrePt f (𝟙 SpecQ))
    (_hinv : ∀ σ : Field.absoluteGaloisGroup ℚ, ab.galSMul (𝟙 SpecQ) σ y = y) :
    ∃ (sec : SpecQ ⟶ A) (hsec : sec ≫ f = 𝟙 SpecQ),
      RelPoint.ofSection sec hsec (specAlgClos ℚ ≫ 𝟙 SpecQ) = y :=
  sorry

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
(PROVEN over the leaves above — six of them as of 2026-07-27:
`exists_x1Compactification`, `exists_rationalCuspsX1`,
`exists_x1Compactification_mod_prime`, `hasRankZeroJacobian_x1TwentyFive`,
`exists_inverse_of_smoothCompactification` and `exists_x1ReductionAt`,
plus `exists_section_of_galoisInvariant` through the moduli dictionary).

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
