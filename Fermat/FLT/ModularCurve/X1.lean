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
