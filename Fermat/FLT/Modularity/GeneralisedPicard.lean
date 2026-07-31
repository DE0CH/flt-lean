/-
Modularity/GeneralisedPicard.lean — own work for the Fermat project (not
vendored from the FLT project).

# The GENERALISED relative Picard functor `PG(X, Z)` of Moret–Bailly §3.4

`Groupes de Picard et problèmes de Skolem II`, Ann. Sci. ÉNS (4) **22**
(1989), 181–194, §3.4, defines

    PG(X̄, Z)(T)  =  { (ℒ, α) : ℒ invertible on X̄_T, α : ℒ|_{Z_T} ≅ 𝒪_{Z_T} } / ≅

— invertible sheaves on the curve RIGIDIFIED along the boundary `Z` — and
exhibits it as an extension

    1 → 𝔾_{m,B} → (π_Z)_* 𝔾_{m,Z} → PG(X̄,Z) → Pic_{X̄/B} → 1     (3.4.2)

of the ordinary relative Picard functor by a smooth affine commutative
`B`-group scheme.  It is the group in which the whole of §3.5–§3.10 takes
place: `φ_d : X̄^(d) → PG_d` of §3.5, the open sets `W_v^d ⊆ P_d(K_v)` of
§3.7, and the quasi-compactness argument of §3.9–§3.10 that produces the
pair `(ℒ, α)` §3.8 needs.

## Why this module exists, and what it is NOT

`Fermat/FLT/ModularCurve/RelativePicard.lean` already has the ORDINARY
relative Picard functor `Fermat.IsRelPicOf` (`T ↦ Pic(X_T)/Pic(T)`, the
naive quotient) together with `Fermat.IsRelPicZeroOf`, and
`Fermat.exists_relPicZero` is PROVEN over two named BLR leaves.  That is
§3.4's RIGHT-HAND term.  What was missing — and what the
`exists_skolemBallDatum_of_projectiveCompactification` docstring in
`Modularity/MoretBailly.lean` names as "the trivialisation layer of §3.4"
— is the rigidified functor itself.  This module supplies it, with the
same functor-of-points presentation `RelativePicard.lean` uses, so that
the two are directly comparable:

* `Fermat.TrivialisedSheaf strX ι g` — the DATUM `(ℒ, α)` at a test
  object, `α` being an isomorphism and not merely its existence;
* `Fermat.TrivialisedSheafEquiv` — isomorphism of such data;
* `Fermat.pullbackTrivialisedSheaf` — base change of a datum along
  `h : T' ⟶ T`, PROVEN to exist (it is the only construction in this file
  that has content, and it is where `boundaryBaseChangeMap_comm` is spent);
* `Fermat.IsGenRelPicOf strX ι pstr` — the predicate "`pstr : P ⟶ S`
  represents `PG(X, Z)`", modelled field-for-field on
  `Fermat.IsRelPicOf`;
* `Fermat.exists_genRelPic` — the LEAF: §3.4's representability.

## The one design decision, and why it differs from `IsRelPicOf`

`IsRelPicOf` compares sheaves through `RelPicEquiv`, i.e. MODULO the
pullback of an invertible sheaf from the base; without that quotient its
`inj` field would be false at any test object with `Pic T ≠ 0`.
`IsGenRelPicOf` compares PAIRS through plain isomorphism, with NO
quotient, and that is not an oversight — it is the whole point of the
rigidification.  Two readings of §3.4, and the reason the second is the
right one:

* the quotient exists in `IsRelPicOf` because an invertible sheaf on
  `X_T` has automorphism group `Γ(X_T, 𝒪^×) = Γ(T, 𝒪^×)` (when
  `f_*𝒪 = 𝒪` universally), which is exactly `Pic`'s failure to be a
  sheaf at the level of objects;
* a PAIR `(ℒ, α)` has NO nontrivial automorphisms as soon as
  `Γ(T, 𝒪^×) → Γ(Z_T, 𝒪^×)` is injective, which holds when `Z → B` is
  faithfully flat — MB's normalisation 3.1.2(iii), and a hypothesis of
  `exists_genRelPic` below.  A presheaf of sets with no automorphisms in
  its objects and effective descent (line bundles and their
  trivialisations both descend fppf) is already a sheaf, so the NAIVE
  functor written here is the right one and needs no sheafification.

That argument is what makes `surj` below a true field rather than a
false one, and it is the check that `exists_genRelPic` is not a leaf
that will turn out to be FALSE AS STATED.  It is recorded here because
the corresponding argument for `IsRelPicOf` (BLR 8.1/4, needing a
section) is recorded there, and the two are genuinely different.

## What is deliberately NOT here

Not the exact sequence 3.4.2 as a statement.  `PG → Pic_{X̄/B}` (forget
`α`) and `(π_Z)_*𝔾_m → PG` (`λ ↦ (𝒪, λ)`) are both writable over what is
in this file, but neither has a consumer yet, and this project forbids
free-floating declarations; the sequence is what a prover of
`exists_genRelPic` will USE, not something its statement needs.  The
same goes for the degree decomposition `PG = ⨿_d PG_d` of §3.4 — `deg`
does not exist at this pin (see the survey in the
`exists_skolemBallDatum_of_projectiveCompactification` docstring), and
`PG_d` is not needed to state representability.
-/
module

public import Fermat.FLT.ModularCurve.RelativePicard
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Fermat

/-! ### The boundary, base-changed -/

/-- **`Z ×_S T ⟶ X ×_S T`**, the base change along `g : T ⟶ S` of a
subscheme inclusion `ι : Z ⟶ X` of `S`-schemes.

Written for an arbitrary `ι`, not only a closed immersion: nothing below
uses that `ι` is one, and the extra generality costs nothing.  The
structure morphism of `Z` is not a separate argument — it is `ι ≫ strX`,
which is what makes `curveBaseChange (ι ≫ strX) g` the correct `Z_T`. -/
noncomputable def boundaryBaseChangeMap {X Z S T : Scheme.{u}} (strX : X ⟶ S) (ι : Z ⟶ X)
    (g : T ⟶ S) : curveBaseChange (ι ≫ strX) g ⟶ curveBaseChange strX g :=
  pullback.lift (pullback.fst (ι ≫ strX) g ≫ ι) (pullback.snd (ι ≫ strX) g)
    (by rw [Category.assoc]; exact pullback.condition)

/-- **Base change of the boundary commutes with base change of the test
object** (PROVEN): the square

    Z_{T'} ⟶ X_{T'}
      ↓          ↓
    Z_T   ⟶ X_T

commutes.  Both composites are maps into the pullback `X ×_S T`, so this
is `pullback.hom_ext` and the two projection computations; the point is
that the `Z`-side vertical map is `curveBaseChangeMap (ι ≫ strX) h hg`,
i.e. the SAME construction applied to the structure morphism of `Z`.

This is the only geometric input to `pullbackTrivialisedSheaf` below, and
hence the only reason that construction is possible at all: without it
the two ways of restricting `α` to `Z_{T'}` would not be comparable. -/
theorem boundaryBaseChangeMap_comm {X Z S T T' : Scheme.{u}} (strX : X ⟶ S) (ι : Z ⟶ X)
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') :
    boundaryBaseChangeMap strX ι g' ≫ curveBaseChangeMap strX h hg =
      curveBaseChangeMap (ι ≫ strX) h hg ≫ boundaryBaseChangeMap strX ι g := by
  apply pullback.hom_ext
  · simp only [boundaryBaseChangeMap, curveBaseChangeMap, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [boundaryBaseChangeMap, curveBaseChangeMap, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-! ### Rigidified invertible sheaves -/

/-- **A pair `(ℒ, α)`** in the sense of Moret–Bailly §3.4: an invertible
sheaf on `X_T` together with a TRIVIALISATION of its restriction to the
boundary `Z_T`.

`triv` is an isomorphism, i.e. DATA.  Replacing it by `Nonempty (…)`
would define a different and much coarser object — "`ℒ` is trivial along
`Z`" — for which §3.4's exact sequence, §3.9's group `Γ(Z, 𝒪_Z^×)` and
the whole of MB's argument are empty: the entire content of the
generalised Picard functor is that the trivialisations, and not merely
their existence, are remembered. -/
structure TrivialisedSheaf {X Z S T : Scheme.{u}} (strX : X ⟶ S) (ι : Z ⟶ X) (g : T ⟶ S) where
  /-- the invertible sheaf `ℒ` on `X_T` -/
  sheaf : (curveBaseChange strX g).Modules
  /-- `ℒ` is invertible -/
  invertible : IsInvertibleSheaf sheaf
  /-- the trivialisation `α : ℒ|_{Z_T} ≅ 𝒪_{Z_T}` -/
  triv : modPullback (boundaryBaseChangeMap strX ι g) sheaf ≅
    modUnit (curveBaseChange (ι ≫ strX) g)

/-- **Isomorphism of pairs**: an isomorphism `e : ℒ ≅ ℒ'` of the
underlying sheaves COMPATIBLE with the trivialisations, `α' ∘ e|_Z = α`.

Note the contrast with `RelPicEquiv`: there is no quotient by the Picard
group of the test object here.  See the module docstring for why that is
correct and not an omission. -/
def TrivialisedSheafEquiv {X Z S T : Scheme.{u}} {strX : X ⟶ S} {ι : Z ⟶ X} {g : T ⟶ S}
    (p q : TrivialisedSheaf strX ι g) : Prop :=
  ∃ e : p.sheaf ≅ q.sheaf,
    modPullbackMapIso (boundaryBaseChangeMap strX ι g) e ≪≫ q.triv = p.triv

/-- **Isomorphism of pairs is reflexive** (PROVEN) — take `e = 𝟙`.  Used
by any consumer that has to compare a pair with itself after rewriting,
and the cheapest available check that `TrivialisedSheafEquiv` is not
accidentally empty. -/
theorem trivialisedSheafEquiv_refl {X Z S T : Scheme.{u}} {strX : X ⟶ S} {ι : Z ⟶ X}
    {g : T ⟶ S} (p : TrivialisedSheaf strX ι g) : TrivialisedSheafEquiv p p := by
  refine ⟨Iso.refl _, ?_⟩
  ext : 1
  simp only [modPullbackMapIso, Iso.trans_hom, Functor.mapIso_refl, Iso.refl_hom]
  exact Category.id_comp _

/-- **Base change of a pair along `h : T' ⟶ T`** (PROVEN).

The sheaf is pulled back along `X_{T'} ⟶ X_T`; the trivialisation is
transported along the commuting square `boundaryBaseChangeMap_comm`,
through the pullback calculus of `RelativePicard.lean`:

    (b')^* c^* ℒ  ≅  (b' ≫ c)^* ℒ  ≅  (c_Z ≫ b)^* ℒ  ≅  c_Z^* b^* ℒ
                  ≅  c_Z^* 𝒪_{Z_T}  ≅  𝒪_{Z_{T'}}

with `b`, `b'` the boundary inclusions at `T`, `T'`, `c` the base change
of the curve and `c_Z` the base change of the boundary.  Every step is a
named isomorphism (`modPullbackCompIso`, `modPullbackCongrIso`,
`modPullbackMapIso`, `modPullbackUnitIso`); the only non-formal input is
the commuting square. -/
noncomputable def pullbackTrivialisedSheaf {X Z S T T' : Scheme.{u}} {strX : X ⟶ S} {ι : Z ⟶ X}
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g')
    (p : TrivialisedSheaf strX ι g) : TrivialisedSheaf strX ι g' where
  sheaf := modPullback (curveBaseChangeMap strX h hg) p.sheaf
  invertible := isInvertibleSheaf_modPullback _ p.invertible
  triv :=
    modPullbackCompIso (boundaryBaseChangeMap strX ι g') (curveBaseChangeMap strX h hg) p.sheaf ≪≫
      modPullbackCongrIso (boundaryBaseChangeMap_comm strX ι h hg) p.sheaf ≪≫
      (modPullbackCompIso (curveBaseChangeMap (ι ≫ strX) h hg)
        (boundaryBaseChangeMap strX ι g) p.sheaf).symm ≪≫
      modPullbackMapIso (curveBaseChangeMap (ι ≫ strX) h hg) p.triv ≪≫
      modPullbackUnitIso (curveBaseChangeMap (ι ≫ strX) h hg)

/-! ### The generalised relative Picard functor -/

/-- **`pstr : P ⟶ S` REPRESENTS the generalised relative Picard functor
`PG(X, Z)`** of Moret–Bailly §3.4.

Modelled field-for-field on `Fermat.IsRelPicOf`, with the invertible
sheaf replaced by a rigidified pair and `RelPicEquiv` by
`TrivialisedSheafEquiv`:

* `pair` — the pair classified by a `T`-point of `P`;
* `inj` — `P ↪ PG` : isomorphic pairs come from equal points;
* `surj` — `P ↠ PG` : every pair is classified;
* `pair_pre` — the classification is natural in the test object, stated
  against `pullbackTrivialisedSheaf`.

Together `inj`, `surj` and `pair_pre` force `P(T) ≅ PG(X,Z)(T)` naturally
in `T`, which by Yoneda determines `P` up to unique isomorphism over `S`.
No group law is a field, for exactly the reason recorded on `IsRelPicOf`:
it is determined by the classification (the tensor product of pairs is a
pair) and can be derived by a consumer that needs it.

**On `invertible` not being a field**: it is one, inside
`TrivialisedSheaf`, so that the type of `triv` is only ever formed for
sheaves already known invertible.  That is the one structural difference
from `IsRelPicOf`, where invertibility is a separate field of the
predicate.

**Vacuity check.**  The trivial witness `P = S`, `pstr = 𝟙 S` — which
makes `RelPoint (𝟙 S) g` a singleton — fails `surj` as soon as `X` has
two non-isomorphic rigidified pairs over some `T`, e.g. `(𝒪, α)` and
`(𝒪, λ·α)` for `λ ∈ Γ(Z_T, 𝒪^×)` not extending to `X_T`, which is
precisely the left-hand end of the exact sequence 3.4.2 and is nonzero
whenever `Z` has more than one point over the base.  So the predicate is
demanding, not decoration. -/
structure IsGenRelPicOf {X Z P S : Scheme.{u}} (strX : X ⟶ S) (ι : Z ⟶ X) (pstr : P ⟶ S) where
  /-- the rigidified pair on `X_T` classified by a `T`-point of `P` -/
  pair : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint pstr g → TrivialisedSheaf strX ι g
  /-- `P ↪ PG(X,Z)` is a monomorphism of functors -/
  inj : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g),
    TrivialisedSheafEquiv (pair p) (pair q) → p = q
  /-- `P ↠ PG(X,Z)`: every rigidified pair on `X_T` is classified -/
  surj : ∀ {T : Scheme.{u}} {g : T ⟶ S} (Lα : TrivialisedSheaf strX ι g),
    ∃ p : RelPoint pstr g, TrivialisedSheafEquiv (pair p) Lα
  /-- the classification is natural in the test object -/
  pair_pre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (p : RelPoint pstr g),
    TrivialisedSheafEquiv (pair (RelPoint.pre h hg p)) (pullbackTrivialisedSheaf h hg (pair p))

/-- **Moret–Bailly §3.4: the generalised relative Picard functor is
REPRESENTABLE** (SORRY — leaf).

`PG(X, Z)` is representable by a smooth separated commutative `S`-group
scheme.  Only representability is asserted here; the group structure is
determined by `inj`/`surj` (a consumer derives it exactly as
`IsRelPicOf.addPoint` does), and smoothness/separatedness are not needed
by the consumer in `Modularity/MoretBailly.lean`, which uses `PG` only
through its points.

**THE ARGUMENT** (MB 3.4, and the reason this is a leaf rather than a
chapter of its own).  The exact sequence

    1 → 𝔾_{m,S} → (π_Z)_* 𝔾_{m,Z} → PG(X,Z) → Pic_{X/S} → 1

presents `PG(X,Z)` as an extension of `Pic_{X/S}` by the smooth affine
commutative `S`-group scheme `(π_Z)_*𝔾_m / 𝔾_m` — Weil restriction of
`𝔾_m` along the finite flat `π_Z : Z → S`, modulo the constants.  An
extension of a representable functor by a representable one, along a
sequence of fppf sheaves, is representable.  The right-hand term is
`Fermat.IsRelPicOf`, whose representability is `Fermat.exists_relPicFull`
(BLR 8.2/1) in `ModularCurve/RelativePicard.lean`; MB notes (3.4) that
over a FIELD base only the generic fibre is needed, which is Murre's
theorem (SGA 6, XII.1.5), and that is the case the sole consumer of this
leaf is in.

So a prover here has, already in this module's import closure: the
right-hand term (`exists_relPicFull` / `exists_relPicZero`), the
pullback calculus for `modPullback`, and `RelPicEquiv` proven to be an
equivalence relation and a congruence.  What is NOT here and has to be
built is the Weil restriction `(π_Z)_*𝔾_m` and the extension argument.

**FAITHFULNESS.**  The hypotheses are MB's 3.1.2 normalisations, restated
over an arbitrary base:

* `hproper`, `hflat`, `hgi` on `strX` — `X → S` proper flat with
  geometrically integral fibres, which is what gives `f_*𝒪_X = 𝒪_S`
  universally and hence makes the automorphism group of an invertible
  sheaf on `X_T` equal to `Γ(T, 𝒪^×)`;
* `hZfin`, `hZflat`, `hZsurj` on `ι ≫ strX` — `Z → S` finite flat
  surjective, i.e. 3.1.2(iii).  FAITHFULLY FLAT is the load-bearing one:
  it makes `Γ(T,𝒪^×) → Γ(Z_T,𝒪^×)` injective, hence a rigidified pair
  has no nontrivial automorphisms, hence the NAIVE functor written in
  `IsGenRelPicOf` is already an fppf sheaf and `surj` is true as stated.
  Dropping it would make this leaf FALSE, not merely harder: without it
  `surj` asserts that a presheaf which is not a sheaf is representable.

`ι` is not required to be a closed immersion.  MB's `Z` is one, but
nothing in the statement uses it, and the consumer supplies one anyway. -/
theorem exists_genRelPic {X Z S : Scheme.{u}} (strX : X ⟶ S) (ι : Z ⟶ X)
    (hproper : IsProper strX) (hflat : Flat strX)
    (hgi : GeometricallyIrreducible strX)
    (hZfin : IsFinite (ι ≫ strX)) (hZflat : Flat (ι ≫ strX))
    (hZsurj : Surjective (ι ≫ strX)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S), Nonempty (IsGenRelPicOf strX ι pstr) :=
  sorry

end Fermat
