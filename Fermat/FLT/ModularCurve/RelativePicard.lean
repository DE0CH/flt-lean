/-
ModularCurve/RelativePicard.lean — own work for the Fermat project (not
vendored from the FLT project).

# The relative Picard functor, and `Pic⁰` as a representable functor

This module supplies the infrastructure named — and, at the time, called
missing everywhere — by the IRREDUCIBILITY audit of
`Fermat.exists_jacobianOf_x0` in `ModularCurve/X0.lean`:

> the honest cut is *representability of `Pic⁰`* + *autoduality of the
> Jacobian*, and stating it needs a relative Picard functor — line
> bundles on `X ×_S T` modulo pullbacks from `T` — which does not exist
> in `Mathlib`, in `~/cs/FLT`, or here.

That audit was correct about the absence and correct about the route.
What it did not say — and what makes the cut available — is that the
relative Picard functor only has to be **stated** for
`exists_jacobianOf_x0` to decompose; it does not have to be developed.
This module states it.

## What the pin does and does not have (surveyed 2026-07-27)

* `Mathlib.RingTheory.PicardGroup` has `CommRing.Pic R`, the Picard group
  of a commutative **ring**.  It is not about schemes and does not help.
* `Mathlib.AlgebraicGeometry.Modules.Sheaf` has `X.Modules`, the abelian
  category of `𝒪_X`-modules, with `Scheme.Modules.pullback` /
  `pushforward` and their adjunction, and `SheafOfModules.unit` for
  `𝒪_X` itself.  This is the substrate used below.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree` has
  `SheafOfModules.IsLocallyFree` — but with no rank, so it does not cut
  out invertible sheaves.
* There is **no monoidal structure on `SheafOfModules`**: the tensor
  product exists only for *presheaves* of modules
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`).  This is the
  one genuine gap, and it is why no Picard theory could be phrased.
  `modTensor` below closes it in the only direction a statement needs:
  sheafify the presheaf tensor product, using
  `PresheafOfModules.sheafification`, which is exactly how
  `Mathlib.AlgebraicGeometry.Modules.Sheaf` itself relates the two
  categories.

  Note what `modTensor` is *not*: no monoidal-category structure is
  built on `X.Modules` here, so there are no associativity, unit or
  symmetry isomorphisms available, and none are used.  Every statement
  below is invariant under isomorphism of sheaves and never composes two
  tensor products, which is why the bare `tensorObj` suffices.

## The functor

For a morphism `strX : X ⟶ S` and a base point `g : T ⟶ S`, the fibre of
the relative Picard functor at `(T, g)` is

  `Pic(X ×_S T) / (pullbacks of invertible sheaves from T)`.

`RelPicEquiv` is the displayed quotient relation, on invertible sheaves
over the honest base change `pullback strX g`; `modTensor`, `modPullback`
and `IsInvertibleSheaf` are the three pieces it is built from.  Quotienting
by pullbacks from `T` is not optional: without it the assignment
`T`-point of the Jacobian `↦` invertible sheaf on `X_T` is **not**
injective, because `L` and `L ⊗ pr_T^* N` define the same point of
`Pic_{X/S}(T)` for every invertible `N` on `T`.  (The usual alternative —
rigidify along the section instead of quotienting — is equivalent here,
and is not used because it would force the Abel–Jacobi field below to
carry a correction term: `𝒪(x − o)` is *not* canonically rigidified, its
pullback along `o` being the conormal bundle of the section.)

Because `strX` has a section, no fppf sheafification is needed: for a
proper flat morphism with a section and with `f_*𝒪_X = 𝒪_S` universally,
the naive quotient above is already the relative Picard functor
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, 8.1/4; Stacks 0D2C).  That is
what makes `IsRelPicZeroOf` statable with no site theory at all.

## `IsRelPicZeroOf`: what it pins, and why each field is needed

`IsRelPicZeroOf strX ab o` says that the abelian scheme `ab` **is**
`Pic⁰_{X/S}`, presented through the functor of points in the idiom of
`Fermat.AbelianSchemeStruct`:

* `sheaf` attaches to every `T`-point of `J` an `𝒪`-module on `X_T`, and
  `invertible` says it is an invertible sheaf;
* `inj` says the attachment is injective modulo pullbacks from `T` —
  i.e. `J ↪ Pic_{X/S}` is a monomorphism of functors.  Without it every
  scheme would qualify by sending everything to `𝒪`;
* `sheaf_zero` and `sheaf_add` say the attachment is a homomorphism: the
  group law of `J` is the tensor product of invertible sheaves.  Without
  them the embedding would be a bare map of functors and would pin no
  group;
* `sheaf_pre` is naturality — the sheaf attached to a base-changed point
  is the base change of the sheaf;
* `aj` and `aj_spec` are the Abel–Jacobi map: the class `[x] − [o]` is a
  point of `J`, pinned by the isomorphism `𝒪(x − o) ⊗ 𝒪(−x) ≅ 𝒪(−o)`,
  written with `sectionIdeal` for the ideal sheaves of the two sections.
  Without them `J` would only be *some* abelian subscheme of `Pic`;
* `aj_pre` and `aj_base` are the naturality and the pointedness of the
  Abel–Jacobi map, which `Fermat.IsJacobianOf` demands verbatim.

**Why this is a sound cut, i.e. why "`IsRelPicZeroOf` ⟹ `IsJacobianOf`"
is TRUE and not merely plausible.**  `inj`, `sheaf_zero` and `sheaf_add`
exhibit `J` as an abelian *subscheme* of `Pic_{X/S}`, and `aj` puts the
image of the Abel–Jacobi map inside it.  For a smooth proper
geometrically connected curve the image of the Abel–Jacobi map generates
`Pic⁰` as a group, and an abelian subscheme containing a generating set
is everything, so `J = Pic⁰`; the Albanese property is then the classical
consequence of autoduality (`φ : X → A` pointed induces
`A^∨ → J^∨` by pullback of line bundles, and biduality turns that back
into `J → A`).  This is the argument the audit called
"representability + autoduality", and it is why `IsRelPicZeroOf` must
carry the group law and not merely the point-set embedding: an arbitrary
injective natural map of pointed functors would *not* force `J = Pic⁰`.

**Why the cut is not vacuous.**  The trivial abelian scheme `J = Spec ℚ`
does not satisfy `IsRelPicZeroOf` at a curve of positive genus: `inj`
would force every class `[x] − [o]` to vanish in `Pic(X_T)/Pic(T)`, i.e.
`𝒪(x) ≅ 𝒪(o)` for all `x`, which for `g ≥ 1` fails already at `T = X`
and the tautological point.  That is exactly the check that the trivial
witness failed for `exists_jacobianOf_x0` itself, transported to the new
node.

## What is PROVEN here, and the one leaf that is not (amended 2026-07-27)

Everything in the *infrastructure* part of this module is PROVEN.  Since
2026-07-27 the module also carries ONE sorried leaf, `exists_relPicZero`
— Grothendieck representability itself — and it is here rather than next
to a consumer for a reason that is forced by Lean's declaration order:
it has **two** consumers, in two different places in
`ModularCurve/X0.lean`, and only a declaration upstream of both can serve
them.  See its own docstring for the inventory.

The autoduality half of the cut lives next to its consumer in
`ModularCurve/X0.lean`, as the two general-base leaves
`IsRelPicZeroOf.exists_albaneseFactorisation` (autoduality and
biduality) and `IsRelPicZeroOf.eq_of_aj_eq` (generation).  Those two are
the whole of what autoduality still owes.

Amended 2026-07-27: the `Spec ℚ` node `exists_relPicZeroOf` is now
PROVEN, as `exists_relPicZero strX hproper hsmooth hconn o` and nothing
else.  Its sibling `isJacobianOf_of_isRelPicZeroOf` is still sorried but
carries NO mathematics — it is
`⟨(P.isAlbaneseOf ⟨hproper, hsmooth, hconn⟩).isJacobianOf⟩`, and the only
obstacle is that `IsRelPicZeroOf.isAlbaneseOf` and
`IsAlbaneseOf.isJacobianOf` are declared BELOW it in `X0.lean`.  Its
docstring carries the exact relocation that closes it.  Do not dispatch
a prover at it.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Fermat.FLT.Modularity.AbelianScheme

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace Fermat

/-! ### Invertible sheaves

Three definitions, all on `X.Modules`: the tensor product (missing from
the pin), the structure sheaf as a module over itself, and invertibility.
-/

/-- **The tensor product of two `𝒪_Z`-modules.**

The pin has a monoidal structure on *presheaves* of modules but none on
sheaves, so this is the sheafification of the presheaf tensor product —
the same passage `Mathlib.AlgebraicGeometry.Modules.Sheaf` uses to
present `Z.Modules` as a localization of `Z.PresheafOfModules`.

Only the object part is defined.  Nothing below needs functoriality of
`⊗`, an associator, or a unitor, and building the monoidal category
would require knowing that sheafification is monoidal — a genuine
theorem, and not one this development consumes. -/
noncomputable def modTensor {Z : Scheme.{u}} (L M : Z.Modules) : Z.Modules :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val)

/-- **The structure sheaf `𝒪_Z`, read as a module over itself** — the
unit of the tensor product above, and the trivial invertible sheaf. -/
noncomputable def modUnit (Z : Scheme.{u}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf

/-- **Pullback of an `𝒪`-module along a morphism of schemes.**

A thin wrapper on `Scheme.Modules.pullback`, so that statements below
read as `modPullback f L` rather than as an application of a functor. -/
noncomputable def modPullback {Z W : Scheme.{u}} (f : W ⟶ Z) (L : Z.Modules) : W.Modules :=
  (Scheme.Modules.pullback f).obj L

/-- **An invertible sheaf on `Z`**: an `𝒪_Z`-module that is Zariski-locally
isomorphic to `𝒪_Z`.

This is the classical definition (locally free of rank one), stated
directly rather than through `SheafOfModules.IsLocallyFree`, which
carries no rank and so does not cut out the invertible ones.  Stating it
by local triviality rather than by "`∃ M, L ⊗ M ≅ 𝒪`" is deliberate: the
two agree, and the local form needs no properties of `modTensor`.

**Not vacuous, and not empty.**  `IsInvertibleSheaf (modUnit Z)` holds
for every `Z`, by `Scheme.Modules.restrictUnitIso` at `U = ⊤`:

    fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : Z.Opens).ι⟩⟩

That one-liner was elaborated and accepted (2026-07-27) and is recorded
here rather than kept as a declaration, because nothing in the
development consumes it and this project does not allow free-floating
declarations.  It is worth recording because it is the check that
`IsInvertibleSheaf` is satisfiable at all: a predicate that no sheaf
satisfies would make `RelPicEquiv` empty and every field of
`IsRelPicZeroOf` below vacuous. -/
def IsInvertibleSheaf {Z : Scheme.{u}} (L : Z.Modules) : Prop :=
  ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
    Nonempty (L.restrict U.ι ≅ modUnit (U : Scheme.{u}))

/-! ### The relative Picard functor -/

/-- **The base change `X ×_S T` of `strX : X ⟶ S` along `g : T ⟶ S`.**

`Scheme` has all pullbacks, so this needs no chosen-pullback data; it is
named only so that the statements below read as geometry. -/
noncomputable abbrev curveBaseChange {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S) :
    Scheme.{u} :=
  pullback strX g

/-- **The projection `X ×_S T ⟶ T`** — the structure morphism of the
base-changed curve, along which invertible sheaves are pulled back from
`T` in `RelPicEquiv`. -/
noncomputable abbrev curveBaseChangeProj {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S) :
    curveBaseChange strX g ⟶ T :=
  pullback.snd strX g

/-- **The section of `X ×_S T ⟶ T` attached to a relative point of `X`.**

A relative point `x : RelPoint strX g` is a morphism `T ⟶ X` over `S`, so
it is the same thing as a section of the base-changed curve — which is
the form in which its ideal sheaf, hence the divisor `[x]`, can be
written. -/
noncomputable def relSection {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}
    (x : RelPoint strX g) : T ⟶ curveBaseChange strX g :=
  pullback.lift x.1 (𝟙 T) (by rw [x.2, Category.id_comp])

/-- **The base point, read at an arbitrary base `g : T ⟶ S`.**

`o : RelPoint strX (𝟙 S)` is a section of `strX` itself; this is its
image under `RelPoint.pre`, i.e. the constant section `o_T` of the
base-changed curve. -/
def relBasePoint {X S T : Scheme.{u}} {strX : X ⟶ S} (o : RelPoint strX (𝟙 S)) (g : T ⟶ S) :
    RelPoint strX g :=
  RelPoint.pre g (Category.comp_id g) o

/-- **The ideal sheaf `I_σ = 𝒪(−σ)` of a section `σ : T ⟶ Z`.**

The kernel of the canonical `𝒪_Z ⟶ σ_* 𝒪_T`, which is the unit of the
`pullback ⊣ pushforward` adjunction evaluated at `𝒪_Z` (the pullback of
`𝒪_Z` along `σ` being `𝒪_T`).  `Z.Modules` is abelian, so the kernel
exists.

For a section of a smooth curve this is an invertible sheaf, and it is
the only way `𝒪(−x)` can be written at this pin: no divisor theory, no
`𝒪(D)`, and no Cartier divisors exist here. -/
noncomputable def sectionIdeal {Z T : Scheme.{u}} (σ : T ⟶ Z) : Z.Modules :=
  kernel ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Z))

/-- **The morphism `X ×_S T' ⟶ X ×_S T` induced by `h : T' ⟶ T`** over an
identification `h ≫ g = g'` of base points — the base change of the curve
along a change of test object, matching `RelPoint.pre`. -/
noncomputable def curveBaseChangeMap {X S T T' : Scheme.{u}} (strX : X ⟶ S) {g : T ⟶ S}
    {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') :
    curveBaseChange strX g' ⟶ curveBaseChange strX g :=
  pullback.lift (pullback.fst strX g') (pullback.snd strX g' ≫ h)
    (by rw [Category.assoc, hg, pullback.condition])

/-- **Equality in the relative Picard group `Pic(X_T)/Pic(T)`**: two
invertible sheaves on `X ×_S T` have the same class when they differ by
the pullback of an invertible sheaf from `T`.

This quotient is the whole point of the *relative* Picard functor.
Dropping it — comparing invertible sheaves on `X_T` up to isomorphism —
would make the classification map of `IsRelPicZeroOf` non-injective for
every test scheme `T` with `Pic T ≠ 0`, and `inj` would then be a FALSE
field rather than a demanding one. -/
def RelPicEquiv {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)
    (L L' : (curveBaseChange strX g).Modules) : Prop :=
  ∃ N : T.Modules, IsInvertibleSheaf N ∧
    Nonempty (L ≅ modTensor L' (modPullback (curveBaseChangeProj strX g) N))

/-! ### `Pic⁰` as an abelian scheme -/

/-- **`ab` represents the degree-zero relative Picard functor of `strX`,
with Abel–Jacobi map based at `o`.**

See the module docstring for what each field pins, why the cut it makes
possible is sound, and why the trivial abelian scheme does not satisfy it
at a curve of positive genus.

The shape follows `Fermat.AbelianSchemeStruct` and `Fermat.IsJacobianOf`:
everything is stated on relative points, over an arbitrary test scheme,
with naturality in the "identified base" form `RelPoint.pre`. -/
structure IsRelPicZeroOf {X J S : Scheme.{u}} (strX : X ⟶ S) {jstr : J ⟶ S}
    (ab : AbelianSchemeStruct jstr) (o : RelPoint strX (𝟙 S)) where
  /-- the invertible sheaf on `X_T` classified by a `T`-point of `J` -/
  sheaf : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint jstr g → (curveBaseChange strX g).Modules
  /-- the classified sheaves are invertible -/
  invertible : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint jstr g), IsInvertibleSheaf (sheaf p)
  /-- `J ↪ Pic_{X/S}` is a monomorphism of functors -/
  inj : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint jstr g),
    RelPicEquiv strX g (sheaf p) (sheaf q) → p = q
  /-- the zero section is the trivial class -/
  sheaf_zero : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    RelPicEquiv strX g (sheaf (ab.zero g)) (modUnit _)
  /-- the group law of `J` is the tensor product of invertible sheaves -/
  sheaf_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint jstr g),
    RelPicEquiv strX g (sheaf (ab.add p q)) (modTensor (sheaf p) (sheaf q))
  /-- the classification is natural in the test object -/
  sheaf_pre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (p : RelPoint jstr g),
    RelPicEquiv strX g' (sheaf (RelPoint.pre h hg p))
      (modPullback (curveBaseChangeMap strX h hg) (sheaf p))
  /-- the Abel–Jacobi map `x ↦ [x] − [o]` -/
  aj : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint strX g → RelPoint jstr g
  /-- ... classified by `𝒪(x − o)`, pinned as `𝒪(x − o) ⊗ 𝒪(−x) ≅ 𝒪(−o)` -/
  aj_spec : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint strX g),
    RelPicEquiv strX g (modTensor (sheaf (aj x)) (sectionIdeal (relSection x)))
      (sectionIdeal (relSection (relBasePoint o g)))
  /-- the Abel–Jacobi map is natural -/
  aj_pre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x : RelPoint strX g),
    aj (RelPoint.pre h hg x) = RelPoint.pre h hg (aj x)
  /-- the base point goes to the origin -/
  aj_base : aj o = ab.zero (𝟙 S)

/-- **GROTHENDIECK REPRESENTABILITY: `Pic⁰_{X/S}` is an abelian scheme,
for a smooth proper geometrically connected curve with a section, over an
ARBITRARY base** (sorry node).

TRUE and classical: FGA, exposé 232 (representability of `Pic_{X/S}` for
a projective flat morphism with integral geometric fibres);
Bosch–Lütkebohmert–Raynaud, *Néron Models*, 8.2/1 (existence) and 9.4/4
(`Pic⁰` of a relative curve is an abelian scheme); Stacks 0D2C.  The
section `o` is what makes the naive quotient `Pic(X_T)/Pic(T)` —
`RelPicEquiv` above — already equal to the relative Picard functor (BLR
8.1/4), which is the only reason `IsRelPicZeroOf` is statable at a pin
with no site theory; and it is what the Abel–Jacobi fields `aj`,
`aj_spec`, `aj_base` are based at.

Each of the three geometric hypotheses is load-bearing.  Without
properness `Pic⁰` is not proper; without smoothness it is not smooth;
without geometric connectedness `f_*𝒪_X = 𝒪_S` fails universally, so the
quotient presentation is not the Picard functor at all and `inj` becomes
a false demand rather than a strong one.

**WHY THIS LEAF LIVES HERE AND NOT NEXT TO A CONSUMER.**  It has two
consumers, both in `ModularCurve/X0.lean` and separated by ~4700 lines:

* `exists_relPicZeroOf` — the `S = SpecQ` instance, stated verbatim with
  the same three unbundled hypotheses.  It is **exactly**
  `exists_relPicZero strX hproper hsmooth hconn o` and nothing else; it
  should be reduced to this declaration rather than proven a second time.
* `exists_albaneseOfCurve` — the general-base Albanese of a curve, which
  needs `S = Spec ℤ_(ℓ)` and `S = Spec 𝔽_ℓ` and so cannot use the
  `SpecQ` version at all.  That is what forced the general statement.

Lean's declaration order is the whole of the argument: a leaf placed at
either consumer is unreachable from the other, and two independently
sorried copies of one classical theorem is the most expensive object
this development can produce.  Universe-polymorphic for the same reason —
nothing here is specific to `Scheme.{0}`.

**WHAT THIS LEAF STILL NEEDS**, none of which exists at this pin
(surveyed 2026-07-27, and note that the survey the *older* docstrings
record — "no monoidal structure on `SheafOfModules`, hence no `Pic` of a
scheme at all" — is now REFUTED by `modTensor` and `sectionIdeal`
above, which is exactly what made this statement writable):

* cohomology and base change for a proper morphism (Hartshorne III.12,
  Stacks 0E6R) — the source of both the smoothness criterion
  (`H²` vanishes on a relative curve, so `Pic` is smooth) and the
  formal-deformation argument behind representability;
* the `𝒪(D)` dictionary on a relative curve — relative effective Cartier
  divisors and the map `Div ⟶ Pic` — of which only the section case
  (`sectionIdeal`) is available here;
* properness of `Pic⁰`, i.e. the valuative criterion for line bundles on
  a relative curve;
* the connected-component-of-identity construction that cuts `Pic⁰` out
  of `Pic`.

A refutation of the first item would be a proof of
`HasUniversallyTrivialPushforward`-style base change in
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`, which is
where the neighbouring `f_*𝒪 = 𝒪` statement already lives; that module is
the natural home for the missing input and is the check that would refute
this note.

**TWO AXES SEARCHED AND REJECTED (2026-07-27), each with an explicit junk
witness, because both look like obvious further cuts and both are wrong.**

*Rejected: split off "the classifying scheme is PROPER" / "…is SMOOTH".*
The tempting cut is "a scheme carrying the classification data exists"
plus "any such scheme is proper and smooth", which would isolate BLR
8.4/2 and 9.4/4 as separate leaves.  It is UNSOUND, and the
counterexample is `Pic_{X/S}` ITSELF: the full Picard scheme satisfies
`sheaf`, `invertible`, `inj`, `sheaf_zero`, `sheaf_add`, `sheaf_pre`,
`aj` and `aj_spec` — every field of `IsRelPicZeroOf` that does not
mention `AbelianSchemeStruct`'s geometry — and it is **not proper**,
being the disjoint union of the `Pic^d` over `d ∈ ℤ`.  So the second
half would be a FALSE leaf.  Nothing in `IsRelPicZeroOf` distinguishes
`Pic` from `Pic⁰`; what would is a surjectivity ("every invertible sheaf
on `X_T` is classified") field, which `IsRelPicZeroOf` deliberately does
not have.  Consequently the passage `Pic ↝ Pic⁰` and the proof that the
result is proper and smooth cannot be separated: they have to be stated
together, i.e. as this leaf.

*Rejected: split off the Abel–Jacobi fields.*  Dropping `aj`, `aj_spec`,
`aj_pre`, `aj_base` to leave a "pure classification" leaf is VACUOUS:
the trivial abelian scheme `J = S`, `jstr = 𝟙 S` satisfies all six
remaining fields, since `RelPoint (𝟙 S) g` is a singleton and `inj` is
then free.  The Abel–Jacobi half would inherit all the content and could
no longer be stated, the witness having been chosen.  This is the same
trap `exists_jacobianOf_x0`'s audit recorded for "existence plus
initiality", in the Picard idiom.

So this leaf is atomic ALONG THE STRUCTURAL AXIS — cuts that partition
the fields of `IsRelPicZeroOf` — and the search that would refute that is
a field-partition of `IsRelPicZeroOf` for which NEITHER `Pic_{X/S}` nor
`Spec ℚ` is a witness of the weaker half.  It was not searched along the
axis of the CONSTRUCTION (Quot/Hilbert schemes, `Sym^d C ⟶ Pic^d`), which
is where a genuine decomposition would come from once relative effective
Cartier divisors exist. -/
theorem exists_relPicZero {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S)) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsRelPicZeroOf strX ab o) :=
  sorry

end Fermat
