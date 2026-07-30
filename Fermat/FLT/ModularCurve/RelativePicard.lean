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
  built on `X.Modules` here.  **Amended 2026-07-28** — the sentence that
  stood here went on to say "so there are no associativity, unit or
  symmetry isomorphisms available, and none are used", and both halves
  are now false.  The tensor-calculus section below PROVES congruence
  (`modTensorMapIso`) and the right unitor (`modTensorUnitRightIso`), and
  states the remaining four as named leaves; `relPicEquiv_refl`,
  `relPicEquiv_symm` and `relPicEquiv_trans` use them, and the two
  representability leaves consume the resulting
  `relPicEquiv_equivalence`.  What is still absent is a
  monoidal-CATEGORY structure — coherence — which nothing here needs.

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

## What is PROVEN here, and the leaves that are not (amended 2026-07-28)

Everything in the *infrastructure* part of this module is PROVEN.
`exists_relPicZero` — Grothendieck representability itself — is here
rather than next to a consumer for a reason that is forced by Lean's
declaration order: it has **two** consumers, in two different places in
`ModularCurve/X0.lean`, and only a declaration upstream of both can serve
them.  See its own docstring for the inventory.

Amended 2026-07-28: `exists_relPicZero` is now PROVEN, as the two-line
composition of the two classical theorems its own docstring had always
been citing side by side, along the CONSTRUCTION axis its atomicity
audit recorded as unsearched:

* `exists_relPicFull` — BLR 8.2/1, existence of the full relative
  Picard scheme, stated through the new `IsRelPicOf`;
* `exists_relPicZero_of_isRelPicOf` — BLR 9.4/4, `Pic⁰` is an abelian
  scheme once `Pic` exists.

Amended again 2026-07-28: **both of those are now PROVEN too**, each as a
short composition that discharges the classical inputs of its own leaf.
The frontier moved DOWN one level rather than closing, and the seven
leaves it moved to are, in dependency order:

* three in the tensor-calculus section — `nonempty_modTensor_assocPic`,
  `nonempty_modPullback_modTensorPic` and `exists_modTensor_inv`.  None
  mentions Picard theory.  They are what `relPicEquiv_equivalence` runs
  on.  The first two are restatements of declarations in
  `Fermat/FLT/Modularity/AmpleSheaf.lean` that are respectively proven
  and owned there, and the action on them is a hoist rather than a
  proof — see their docstrings.

  **Amended 2026-07-29: `exists_modTensor_inv` is now PROVEN**, and the
  leaf under it is `exists_modDual` — the dual sheaf `L^∨` with its
  evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_Z`, asked for only up to LOCAL
  isomorphy of that one global map.  Both it and the global-from-local
  step `isIso_of_locally_isIso` that closes the gap were HOISTED here
  from `AmpleSheaf.lean`, where they had been written against a twin of
  this leaf named `exists_modTensor_inverse`; that module is DOWNSTREAM,
  so the two copies could never have merged any other way.
  `exists_modDual` is the one legitimate dispatch target of this section;
* `exists_relPicOf_isAffineOpen` and
  `exists_relPicOf_of_forall_isAffineOpen` — the two halves that
  `exists_relPicOf_of_hasUniversallyTrivialPushforward` (FGA 232, with
  `f_*𝒪 = 𝒪` and the equivalence relation supplied) was cut into on
  2026-07-29; that leaf is now PROVEN as their two-line assembly.  The
  first is FGA 232 proper — projectivity over an affine base — and the
  second is Zariski gluing, which needs no FGA and is the approachable
  one.  See the section header above them;
* `exists_relPicZeroOf_of_relPicGroupLaw` — BLR 9.4/4 with `f_*𝒪 = 𝒪`,
  the equivalence relation and the group law on `Pic`'s points supplied.
  **Amended 2026-07-29: this one is now PROVEN**, over a two-leaf cut of
  BLR 9.4/4 into its `𝒪(D)` half and its geometric half, which are
  independent of each other:

  * `exists_abelJacobiPoint` — the Abel–Jacobi map `x ↦ [x] − [o]` into
    the POINTS of `Pic`.  Owes two facts about `sectionIdeal` (that
    `𝒪(−σ)` is invertible, and that it commutes with base change) plus
    one tensor-calculus statement its docstring names precisely;
  * `exists_relPicZeroSubgroup` — the geometry: cut `Pic⁰` out of `Pic`
    and show it is proper, smooth and geometrically connected.  This is
    what BLR 9.4/4 is usually cited FOR, and it is the leaf with real
    content: the identity component of a group scheme does not exist at
    this pin in any form.

Also PROVEN here and worth knowing about before re-deriving them:
`modTensorMapIso`, `modTensorUnitLeftIso`, `modTensorUnitRightIso`,
`modPullbackUnitIso`, `isInvertibleSheaf_modUnit`,
`isInvertibleSheaf_modTensorPic`, `relPicEquiv_refl/symm/trans/equivalence`,
and `IsRelPicOf.zeroPoint/addPoint` with their two classification specs.
Most of the first group was HOISTED from `AmpleSheaf.lean`; see the
tensor-calculus section header.

`IsRelPicOf` is `IsRelPicZeroOf` with the group law and the Abel–Jacobi
fields dropped and a **surjectivity** field added; that field is what
makes `Pic` rather than `Pic⁰` the intended witness, and it is exactly
the field `exists_relPicZero`'s atomicity audit named as the missing
discriminator.  `IsRelPicOf` is also the shape a future
`DualStruct`-to-`Pic⁰` bridge wants (`AbelianScheme.lean` records that
bridge as the concrete next step for polarizations), so it is worth
having for more than this leaf.

The autoduality half of the cut lives next to its consumer in
`ModularCurve/X0.lean`, as the two general-base leaves
`IsRelPicZeroOf.exists_albaneseFactorisation` (autoduality and
biduality) and `IsRelPicZeroOf.eq_of_aj_eq` (generation).  Those two are
the whole of what autoduality still owes.

Amended 2026-07-27: the `Spec ℚ` node `exists_relPicZeroOf` is now
PROVEN, as `exists_relPicZero strX hproper hsmooth hconn o` and nothing
else.

Amended 2026-07-28, correcting the paragraph that stood here: its sibling
`isJacobianOf_of_isRelPicZeroOf` is **no longer sorried either**.  This
file used to say it was still open, carrying no mathematics, blocked only
by `IsRelPicZeroOf.isAlbaneseOf` and `IsAlbaneseOf.isJacobianOf` being
declared BELOW it in `X0.lean`.  That diagnosis was right and the
relocation it prescribed has since been carried out, so the node is now
the one line `⟨(P.isAlbaneseOf ⟨hproper, hsmooth, hconn⟩).isJacobianOf⟩`
and is PROVEN.  Checked against the compiler's `declaration uses 'sorry'`
set for `X0.lean`, not against its docstrings.  The two genuinely open
leaves left in the autoduality half are still
`IsRelPicZeroOf.exists_albaneseFactorisation` and
`IsRelPicZeroOf.eq_of_aj_eq`.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open TopologicalSpace MonoidalCategory Opposite

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

/-! ### A tensor calculus for `modTensor`

**This section exists because of a specific recorded finding, and it
absorbs one that was made independently downstream.**

The ROUTE AUDIT on `exists_relPicFull` below concluded that the one live
gate on every route to representability is that `modTensor` supplies only
the OBJECT part of a tensor product: with no unitor, no associator and no
inverses, `RelPicEquiv` is not known to be reflexive, symmetric or
transitive, so the relative Picard presheaf cannot be assembled as a
functor and none of mathlib's representability machinery can be pointed
at it.  That audit named the discharging check explicitly — "prove
`RelPicEquiv` is an equivalence relation … and the fppf/Zariski route
opens".  This section runs that check; `relPicEquiv_equivalence` below is
the result.

**Where this material came from (2026-07-28).**  Most of it was NOT
written here.  `Fermat/FLT/Modularity/AmpleSheaf.lean`, which *imports*
this module, had already built the same calculus for its own purposes,
having reached the same conclusion the audit above did and recorded it in
its own words:

> `RelativePicard.lean` built only the object part of `⊗` because
> "building the monoidal category would require knowing that
> sheafification is monoidal".  That is true of the ASSOCIATOR and false
> of everything else.

That is correct, and it was found by a `declaration uses 'sorry'`-level
collision rather than by reading: an attempt to state
`isInvertibleSheaf_modUnit` here failed to build `AmpleSheaf.lean` with
"`Fermat.isInvertibleSheaf_modUnit` has already been declared".  Since
`AmpleSheaf` imports this module and not conversely, the material had to
move UP for the Picard leaves to use it, so the following declarations
were **hoisted out of `AmpleSheaf.lean` unchanged** and deleted there:
`modPullbackCompIso`, `modPullbackCongrIso`, `modPullbackMapIso`,
`presheafOfModulesMonoidal`, `modSheafifyValIso`, `modTensorMapIso`,
`modTensorUnitLeftIso`, `opensMapFinal`, `modPullbackUnitIso`,
`modRestrictPullbackIso`, `modRestrictLEIso`, `trivializationOfLE`,
`isInvertibleSheaf_modUnit`.  `AmpleSheaf.lean` inherits every one of
them by import and is otherwise untouched.

**So do not re-derive any of this, and note in particular that two
statements the audit listed as missing are FREE at this pin**:
`modPullbackUnitIso` (`f^*𝒪_Y ≅ 𝒪_X`, because `Opens.map g` is a Final
functor — `opensMapFinal` — so mathlib's
`SheafOfModules.pullbackObjUnitToUnit` is an isomorphism), and both
unitors.

**And so is the SYMMETRY — a third one, found and compiler-checked
2026-07-29.**  Every audit in this file that lists the missing pieces
puts "symmetry" beside "associativity"; that is wrong, and it is wrong
for the same reason the unitors were.  Mathlib carries
`SymmetricCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _))`
(`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`, line 146),
so the braiding needs only the same re-keying `presheafOfModulesMonoidal`
already does, and then sheafifying it is the same three lines as
`modTensorUnitLeftIso`.  Verified to elaborate against this module's
oleans, in full:

    noncomputable instance presheafOfModulesSymm (Z : Scheme.{u}) :
        SymmetricCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
      inferInstanceAs (SymmetricCategory
        (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

    noncomputable def modTensorSymmIso {Z : Scheme.{u}} (L M : Z.Modules) :
        modTensor L M ≅ modTensor M L :=
      (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (β_ L.val M.val)

Neither is a declaration here, because nothing in the module consumes one
yet and this project forbids free-floating declarations — the same reason
`isInvertibleSheaf_modUnit` spent a day as a docstring one-liner.  **Paste
them in as soon as you have a consumer**; `exists_abelJacobiPoint` below
is the first, and its docstring says where each use falls.

The immediate consequences, so that nobody prices them as leaves:
`modTensor L M ≅ 𝒪 → modTensor M L ≅ 𝒪` is one line, and the
middle-four interchange `(L ⊗ N) ⊗ M ≅ (L ⊗ M) ⊗ N` is
`nonempty_modTensor_assocPic` twice plus one braiding.  **`ASSOCIATIVITY`
is the only genuinely missing coherence isomorphism** at this pin.

**What is genuinely still open** is exactly the part needing
*sheafification to be monoidal*.  Two leaves are stated below,
`nonempty_modTensor_assocPic` and `nonempty_modPullback_modTensorPic`,
and **both already have proofs or owners in `AmpleSheaf.lean`** — see
their docstrings.  They are duplicated here only because the declarations
that discharge them sit below this module in the import order and could
not be hoisted without colliding with live work.  **They must not be
dispatched at independently**; the correct action on either is a hoist,
not a proof. -/

/-! #### Pseudo-functoriality of `modPullback` (PROVEN — free from the pin) -/

/-- **`f^*(g^* L) ≅ (f ≫ g)^* L`** — `Scheme.Modules.pullbackComp`, read on an
object. -/
noncomputable def modPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) :
    modPullback f (modPullback g L) ≅ modPullback (f ≫ g) L :=
  (Scheme.Modules.pullbackComp f g).app L

/-- **Pullbacks along equal morphisms agree** — `Scheme.Modules.pullbackCongr`,
read on an object.  Needed because `pullback.condition` is an equality of
morphisms, not a definitional identity. -/
noncomputable def modPullbackCongrIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (L : Y.Modules) :
    modPullback f L ≅ modPullback g L :=
  (Scheme.Modules.pullbackCongr h).app L

/-- **`f^*` carries isomorphisms to isomorphisms** — it is a functor. -/
noncomputable def modPullbackMapIso {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules} (e : L ≅ M) :
    modPullback f L ≅ modPullback f M :=
  (Scheme.Modules.pullback f).mapIso e

/-! #### The monoidal structure that `modTensor` inherits from presheaves -/

/-- The presheaf-level monoidal structure, re-keyed on `Z.ringCatSheaf.obj`.

`Mathlib`'s instance is stated for `PresheafOfModules (R ⋙ forget₂ CommRingCat
RingCat)` with `R` a presheaf of *commutative* rings; typeclass search cannot
invert that composition against `Z.ringCatSheaf.obj`, which is definitionally
`Z.presheaf ⋙ forget₂ CommRingCat RingCat`.  This instance supplies it. -/
noncomputable instance presheafOfModulesMonoidal (Z : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- **Sheafifying a sheaf changes nothing**: `a(M.val) ≅ M`.

The counit of `PresheafOfModules.sheafificationAdjunction`, which mathlib
already knows is an isomorphism. -/
noncomputable def modSheafifyValIso {Z : Scheme.{u}} (M : Z.Modules) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).counit).app M

/-- **`modTensor` is functorial** (on isomorphisms, which is all that is used).

The morphism part this module originally declined to define: sheafify
`PresheafOfModules.Monoidal.tensorHom`. -/
noncomputable def modTensorMapIso {Z : Scheme.{u}} {L L' M M' : Z.Modules}
    (e : L ≅ L') (e' : M ≅ M') : modTensor L M ≅ modTensor L' M' :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso
      ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso e'))

/-- **The LEFT UNITOR**, `𝒪_Z ⊗ M ≅ M`.  Sheafify the presheaf-level unitor,
then use that `M` is already a sheaf. -/
noncomputable def modTensorUnitLeftIso {Z : Scheme.{u}} (M : Z.Modules) :
    modTensor (modUnit Z) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    modSheafifyValIso M

/-- **THE RIGHT UNITOR**, `L ⊗ 𝒪_Z ≅ L` (PROVEN 2026-07-28, new here).

`AmpleSheaf.lean` built only the left unitor, "since nothing here consumes
the right one"; `relPicEquiv_refl` below does, because `RelPicEquiv` puts
the twisting sheaf on the RIGHT.  Same three-line construction with
`MonoidalCategory.rightUnitor` in place of `λ_`. -/
noncomputable def modTensorUnitRightIso {Z : Scheme.{u}} (L : Z.Modules) :
    modTensor L (modUnit Z) ≅ L :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (ρ_ L.val) ≪≫
    modSheafifyValIso L

/-! #### `f^* 𝒪_Y ≅ 𝒪_X` -/

/-- **`Opens.map g` is a FINAL functor**, for every continuous `g : X ⟶ Y`.

`StructuredArrow U (Opens.map g)` has the TERMINAL object `⊤` — every `U` obeys
`U ≤ g ⁻¹ᵁ ⊤` — and a category with a terminal object is connected. -/
instance opensMapFinal {X Y : TopCat.{u}} (g : X ⟶ Y) : (Opens.map g).Final := by
  constructor
  intro U
  have hterm : ∀ A : StructuredArrow U (Opens.map g),
      Nonempty (A ⟶ StructuredArrow.mk (Y := (⊤ : Opens Y)) (homOfLE le_top)) :=
    fun _ => ⟨StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)⟩
  have : Nonempty (StructuredArrow U (Opens.map g)) :=
    ⟨StructuredArrow.mk (Y := ⊤) (homOfLE le_top)⟩
  apply zigzag_isConnected
  intro j₁ j₂
  exact Relation.ReflTransGen.head (Or.inl (hterm j₁))
    (Relation.ReflTransGen.single (Or.inr (hterm j₂)))

/-- **`f^* 𝒪_Y ≅ 𝒪_X`** — mathlib's `SheafOfModules.pullbackObjUnitToUnit`,
which is an isomorphism because `Opens.map f.base` is final (`opensMapFinal`).

The `IsIso` instance is supplied by name rather than by `inferInstance`: the
two occurrences of `pullbackObjUnitToUnit` otherwise pick up different (but
defeq) `IsRightAdjoint` instance arguments and unification stalls. -/
noncomputable def modPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modPullback f (modUnit Y) ≅ modUnit X :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom f))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)

/-! #### Restriction to an open, as a pullback -/

/-- **Restriction along an open immersion IS the pullback** —
`Scheme.Modules.restrictFunctorIsoPullback`, read on an object. -/
noncomputable def modRestrictPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (A : Y.Modules) : A.restrict f ≅ modPullback f A :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app A

/-- **`A|_W ≅ (A|_U)|_W` for `W ≤ U`** (PROVEN — `Scheme.homOfLE_ι` transported by
`Scheme.Modules.restrictFunctorCongr`, then `restrictFunctorComp`).

Both factors have `rfl` `_app_app` lemmas reading `A.presheaf.map (eqToHom _).op`,
which is what makes `trivializedSection_trivializationOfLE` (in
`Modularity/AmpleSheaf.lean`, downstream) provable.  **DO NOT re-route this
through `modPullback`**: that older definition composed
`Adjunction.leftAdjointUniq` components, which compute on sections not at all,
and it is what kept that lemma open.  The two definitions are propositionally
equal and only this one is usable. -/
noncomputable def modRestrictLEIso {Z : Scheme.{u}} (A : Z.Modules) {W U : Z.Opens} (h : W ≤ U) :
    A.restrict W.ι ≅ (A.restrict U.ι).restrict (Z.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (Z.homOfLE_ι h).symm).app A ≪≫
    (Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι).app A

/-- **A trivialization over `U` restricts to one over any `W ≤ U`** (PROVEN). -/
noncomputable def trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens} (h : W ≤ U)
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    A.restrict W.ι ≅ modUnit (W : Scheme.{u}) :=
  modRestrictLEIso A h ≪≫ (Scheme.Modules.restrictFunctor (Z.homOfLE h)).mapIso φ ≪≫
    Scheme.Modules.restrictUnitIso (Z.homOfLE h)

/-! #### Invertibility -/

/-- `𝒪_Z` is invertible.  (Recorded as a one-liner in the `IsInvertibleSheaf`
docstring above; it has consumers now, so it is a declaration.) -/
theorem isInvertibleSheaf_modUnit (Z : Scheme.{u}) : IsInvertibleSheaf (modUnit Z) :=
  fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : Z.Opens).ι⟩⟩

/-! #### The two leaves that remain, and their downstream twins -/

/-- **ASSOCIATIVITY OF `modTensor`** (sorry leaf — **BUT SEE THE WARNING**).

`modTensor` sheafifies after each tensor, so this compares
`sheafify (sheafify (L ⊗ M) ⊗ N)` with `sheafify (L ⊗ sheafify (M ⊗ N))`.
Both are `sheafify (L ⊗ M ⊗ N)`, and proving so is exactly the statement
that **sheafification is monoidal**.

**DO NOT DISPATCH A PROVER AT THIS.**  It is the verbatim twin of
`Fermat.nonempty_modTensor_assoc` in
`Fermat/FLT/Modularity/AmpleSheaf.lean`, which is **PROVEN** there
(2026-07-28) by localizing the presheaf monoidal category at the class
`modLocW` of local isomorphisms and transporting — over two leaves of its
own, `modLocW_whiskerLeft` and `modLocW_whiskerRight`, which have their
own owners.

It is restated here only because that proof and its ~150 lines of
localization machinery sit BELOW this module in the import order, in a
region of `AmpleSheaf.lean` with live owners, so it could not be hoisted
the way everything above it was.  **The correct action is the hoist**:
once `modLocW_whiskerLeft`/`Right` are settled, move the
`modLocW`/`ModLM`/`modTensorLocIso`/`nonempty_modTensor_assoc` block up
here and delete this declaration, redirecting its two uses in
`relPicEquiv_symm` and `relPicEquiv_trans`. -/
theorem nonempty_modTensor_assocPic {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor L (modTensor M N)) := sorry

/-- **PULLBACK COMMUTES WITH `modTensor`** (sorry leaf — **BUT SEE THE
WARNING**).

`Scheme.Modules.pullback` is a left adjoint and the presheaf pullback is
strong monoidal, so the content is again that sheafification is monoidal:
the sheafification inside `modTensor` has to move across the pullback.

**DO NOT DISPATCH A PROVER AT THIS.**  It is the verbatim twin of
`Fermat.nonempty_modPullback_modTensor` in
`Fermat/FLT/Modularity/AmpleSheaf.lean`, which is an open leaf there with
a live owner as of 2026-07-28.  Same reason as the leaf above: it could
not be hoisted without colliding with that owner's work.  **The correct
action is the hoist**, once that owner has finished. -/
theorem nonempty_modPullback_modTensorPic {Z W : Scheme.{u}} (h : W ⟶ Z) (L M : Z.Modules) :
    Nonempty (modPullback h (modTensor L M) ≅ modTensor (modPullback h L) (modPullback h M)) :=
  sorry

/-- **RESTRICTION COMMUTES WITH `modTensor`** (PROVEN over
`nonempty_modPullback_modTensorPic`) — the special case the invertibility
argument below actually consumes, and strictly weaker than the general
statement. -/
theorem nonempty_restrict_modTensorPic {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (L M : Y.Modules) :
    Nonempty ((modTensor L M).restrict f ≅ modTensor (L.restrict f) (M.restrict f)) := by
  obtain ⟨e⟩ := nonempty_modPullback_modTensorPic f L M
  exact ⟨modRestrictPullbackIso f _ ≪≫ e ≪≫
    modTensorMapIso (modRestrictPullbackIso f L).symm (modRestrictPullbackIso f M).symm⟩

/-- **A TENSOR PRODUCT OF INVERTIBLE SHEAVES IS INVERTIBLE** (PROVEN over
`nonempty_modPullback_modTensorPic`): trivialize both over `U ⊓ V`.

Consumed by `IsRelPicOf.addPoint`, which needs the tensor product of two
classified sheaves to be invertible before `surj` will classify it, and
by `relPicEquiv_trans`. -/
theorem isInvertibleSheaf_modTensorPic {Z : Scheme.{u}} {L M : Z.Modules}
    (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) : IsInvertibleSheaf (modTensor L M) := by
  intro z
  obtain ⟨U, hzU, ⟨φ⟩⟩ := hL z
  obtain ⟨V, hzV, ⟨ψ⟩⟩ := hM z
  obtain ⟨e⟩ := nonempty_restrict_modTensorPic (U ⊓ V : Z.Opens).ι L M
  exact ⟨U ⊓ V, ⟨hzU, hzV⟩, ⟨e ≪≫ modTensorMapIso (trivializationOfLE inf_le_left φ)
    (trivializationOfLE inf_le_right ψ) ≪≫ modTensorUnitLeftIso _⟩⟩

/-! #### Global-from-local, and the dual sheaf

**HOISTED from `Modularity/AmpleSheaf.lean` (2026-07-29), and the hoist is the
POINT rather than a tidy-up.**  `isIso_of_locally_isIso` and `exists_modDual`
were written there on 2026-07-28 (branch `flt-lean-337`) to prove
`exists_modTensor_inverse`, a verbatim twin of `exists_modTensor_inv` below.
But `AmpleSheaf.lean` `public import`s THIS module, so nothing it proves can
serve the relative-Picard calculus here, and the two copies of the leaf could
only ever both stay open.  They are therefore declared here, once, and the
`AmpleSheaf.lean` copies deleted with their consumers redirected. -/

/-- **ISOMORPHY IS LOCAL ON THE BASE** (PROVEN 2026-07-28) — a morphism of
`𝒪_Z`-modules whose restriction to each member of an open cover is an
isomorphism is itself an isomorphism.

This is the global-from-local half of every "the evaluation pairing
`L ⊗ L^∨ ⟶ 𝒪` is an isomorphism because it is one on trivializing opens"
argument, and it is the half that is formal.  It is stated for an arbitrary
morphism because nothing in the proof knows about `modTensor`.

**Route (all four steps are mathlib at this pin).**
1. `Scheme.Modules.toPresheaf Z : Z.Modules ⥤ TopCat.Presheaf Ab Z` REFLECTS
   isomorphisms (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, instance just
   below `toPresheaf`), so it suffices to make the underlying map of
   `Ab`-presheaves an isomorphism.
2. Those presheaves are sheaves (`Scheme.Modules.isSheaf`), so
   `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`
   (`Mathlib/Topology/Sheaves/Stalks.lean`) reduces that to the stalk maps.
3. `Scheme.Modules.restrictStalkNatIso` identifies the stalk of a RESTRICTION
   at `x : U` with the stalk of the original at `U.ι x`, naturally in the
   module — and `U.ι ⟨z, hz⟩ = z` is `rfl`.
4. `NatIso.isIso_map_iff` transports "is an iso" across that natural iso.

**Worth recording, because `AmpleSheaf.lean`'s module docstring could be read
as forbidding this.**  That docstring says `Scheme.Modules` "has no `Module`
structure on stalks at this pin", which is why `NonvanishingAt` is stated
through local trivializations rather than through stalks.  That remains true
and is not contradicted here: detecting an ISOMORPHISM needs no module
structure on the stalk, only the underlying `Ab`-stalk, because `toPresheaf`
already reflects isomorphisms.  Stalks are unusable for *stating* generation;
they are perfectly usable for *detecting* invertibility. -/
theorem isIso_of_locally_isIso {Z : Scheme.{u}} {A B : Z.Modules} (f : A ⟶ B)
    (h : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  have hstalk : ∀ z : Z, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} z).map
      ((Scheme.Modules.toPresheaf Z).map f)) := by
    intro z
    obtain ⟨U, hz, hiso⟩ := h z
    haveI := hiso
    have h1 : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙
        Scheme.Modules.toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (⟨z, hz⟩ : U.toScheme)).map f) := by
      show IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (⟨z, hz⟩ : U.toScheme)).map
        ((Scheme.Modules.toPresheaf U.toScheme).map ((Scheme.Modules.restrictFunctor U.ι).map f)))
      infer_instance
    exact (NatIso.isIso_map_iff
      (Scheme.Modules.restrictStalkNatIso U.ι (⟨z, hz⟩ : U.toScheme)) f).mp h1
  let FA : TopCat.Sheaf Ab.{u} Z.toPresheafedSpace := ⟨A.presheaf, A.isSheaf⟩
  let FB : TopCat.Sheaf Ab.{u} Z.toPresheafedSpace := ⟨B.presheaf, B.isSheaf⟩
  let g : FA ⟶ FB := ⟨(Scheme.Modules.toPresheaf Z).map f⟩
  haveI : ∀ x : Z, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map g.hom) := hstalk
  haveI : IsIso g := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso g
  haveI : IsIso ((Scheme.Modules.toPresheaf Z).map f) :=
    (TopCat.Sheaf.forget Ab.{u} Z.toPresheafedSpace).map_isIso g
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf Z)

/-- **THE DUAL SHEAF AND ITS EVALUATION PAIRING** (sorry leaf, cut 2026-07-28
out of `exists_modTensor_inv`) — an invertible `L` admits an invertible `M`
together with a GLOBAL morphism `ev : L ⊗ M ⟶ 𝒪_Z` that is an isomorphism
LOCALLY.

TRUE and classical (Hartshorne II.6.12, Stacks 01CV): take `M := L^∨ =
Hom_{𝒪_Z}(L, 𝒪_Z)` with `ev` the evaluation map.  On a trivializing open both
sides are `𝒪` and `ev` is the multiplication `𝒪 ⊗ 𝒪 ≅ 𝒪`, which is where the
local isomorphy comes from; `L^∨` is invertible for the same local reason.

**WHY THE MORPHISM `ev` IS PART OF THE STATEMENT AND CANNOT BE DROPPED.**  A
weaker-looking cut — "`∃ M` invertible with `modTensor L M` locally isomorphic
to `𝒪`" — is TRUE FOR EVERY `M`, hence useless: `isInvertibleSheaf_modTensorPic`
above already proves the tensor of two invertible sheaves is locally trivial.
Local triviality never gives a global isomorphism (`L` itself is the
counterexample), so what has to be produced locally is not an isomorphism but
the LOCAL ISOMORPHY OF ONE FIXED GLOBAL MAP.  With `ev` in hand,
`isIso_of_locally_isIso` above finishes, which is exactly how
`exists_modTensor_inv` is proven below.

**This leaf is therefore EQUIVALENT to `exists_modTensor_inv`, not weaker**
(given an inverse iso, take `ev` to be it: restrictions of an iso are isos).
The cut buys the prover the global-from-local step, which is the half that is
formal, and nothing else.  It is recorded here so that nobody re-derives it.

**WHAT IT NEEDS, re-surveyed 2026-07-28 ON THE WORKER HOST, and re-checked
2026-07-29** (an earlier survey was run where `.lake/packages` is a dangling
symlink, and `AmpleSheaf.lean`'s `modTensorComm` docstring records what that
cost):

* **No internal `Hom`, confirmed twice.**  `MonoidalClosed`/`ihom`/
  `internalHom` occur nowhere under
  `Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` or under
  `Mathlib/AlgebraicGeometry/`; the only file either grep reaches is
  `ModuleCat/Monoidal/Closed.lean`, which is `ModuleCat R` itself.  Neither
  directory contains any `Dual` either.  So `L^∨` must be built by hand.
* **The GLUING route is NOT cheaper.**  Mathlib's descent machinery is
  abstract (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean`) and has **no
  instances anywhere in mathlib** — in particular it is not known here that
  `Scheme.Modules` is a stack, so "glue from the inverse cocycle" is itself a
  theory build.
* **The route that does avoid both obstructions** is the dual as a presheaf of
  COMPATIBLE FAMILIES: `L^∨(U) := {φ : ∀ V ≤ U, Γ(L,V) →ₗ[Γ(Z,V)] Γ(Z,V) //
  φ commutes with the restriction maps}`, with restriction along `U' ≤ U`
  given by forgetting.  This is STRICTLY functorial, which the naive
  `U ↦ (L.restrict U.ι ⟶ modUnit U)` is not — restriction of `𝒪`-modules is
  only pseudo-functorial (`Scheme.Modules.restrictFunctorComp` is an iso, not
  an equality), and that, not the absence of `ihom`, is the real obstruction
  to writing the dual directly.  What then remains: the sheaf condition for
  `L^∨`, its local triviality (from a trivialization of `L`), and `ev` out of
  `PresheafOfModules.Monoidal.tensorObj` through
  `PresheafOfModules.sheafificationAdjunction`.

**FOUR MORE AXES SEARCHED AND CLOSED 2026-07-29, on the worker host** (recorded
so the next prover does not re-run them; each was searched by STATEMENT SHAPE,
not only by the name one would expect):

* **No `Dual` either.**  `grep -n "def.*[Dd]ual"` over
  `Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` returns nothing, so the
  absence is not merely of the *name* `ihom`.
* **No monoidal structure on `SheafOfModules` at all.**  `MonoidalCategory` and
  `tensorObj` occur nowhere under `Mathlib/Algebra/Category/ModuleCat/Sheaf/`.
  `modTensor` above really is the only tensor product available here, and it is
  built by sheafifying the *presheaf* one.
* **`Sites/Descent/IsPrestack.lean` does have `Pseudofunctor.presheafHom`** —
  mathlib's own version of the compatible-families trick, as a presheaf of TYPES
  on `Over S` — and `IsPrestack J` is exactly "those presheaves are sheaves".
  It does not help: `grep -i instance` over every `IsPrestack`/`IsStack`
  occurrence in `Mathlib/` returns **zero instances**, so descent of morphisms is
  as instance-free as effectivity of descent.  Both halves of the descent
  machinery are abstract-only at this pin.
* **The quasi-coherent route exists but is not obviously shorter.**
  `Sheaf/LocallyFree.lean` has `SheafOfModules.IsLocallyFree` with
  `instance (priority := 100) [M.IsLocallyFree] : M.IsQuasicoherent`, and
  `AlgebraicGeometry/Modules/Tilde.lean` has `tilde`, `modulesSpecToSheaf` and
  `SpecModulesToSheafFullyFaithful`.  So on an AFFINE `Z` one could dualize the
  module and transport.  Two costs before that is usable: `IsInvertibleSheaf`
  (this file's own local-triviality predicate) is not mathlib's `IsLocallyFree`
  (`LocalGeneratorsData` on a site) and the bridge has to be built; and passing
  from affines back to a general `Z` is again gluing, i.e. the same obstruction.
  Recorded as OPEN, not as refuted.

**`hL` IS LOAD-BEARING AND THE STATEMENT IS FALSE WITHOUT IT**, with a
counterexample needing no geometry: take `L := 0`, the zero object of the
abelian category `Z.Modules`.  Then `modTensor 0 M` is `0` for every `M`,
while `modUnit Z` has stalk `𝒪_{Z,z} ≠ 0` at every `z`, so no `M` and no `ev`
work on any NONEMPTY `Z`.  (The hedge matters: over `Z = ∅` the category is
trivial, `IsInvertibleSheaf` is vacuously true and so is the conclusion, so
the counterexample has to name a point.)  A skyscraper `k` at a closed point
of `Spec k[u]` is a second, non-degenerate witness: it is finitely generated
and nonzero, and `k ⊗ M` is again supported at that point, never all of `𝒪`.
So this is not a formal fact about a monoidal category — it is exactly the
statement that local triviality globalises to an inverse. -/
theorem exists_modDual {Z : Scheme.{u}} {L : Z.Modules} (_hL : IsInvertibleSheaf L) :
    ∃ (M : Z.Modules) (ev : modTensor L M ⟶ modUnit Z), IsInvertibleSheaf M ∧
      ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map ev) :=
  sorry

/-- **AN INVERTIBLE SHEAF HAS AN INVERSE** (PROVEN 2026-07-29 over
`exists_modDual` and `isIso_of_locally_isIso`) — i.e. the invertible sheaves
on `Z` form a GROUP under `⊗`, which is the whole content of "`Pic Z` is a
group" and the single missing input of the relative Picard calculus below.

The proof is the whole assembly: `exists_modDual` supplies an invertible `M`
and a global pairing `ev : L ⊗ M ⟶ 𝒪_Z` that is locally an isomorphism, and
`isIso_of_locally_isIso` upgrades that to `IsIso ev`.  All the mathematics has
moved to `exists_modDual`; read ITS docstring for the survey, the route, and
the falsity audit of `hL`.

**ONE SIDE IS ENOUGH, and deliberately so.**  `modTensorComm`
(`Modularity/AmpleSheaf.lean`) makes `modTensor` symmetric, so
`modTensor M L ≅ modUnit Z` follows from the stated `modTensor L M ≅ modUnit Z`
by composing with the braiding — which is what `nonempty_iso_of_modTensor_left`
does there.  An earlier draft demanded both sides, on a since-refuted belief
that no braiding exists here; a prover should NOT reinstate that, because the
extra clause is free and therefore pure noise.

**STALE CLAIM CORRECTED (2026-07-29).**  This docstring used to read "genuinely
new, with no twin anywhere in the development … no owner and no downstream
proof".  That was true when written and false within the day: `flt-lean-337`
cut and proved the identical statement as `exists_modTensor_inverse` in
`Modularity/AmpleSheaf.lean`, over `exists_modDual` there.  Since that module
is DOWNSTREAM of this one, the two copies could not be merged by anything but a
hoist, which is what happened; the `AmpleSheaf.lean` declaration is gone and its
two consumers point here. -/
theorem exists_modTensor_inv {Z : Scheme.{u}} {L : Z.Modules} (hL : IsInvertibleSheaf L) :
    ∃ M : Z.Modules, IsInvertibleSheaf M ∧ Nonempty (modTensor L M ≅ modUnit Z) := by
  obtain ⟨M, ev, hM, hloc⟩ := exists_modDual hL
  haveI : IsIso ev := isIso_of_locally_isIso ev hloc
  exact ⟨M, hM, ⟨asIso ev⟩⟩

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

/-! ### `RelPicEquiv` IS an equivalence relation

**PROVEN over the five tensor-calculus leaves above.**  This closes the
check the ROUTE AUDIT on `exists_relPicFull` named as the one that would
"refute the note", i.e. that opens the fppf/Zariski route: with these
three lemmas the naive quotient `Pic(X_T)/Pic(T)` is a genuine quotient
SET, hence assemblable as a presheaf, hence a legitimate target for
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`.

The three docstring claims this supersedes are corrected in place above:
the module docstring's "there are no associativity, unit or symmetry
isomorphisms available, and none are used" was true when written and is
now false in its second half (the unit isomorphism is `modTensorUnitRightIso`,
and it IS used), and the `IsRelPicOf` docstring's "`RelPicEquiv` is not
proven symmetric or transitive in this module" is likewise superseded —
though the direction conventions there were chosen while it was true and
are left alone, since they cost nothing.

Note which leaf does what.  Reflexivity needs the unit isomorphisms
only, and is therefore already UNCONDITIONAL, since `modPullbackUnitIso`
and `modTensorUnitRightIso` are both proven; transitivity needs
associativity and the pullback/tensor interchange; symmetry is the only
one that needs inverses.

**Corrected 2026-07-29.**  "The module docstring's claim was false in its
second half" understates it: the SYMMETRY isomorphism is free at this pin
too, not merely the unit one — see the tensor-calculus section header for
the two declarations, compiler-checked, that produce it.  So of the three
coherence isomorphisms named in the superseded sentence, exactly ONE —
associativity — is genuinely missing.  Nothing in this section changes as
a result (`relPicEquiv_symm` needs `exists_modTensor_inv` either way);
the correction matters downstream, where `exists_abelJacobiPoint` would
otherwise be priced as needing a braiding leaf. -/

section RelPicEquivIsEquivalence

variable {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)

/-- **`RelPicEquiv` is reflexive**: take `N = 𝒪_T`. -/
theorem relPicEquiv_refl (L : (curveBaseChange strX g).Modules) :
    RelPicEquiv strX g L L := by
  refine ⟨modUnit T, isInvertibleSheaf_modUnit T, ⟨?_⟩⟩
  refine (modTensorUnitRightIso L).symm ≪≫ ?_
  exact modTensorMapIso (Iso.refl L)
    (modPullbackUnitIso (curveBaseChangeProj strX g)).symm

/-- **`RelPicEquiv` is symmetric**: replace `N` by its inverse. -/
theorem relPicEquiv_symm {L L' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') : RelPicEquiv strX g L' L := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨N', hN', ⟨u⟩⟩ := exists_modTensor_inv hN
  refine ⟨N', hN', ⟨?_⟩⟩
  have step : modTensor L (modPullback (curveBaseChangeProj strX g) N')
      ≅ modTensor (modTensor L' (modPullback (curveBaseChangeProj strX g) N))
          (modPullback (curveBaseChangeProj strX g) N') :=
    modTensorMapIso e (Iso.refl _)
  refine ?_ ≪≫ step.symm
  refine (modTensorUnitRightIso L').symm ≪≫ ?_ ≪≫
    (nonempty_modTensor_assocPic L' (modPullback (curveBaseChangeProj strX g) N)
      (modPullback (curveBaseChangeProj strX g) N')).some.symm
  refine modTensorMapIso (Iso.refl L') ?_
  refine (modPullbackUnitIso (curveBaseChangeProj strX g)).symm ≪≫ ?_
  refine (modPullbackMapIso (curveBaseChangeProj strX g) u).symm ≪≫ ?_
  exact (nonempty_modPullback_modTensorPic (curveBaseChangeProj strX g) N N').some

/-- **`RelPicEquiv` is transitive**: multiply the two twists. -/
theorem relPicEquiv_trans {L L' L'' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') (h' : RelPicEquiv strX g L' L'') :
    RelPicEquiv strX g L L'' := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨N', hN', ⟨e'⟩⟩ := h'
  refine ⟨Fermat.modTensor N' N, isInvertibleSheaf_modTensorPic hN' hN, ⟨?_⟩⟩
  refine e ≪≫ modTensorMapIso e' (Iso.refl _) ≪≫ ?_
  refine (nonempty_modTensor_assocPic L'' (modPullback (curveBaseChangeProj strX g) N')
    (modPullback (curveBaseChangeProj strX g) N)).some ≪≫ ?_
  exact modTensorMapIso (Iso.refl L'')
    (nonempty_modPullback_modTensorPic (curveBaseChangeProj strX g) N' N).some.symm

/-- **The relative Picard relation is an equivalence relation** — the
hypothesis both representability leaves below now receive in hand. -/
theorem relPicEquiv_equivalence : Equivalence (RelPicEquiv strX g) :=
  ⟨relPicEquiv_refl strX g, relPicEquiv_symm strX g, relPicEquiv_trans strX g⟩

end RelPicEquivIsEquivalence

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

/-- **`pstr : P ⟶ S` represents the FULL relative Picard functor
`Pic_{X/S}`** — every invertible sheaf on `X_T`, not just the
degree-zero ones.

This is `IsRelPicZeroOf` with two changes, and both are forced by what
the FULL Picard scheme is:

* a **`surj` field** is added — *every* invertible sheaf on `X_T` is
  classified.  This is the field the atomicity audit below names as the
  one thing that would distinguish `Pic` from `Pic⁰`, and it is why
  `IsRelPicZeroOf` deliberately does not have it;
* the group law (`sheaf_zero`, `sheaf_add`), the Abel–Jacobi fields
  (`aj`, `aj_spec`, `aj_pre`, `aj_base`) and the `AbelianSchemeStruct`
  are all **dropped**.  Dropping them costs nothing: `inj` and `surj`
  together say that `sheaf` is a natural BIJECTION
  `Hom_S(T, P) ≅ Pic(X_T)/Pic(T)`, so `P` is pinned by Yoneda and its
  group law — the tensor product of invertible sheaves — is determined
  rather than assumed.  `Pic` is not proper, so it could not carry an
  `AbelianSchemeStruct` in any case.

**Not vacuous, and no junk witness.**  `inj` alone is satisfied by every
scheme whose functor of points is a singleton (send everything to `𝒪`);
`surj` alone by `Pic` and by anything mapping onto it.  Together they
force `P(T) ≅ Pic(X_T)/Pic(T)` naturally in `T`, which by Yoneda
determines `P` up to unique isomorphism over `S`.  In particular the
trivial witness `P = S`, `pstr = 𝟙 S` — the one that makes every field
of `IsRelPicZeroOf` except `inj` free, because `RelPoint (𝟙 S) g` is a
singleton — fails `surj` at any curve of positive genus, already at
`T = X`, `g = strX`: `sheaf` then has a single value, while
`Pic(X ×_S X)/Pic(X)` contains the class of `𝒪(Δ) ⊗ 𝒪(−o_X)` and the
trivial class, which are distinct for `g ≥ 1`.  That is the same check
the module docstring records for `IsRelPicZeroOf`, transported to the
larger functor.

`RelPicEquiv` is not proven symmetric or transitive in this module —
that would need a unitor, an inverse and an associator for `modTensor`,
none of which is built here — so the direction of each occurrence is
part of the statement.  (**Amended 2026-07-28**: it now IS proven an
equivalence relation, by `relPicEquiv_equivalence`, over five named
leaves; the unitor is no longer among them, being PROVEN as
`modTensorUnitRightIso`.  The direction conventions below were chosen while
this paragraph was true and are deliberately left alone — they cost
nothing and changing them would churn every consumer.)  Both fields are
written in the same direction as
the corresponding field of `IsRelPicZeroOf` (`sheaf p` on the left), and
classically the relation IS an equivalence, so nothing is lost.

The base point `o` does not appear: the naive quotient
`Pic(X_T)/Pic(T)` is stated directly, and it is only the *theorem* that
this quotient is the relative Picard functor (BLR 8.1/4) which needs the
section. -/
structure IsRelPicOf {X P S : Scheme.{u}} (strX : X ⟶ S) (pstr : P ⟶ S) where
  /-- the invertible sheaf on `X_T` classified by a `T`-point of `P` -/
  sheaf : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint pstr g → (curveBaseChange strX g).Modules
  /-- the classified sheaves are invertible -/
  invertible : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g), IsInvertibleSheaf (sheaf p)
  /-- `P ↪ Pic_{X/S}` is a monomorphism of functors -/
  inj : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g),
    RelPicEquiv strX g (sheaf p) (sheaf q) → p = q
  /-- `P ↠ Pic_{X/S}`: every invertible sheaf on `X_T` is classified -/
  surj : ∀ {T : Scheme.{u}} {g : T ⟶ S} (L : (curveBaseChange strX g).Modules),
    IsInvertibleSheaf L → ∃ p : RelPoint pstr g, RelPicEquiv strX g (sheaf p) L
  /-- the classification is natural in the test object -/
  sheaf_pre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (p : RelPoint pstr g),
    RelPicEquiv strX g' (sheaf (RelPoint.pre h hg p))
      (modPullback (curveBaseChangeMap strX h hg) (sheaf p))

/-! ### The group law on the points of `Pic`, derived rather than assumed

The `IsRelPicOf` docstring above argues that dropping `sheaf_zero` and
`sheaf_add` "costs nothing", because `inj` and `surj` pin `P` by Yoneda
and its group law is then determined.  That argument is **carried out**
here rather than left as prose: `zeroPoint` and `addPoint` are the
determined operations, and `sheaf_zeroPoint` / `sheaf_addPoint` are the
two identities `IsRelPicZeroOf` asks for as fields.  Both are PROVEN.

They are obtained by choice from `surj`, and they are the CORRECT
operations rather than arbitrary choices because `inj` makes the point
they name unique — a fact a consumer needs and can prove on the spot,
since `inj` is a field of the same structure.

`addPoint` is where `isInvertibleSheaf_modTensorPic` is consumed: `surj`
only classifies INVERTIBLE sheaves, so the tensor product of two
classified sheaves has to be known invertible before it has a point.
That is the whole reason that leaf is stated above. -/

namespace IsRelPicOf

variable {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S} (hP : IsRelPicOf strX pstr)

/-- **The origin of `Pic`**: the point classifying `𝒪_{X_T}`. -/
noncomputable def zeroPoint {T : Scheme.{u}} (g : T ⟶ S) : RelPoint pstr g :=
  (hP.surj (modUnit _) (isInvertibleSheaf_modUnit _)).choose

/-- `zeroPoint` classifies the trivial class (PROVEN) — the `sheaf_zero`
field of `IsRelPicZeroOf`, at the level of `Pic`. -/
theorem sheaf_zeroPoint {T : Scheme.{u}} (g : T ⟶ S) :
    RelPicEquiv strX g (hP.sheaf (hP.zeroPoint g)) (modUnit _) :=
  (hP.surj (modUnit _) (isInvertibleSheaf_modUnit _)).choose_spec

/-- **The group law of `Pic`**: the point classifying `L_p ⊗ L_q`. -/
noncomputable def addPoint {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g) :
    RelPoint pstr g :=
  (hP.surj (modTensor (hP.sheaf p) (hP.sheaf q))
    (isInvertibleSheaf_modTensorPic (hP.invertible p) (hP.invertible q))).choose

/-- `addPoint` classifies the tensor product (PROVEN) — the `sheaf_add`
field of `IsRelPicZeroOf`, at the level of `Pic`. -/
theorem sheaf_addPoint {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g) :
    RelPicEquiv strX g (hP.sheaf (hP.addPoint p q))
      (modTensor (hP.sheaf p) (hP.sheaf q)) :=
  (hP.surj (modTensor (hP.sheaf p) (hP.sheaf q))
    (isInvertibleSheaf_modTensorPic (hP.invertible p) (hP.invertible q))).choose_spec

end IsRelPicOf

/-! ### The Zariski-local decomposition of FGA 232

`exists_relPicOf_of_hasUniversallyTrivialPushforward` below is cut into
the two halves BLR itself uses, and the cut is along the BASE:

* over an affine open `V ⊆ S` the curve becomes **projective**, which is
  the hypothesis FGA 232 / BLR 8.2/1 is actually stated under —
  `exists_relPicOf_isAffineOpen`;
* representability is **Zariski-local on the base**, so the local Picard
  schemes glue — `exists_relPicOf_of_forall_isAffineOpen`.

**Why affineness of `V` is the load-bearing hypothesis of the first half,
and not decoration.**  `f_*ω_{X/S}` is locally free of finite rank, so the
genus is a LOCALLY CONSTANT function on `S`.  On a quasi-compact `S` a
locally constant function has finite image (its fibres are an open cover),
so `V` decomposes as a FINITE disjoint union of opens `V_g` of constant
genus, and on each `𝒪((2g+1)·o)` is relatively very ample.  That is what
makes `X_V ⟶ V` projective.  Over a base that is merely a scheme the
decomposition can be infinite and there is no single relatively very ample
sheaf to write, which is exactly why FGA is stated for projective
morphisms and why the reduction has to happen first.

**Why the geometric hypotheses are carried into the SECOND half too, and
dropping them makes it FALSE.**  Gluing the `P_V` into a scheme `P` needs
only Yoneda: each `P_V` represents `T ↦ Pic(X_T)/Pic(T)` on `V`-schemes, so
the comparison isomorphisms `P_V ×_V (V ⊓ W) ≅ P_W ×_W (V ⊓ W)` and their
cocycle conditions are *forced* by uniqueness of a representing object,
and the bare existence statements in `_hloc` — with no compatibility data
— really do suffice.  What is NOT free is the `surj` field of the glued
`P`: given `L` on `X_T` one gets classifying points `p_i` over a cover of
`T` and glues them to `p : T ⟶ P`, but concluding `sheaf p ≡ L` GLOBALLY
from `sheaf p|_{T_i} ≡ L|_{T_i}` is precisely the statement that
`T ↦ Pic(X_T)/Pic(T)` is a Zariski sheaf, i.e. BLR 8.1/4, i.e. the
exactness of `0 ⟶ Pic T ⟶ Pic X_T ⟶ P_{X/S}(T)`.  That needs `_hpush` and
the section `_o`.  Drop either and the second half is false, not merely
unprovable: for `X = S ⊔ S` the sequence breaks and a class can be locally
but not globally in the image.

The `sheaf` field is the same obligation wearing a different hat, and it
is worth naming separately because it is the one a prover meets FIRST: to
define `sheaf p` for `p : T ⟶ P` one wants a POINCARÉ bundle on `X_P`,
i.e. an actual invertible sheaf representing the universal class, and that
representative exists exactly because the section kills the obstruction in
`Br T`.  Gluing local representatives `L_i` by hand does not work — they
agree only up to a twist by `Pic(T_i ⊓ T_j)`, so there is no cocycle to
glue along.  Both routes therefore consume `_o` and `_hpush`; neither is a
way around them.

**Neither half is the other in disguise.**  `_hloc` cannot be instantiated
at `V = ⊤` to recover the conclusion, because `IsAffineOpen (⊤ : S.Opens)`
is exactly `IsAffine S`, which is not assumed; and the first half cannot be
proved from the second, which consumes it. -/

/-- **THE RELATIVE PICARD SCHEME OVER AN AFFINE OPEN OF THE BASE** — FGA
exposé 232 / BLR 8.2/1 in the form it is actually stated, i.e. for a
PROJECTIVE morphism (sorry leaf).

This is where all of the geometry of the parent leaf lives.  The
hypotheses are the parent's, stated for the original `strX` rather than
for the restricted curve on purpose: the base-change stability of
`IsProper`, `SmoothOfRelativeDimension 1`, `GeometricallyConnected`,
`HasUniversallyTrivialPushforward` and of the section is routine and
belongs to whoever proves this, not to the assembly, and putting it here
keeps the assembly free of transport.

So a prover owes, in order: (i) `X ×_S V ⟶ V` is again a proper smooth
geometrically connected relative curve with a section, over an AFFINE
base; (ii) it is therefore projective, by the finite constant-genus
decomposition and `𝒪((2g+1)·o)` (see the section note above); (iii) FGA
232 for a projective flat morphism with integral geometric fibres — the
geometric fibres here are smooth connected curves over an algebraically
closed field, hence integral; (iv) BLR 8.1/4 to identify the fppf sheaf
with the naive quotient, which is what makes `surj` statable without
sheafification.

Steps (i)–(ii) are the cheap ones; (iii) is Grothendieck's theorem and is
the only genuinely research-scale obligation in this file. -/
theorem exists_relPicOf_isAffineOpen {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (V : S.Opens) (_hV : IsAffineOpen V) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ (V : Scheme.{u})),
      Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) :=
  sorry

/-- **REPRESENTABILITY OF THE RELATIVE PICARD FUNCTOR IS ZARISKI-LOCAL ON
THE BASE** (sorry leaf) — Stacks 01JJ for the gluing, BLR 8.1/4 for the
descent of `surj`.

The affine opens cover `S`, so `_hloc` is a genuine cover hypothesis.  See
the section note above for why the existence statements in `_hloc` need
carry no compatibility data (Yoneda supplies it) and why the geometric
hypotheses are nevertheless load-bearing here (they are what makes
`T ↦ Pic(X_T)/Pic(T)` a Zariski sheaf, hence what lets `surj` be checked
locally).

**This is the half that is approachable now.**  It needs no FGA and no new
geometry: `AlgebraicGeometry.Scheme.GlueData` for the construction, and
then four field-by-field checks on `IsRelPicOf`, of which `inj` and
`sheaf_pre` are local by inspection and `surj` is the BLR 8.1/4 step.  Note
the universe warning on the parent's ROUTE AUDIT before reaching instead
for `Scheme.LocalRepresentability.isRepresentable`: that takes a
`Type u`-valued sheaf and the naive quotient is a priori `Type (u+1)`. -/
theorem exists_relPicOf_of_forall_isAffineOpen {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (P : Scheme.{u}) (pstr : P ⟶ (V : Scheme.{u})),
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S), Nonempty (IsRelPicOf strX pstr) :=
  sorry

/-- **EXISTENCE OF THE RELATIVE PICARD SCHEME** — FGA exposé 232,
Bosch–Lütkebohmert–Raynaud, *Néron Models*, 8.2/1 (**PROVEN 2026-07-29
over `exists_relPicOf_isAffineOpen` and
`exists_relPicOf_of_forall_isAffineOpen`** — formerly a bare sorry leaf;
see the section note above those two for the cut and for what each owes).

**`_hequiv` is now REDUNDANT and is kept only for the callers.**
`relPicEquiv_equivalence` above proves it UNCONDITIONALLY, so it can be
supplied at any call site with no hypotheses at all and it constrains
nothing.  It is deliberately not removed: `exists_relPicFull` below passes
it explicitly, the hypothesis is harmless, and deleting an input from a
released signature churns consumers for no mathematical gain.  A future
reader must not read it as a live obligation — it is not one, and the
proof below does not use it.

For a smooth proper geometrically connected relative curve with a
section, the naive quotient `T ↦ Pic(X_T)/Pic(T)` is representable by an
`S`-scheme.  Two classical inputs, and both are genuinely used:

* representability of `Pic_{X/S}` as an fppf sheaf, which for a
  projective flat morphism with integral geometric fibres is FGA 232 /
  BLR 8.2/1.  `strX` is proper and smooth of relative dimension 1, hence
  Zariski-locally on `S` projective, and its geometric fibres are smooth
  connected curves, hence integral;
* BLR 8.1/4: because `strX` has the section `o` and satisfies
  `f_*𝒪_X = 𝒪_S` universally (geometric connectedness), the fppf sheaf
  is ALREADY the naive quotient, with no sheafification.  This is what
  makes the conclusion statable with no sheafification.

**THE `f_*𝒪_X = 𝒪_S` HALF IS ALREADY PROVEN IN THIS PROJECT — do not
rebuild it** (checked 2026-07-28 against the compiler, not against a
docstring).  It is

    AlgebraicGeometry.hasUniversallyTrivialPushforward_of_isProper_of_smooth
      (f) [IsProper f] [Smooth f] [GeometricallyConnected f] :
        HasUniversallyTrivialPushforward f

in `Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`
(namespace `AlgebraicGeometry`), and its three instance hypotheses are
exactly this leaf's three: `Smooth strX` comes from `_hsmooth` by
`SmoothOfRelativeDimension.smooth`
(`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`).

Precisely: it carries **no direct `sorry`**, but it is still TRANSITIVELY
sorried through that file's own leaves.

**RE-COUNTED 2026-07-30 (third correction).**  This paragraph has now been
wrong three times, each time in a different way, and the third error was
introduced by a correction of the second.  It first named
`finiteType_appTop_of_isProper` and
`surjective_quotientMap_appTop_of_isIso_appTop_fiber`; it was then corrected
to a set of THREE at `{1225, 1534, 1666}` naming
`inf_smul_top_le_smul_ker_of_forall_isMaximal_comap_le` and
`exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber`, both of
which have since been PROVEN.  **That second correction also asserted that
`surjective_quotientMap_appTop_of_isIso_appTop_fiber` "does not exist in
that file", and that assertion is FALSE** — the declaration is there and is
PROVEN (2026-07-28).  What was true of it is only that it is not an open
leaf, and "not on the direct-sorry list" was written down as "not a
declaration"; the two are different claims and a `grep` separates them in
one command.  Do not repeat that inference: a name absent from a leaf list
is a name to `grep`, not a name to declare nonexistent.

The file's direct-sorry set is, as of 2026-07-30, **TWO**:
`adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` and
`eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`.  Note the first of
those replaced `finiteType_appTop_of_isProper` the same day — that theorem
was PROVEN over it — so a fourth version of this list would have been wrong
too.  **Line numbers in this paragraph have been dropped deliberately** —
every version of them has gone stale within a day, and the names are what a
`grep` can check.  Read the count off the compiler's warning set, never off
this docstring.

That distinction does not change the advice: the statement is available to
CONSUME here, and those leaves belong to `ProperPushforward.lean`'s
owner, not to this one.  Rebuilding the argument in this module would
duplicate it and inherit the same leaves.

**AMENDED 2026-07-29 — that import is now IN THE HEADER, and this
paragraph used to say the opposite.**  It formerly read "It is NOT in this
module's import cone … whoever attacks this leaf must add
`public import Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward` …
It is deliberately not added here".  `exists_relPicFull` below became the
consumer and added it, so the instruction is discharged and the "NOT in
the cone" claim is false.  Verified by `grep -n ProperPushforward` on this
file's header, not by reading a docstring.  The import remains
**cycle-free**: `ProperPushforward.lean`'s only project import is
`Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced`.

Its three own direct leaves at the merge base of 2026-07-29 are at
`ProperPushforward.lean:1225`, `:1534` and `:1666` — so the statement is
available to CONSUME here and is transitively sorried through them; they
belong to that file's owner, not to this one.

So what `exists_relPicFull` genuinely still owes is the FIRST bullet
only — representability itself — plus the passage from
`HasUniversallyTrivialPushforward` to "the naive quotient is the Picard
functor".  **The check that would refute this note**: `grep -n
hasUniversallyTrivialPushforward_of_isProper_of_smooth
Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean` and confirm
the declaration is not in the build's `declaration uses 'sorry'` set.

This is the half of `exists_relPicZero` that constructs a scheme at all.
The other half — cutting `Pic⁰` out of `Pic` and proving it proper and
smooth — is `exists_relPicZero_of_isRelPicOf`.

**FAITHFULNESS RE-AUDITED INDEPENDENTLY 2026-07-28 (second reader): TRUE
as written.**  The two clauses that could have made it false were checked
separately, and one correction to the note above came out of it.

*`surj` is faithful, and it is faithful for EVERY `T`* — not merely for
affine or noetherian test objects.  That is BLR 8.1/4, whose hypothesis
`𝒪_{S'} ⟶ f_{S'*}𝒪_{X_{S'}}` an isomorphism for every `S' ⟶ S` is here
IMPLIED rather than assumed: `_hsmooth` gives flat with geometrically
reduced fibres, `_hconn` gives geometrically connected ones, `_hproper`
gives properness, and those together force it.  The exact sequence
`0 ⟶ Pic T ⟶ Pic X_T ⟶ P_{X/S}(T) ⟶ Br T ⟶ Br X_T` then has its last map
injective *because of the section*, which is what collapses the fppf
sheaf onto the naive quotient.  Drop `_hconn` and `surj` becomes FALSE
rather than merely unprovable: for `X = S ⊔ S` one has
`f_*𝒪_X = 𝒪_S × 𝒪_S`, the sequence breaks, and classes not of the form
`𝒪(D)` for a relative `D` are unclassified.

*`P` is required to be a SCHEME, not an algebraic space, and that is
true here* — but the reason is NOT only BLR 8.1/4, which is why the
"only place the section is used" clause that stood here has been
removed.  `f_*ω_{X/S}` is locally free of finite rank, so the genus is
locally constant and `S` is the disjoint union of opens `S_g`; on each,
`𝒪(n · o)` with `n = 2g + 1` is relatively very ample, so `X_{S_g} ⟶ S_g`
is PROJECTIVE and FGA 232 applies in the form BLR 8.2/1 states it; the
local Picard schemes then glue because `Pic` is a Zariski sheaf on `S`.
So the section is load-bearing TWICE — once for the naive quotient, once
for relative projectivity — and a future prover who drops it loses
representability by a scheme, not just the quotient presentation.

**ROUTE AUDIT 2026-07-28 — the pin has MOVED, and the older notes here
name the wrong gate.**

* "a pin with no site theory" is **FALSE** at `a3364fa`.  Mathlib has
  `AlgebraicGeometry.fppfTopology` and `fpqcTopology`
  (`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`), both with a
  `Subcanonical` instance, and a Zariski-gluing representability
  criterion in `Mathlib/AlgebraicGeometry/Sites/Representability.lean`:
  `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` takes a
  `Type u`-valued sheaf `F` for `Scheme.zariskiTopology`, a family
  `yoneda.obj (X i) ⟶ F` of relatively representable open immersions that
  is jointly (locally) surjective, and returns `F.IsRepresentable`
  (Stacks 01JJ).  That is exactly the gluing step the disjoint-union
  argument above needs, already done.  So the fppf route is not blocked
  by the absence of a site.
* **The true gate is the missing MONOIDAL STRUCTURE on
  `SheafOfModules`.**  `grep -rn "MonoidalCategory"
  Mathlib/Algebra/Category/ModuleCat/Sheaf/` returns EMPTY at this pin.
  `modTensor` supplies the object part only, so `RelPicEquiv` has no
  unitor, no associator and no inverses, and is therefore not known to be
  reflexive, symmetric or transitive.  Consequently the relative Picard
  presheaf cannot be assembled as a `CategoryTheory.Functor` at all, and
  none of the representability machinery above can be pointed at it.
  **The check that refutes this note**: prove `RelPicEquiv` is an
  equivalence relation — which needs `L ⊗ pr^*𝒪 ≅ L`, an inverse for an
  invertible sheaf, and associativity — and the fppf/Zariski route opens.

  **THAT CHECK WAS RUN 2026-07-28 AND THE NOTE IS HALF-REFUTED.**  The
  grep is still accurate — there is no `MonoidalCategory` instance on
  `SheafOfModules` — but the inference drawn from it was too strong on
  two counts.  (i) `PresheafOfModules` DOES carry a full
  `MonoidalCategory` instance, and sheafification is a functor whose
  adjunction counit is an isomorphism on sheaves, so CONGRUENCE and the
  RIGHT UNITOR are available with no new theory: `modTensorMapIso` and
  `modTensorUnitRightIso` are proven above.  (ii) `RelPicEquiv` is now proven
  reflexive, symmetric and transitive (`relPicEquiv_equivalence`) over
  five named leaves, so this route IS open, in the precise sense the
  note demanded — what is left is those five leaves, not an unbounded
  theory.  The residue of the gate is genuinely "sheafification is
  monoidal" (needed for the associator and the pullback/tensor
  interchange), plus invertibility of a tensor product and existence of
  inverses.

  **THIRD PASS 2026-07-29: the "sheafification is monoidal" residue is
  ITSELF DISCHARGED, one module downstream.**  `Modularity/AmpleSheaf.lean`
  carries a section "SHEAFIFICATION IS MONOIDAL, via
  `CategoryTheory.LocalizedMonoidal`" (`modLocW`, `modLocW_whiskerLeft`,
  `modLocW_whiskerRight`, `modTensorLocIso`) and proves
  `nonempty_modTensor_assoc` and `nonempty_modPullback_modTensor` off it.
  Checked against the compiler, not the prose: the build's
  `declaration uses 'sorry'` set for `AmpleSheaf.lean` is exactly
  `{749, 1121, 1210}`, and neither `nonempty_modTensor_assoc` (`:600`) nor
  `nonempty_modPullback_modTensor` (`:764`) is in it.  So the monoidality
  gate no longer costs a theory anywhere in the tree — it costs a HOIST,
  which is what the twins `nonempty_modTensor_assocPic` /
  `nonempty_modPullback_modTensorPic` above are waiting on.  Do not price
  it as missing machinery again.
* **A UNIVERSE OBSTRUCTION on the `isRepresentable` route, recorded
  2026-07-29 so the next reader does not walk into it.**  The bullet above
  is right that `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`
  is the gluing step one wants — but it consumes a sheaf valued in
  `Type u`, and the naive quotient is not obviously `Type u`-valued here:
  `(curveBaseChange strX g).Modules` is `SheafOfModules …`, which lives in
  `Type (u+1)`, so its set of `RelPicEquiv`-classes is a priori
  `Type (u+1)` too.  Making it `Type u`-small is a THEOREM (essentially
  `Pic = H¹(_, 𝒪ˣ)`), not a coercion, and nothing in the pin supplies it.
  That is why the cut taken below goes through a Zariski-local
  decomposition of the BASE, stated with schemes on both sides, rather
  than through a sheaf of types.
* `Mathlib/AlgebraicGeometry/Group/Abelian.lean` is **not** abelian
  schemes: it is commutativity of a proper geometrically integral group
  scheme over a FIELD.  There is still no abelian-scheme theory in the
  pin, which is why `Fermat.AbelianSchemeStruct` exists.
* Divisor theory is still entirely absent:
  `grep -rl "EffectiveCartier\|CartierDivisor\|WeilDivisor" Mathlib/`
  is EMPTY.  So the `Sym^d`/`Div^d` axis named on `exists_relPicZero`
  would have to STATE relative effective Cartier divisors before it could
  cut — see the axis inventory on `exists_relPicZero_of_isRelPicOf`.
  RE-CHECKED 2026-07-29 by SHAPE rather than by spelling, since a grep
  proves a spelling absent and not a theorem: case-insensitively over
  `Mathlib/AlgebraicGeometry/` for `cartierdivisor`, `effectivecartier`
  and `weildivisor`, plus `ls Mathlib/AlgebraicGeometry/ | grep -i div`.
  Both empty.  There is also still no `IsProjective` and no ampleness for
  MORPHISMS anywhere in `Mathlib/AlgebraicGeometry/` — which is why
  `exists_relPicOf_isAffineOpen` below has to say "affine open of the
  base" instead of "projective". -/
theorem exists_relPicOf_of_hasUniversallyTrivialPushforward {X S : Scheme.{u}} (strX : X ⟶ S)
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S), Nonempty (IsRelPicOf strX pstr) :=
  exists_relPicOf_of_forall_isAffineOpen strX hproper hsmooth hconn o hpush
    fun V hV => exists_relPicOf_isAffineOpen strX hproper hsmooth hconn o hpush V hV

/-- **EXISTENCE OF THE RELATIVE PICARD SCHEME** (PROVEN 2026-07-28 over
`exists_relPicOf_of_hasUniversallyTrivialPushforward`, discharging both
of that leaf's two extra hypotheses).

What this two-line proof buys, and why the extra hypotheses are not
ceremony:

* **`_hpush` is discharged outright.**  `f_*𝒪_X = 𝒪_S` universally is
  `AlgebraicGeometry.hasUniversallyTrivialPushforward_of_isProper_of_smooth`
  in `Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`, whose
  three instance hypotheses are exactly the three geometric hypotheses
  here (`Smooth strX` from `SmoothOfRelativeDimension.smooth`).  A
  previous note in this file identified it and deliberately left the
  import unadded because nothing consumed it; this declaration is the
  consumer, and `public import
  Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward` is now in the
  header.  It carries no direct `sorry`, though it is transitively
  sorried through that file's own leaves — as of 2026-07-30 exactly TWO,
  `adjoin_le_span_one_sup_smul_of_isIso_appTop_fiber` and
  `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber` — which belong to
  that file's owner, not to this one.  (Corrected three times; see the
  leaf docstring above for the history.  In particular the claim that
  `surjective_quotientMap_appTop_of_isIso_appTop_fiber` "does not exist"
  stood here and is FALSE — it exists and is proven; it is merely not an
  open leaf.  Line numbers deliberately omitted.)
* **`_hequiv` is discharged over five named leaves** by
  `relPicEquiv_equivalence`.  This is not ceremony either: without it
  `IsRelPicOf` is not merely hard to satisfy, it is not obviously
  SATISFIABLE at all, since `surj` produces a classifying point and
  `inj` demands it be unique, and uniqueness of a representative is
  exactly what symmetry and transitivity supply.  A prover of the leaf
  who did not have `_hequiv` would have to prove it first. -/
theorem exists_relPicFull {X S : Scheme.{u}} (strX : X ⟶ S)
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S), Nonempty (IsRelPicOf strX pstr) := by
  haveI := hproper
  haveI := hsmooth
  haveI := hconn
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth (n := 1) (f := strX)
  exact exists_relPicOf_of_hasUniversallyTrivialPushforward strX hproper hsmooth hconn o
    (AlgebraicGeometry.hasUniversallyTrivialPushforward_of_isProper_of_smooth strX)
    (fun g => relPicEquiv_equivalence strX g)

/-! ### BLR 9.4/4 — the audit written while this was ONE node

Everything down to the `DECOMPOSED 2026-07-29` paragraph was the
docstring of `exists_relPicZeroOf_of_relPicGroupLaw` while that theorem
was a `sorry`.  It is kept verbatim, demoted to a section comment,
because the survey it records — what pins `Pic⁰`, which further cuts are
vacuous, and which axes were searched and rejected, each with its price —
is exactly what a reader of the two leaves below needs, and none of it is
restated there.

**`Pic⁰` IS AN ABELIAN SCHEME, GIVEN `Pic`** —
Bosch–Lütkebohmert–Raynaud, *Néron Models*, 9.4/4.

Assuming the relative Picard scheme `P` of `strX` has been constructed
(`IsRelPicOf`), cut out its identity component and show that it is an
abelian scheme carrying the Abel–Jacobi map based at `o`.  Everything
this leaf still owes is exactly BLR 9.4/4 and its inputs:

* the connected-component-of-identity construction, which needs `P ⟶ S`
  to be smooth and separated — itself a consequence of cohomology and
  base change on the relative curve (`H²` vanishes, so `Pic` is smooth);
* properness of `Pic⁰`, i.e. the valuative criterion for line bundles on
  a relative curve;
* the `𝒪(D)` dictionary for the section divisors `[x]` and `[o]`, which
  is what produces the `aj`, `aj_spec`, `aj_pre`, `aj_base` fields.  Only
  the section case of that dictionary is needed, and `sectionIdeal`
  above already writes it.

The hypothesis is deliberately as WEAK as it can be while still pinning
`P`: no group law is assumed on `P`, because `inj` and `surj` make
`Hom_S(-, P) ≅ Pic(X_{-})/Pic(-)` a natural bijection and the group law
transports through it by Yoneda.  So this leaf is as strong as it can
be, and `exists_relPicFull` correspondingly as weak as it can be; both
are true.

**FAITHFULNESS RE-AUDITED INDEPENDENTLY 2026-07-28 (second reader): TRUE,
and the cut is NOT a relocation.**  `IsRelPicOf` neither implies nor is
implied by `IsRelPicZeroOf` — `surj` fails for `Pic⁰` at any curve of
positive genus, and the group law and the Abel–Jacobi fields are absent
from `IsRelPicOf` — so this is a genuine implication and not
`exists_relPicZero` under another name.  The hypothesis buys exactly what
BLR 9.4/4 assumes: representability of `Pic`, leaving smoothness of
`Pic ⟶ S` (`H²` vanishes on a relative curve), the identity-component
construction, and properness of `Pic⁰`.

No internal inconsistency: `aj_spec` read at `x = o` says
`sheaf (aj o) ⊗ 𝒪(−o) ∼ 𝒪(−o)`, i.e. `sheaf (aj o) ∼ 𝒪`, which is what
`aj_base` together with `sheaf_zero` independently demands.  So the
conclusion is satisfiable, and `IsRelPicOf` is inhabited (by the genuine
`Pic_{X/S}`), so the leaf is not vacuously true either.

**ATOMICITY RE-CHECKED, AND THE PARENT'S REJECTION TRANSFERS.**  The
obvious further cut — "produce `J` with everything except `aj`,
`aj_spec`, `aj_pre`, `aj_base`" — is still VACUOUS **even with `_hP` in
hand**, and this is worth stating because `_hP` looks as though it should
rule the junk witness out.  It does not: `_hP` constrains `P`, and says
nothing whatever about `J`.  So `J = S`, `jstr = 𝟙 S` survives exactly as
it did on the parent, `RelPoint (𝟙 S) g` being a singleton.  Dually,
"produce `J` with everything except properness and smoothness" is refuted
by `P` itself, which is the rejection already recorded on
`exists_relPicZero`.  What pins `Pic⁰` inside `Pic` is precisely the
conjunction *proper + open + contains the Abel–Jacobi image* — for a
curve `NS` is `ℤ`, hence torsion-free, so `Pic⁰ = Pic^τ` and there is no
other proper open subgroup scheme — and `IsRelPicZeroOf` already IS that
conjunction.  Hence no proper sub-package of its fields pins the object.

**AXES SEARCHED 2026-07-28 AND NOT TAKEN, each with its price**, recorded
so the next reader need not re-run the survey (and per the standing rule
that an irreducibility verdict is only as wide as the axis searched):

* *`Sym^d` / `Div^d`*, the axis `exists_relPicZero`'s audit anticipated.
  Still blocked, and now measured: mathlib has NO divisor theory at all
  at `a3364fa`, so relative effective Cartier divisors must be STATED
  first — a datum carrying a closed subscheme of `X_T` whose ideal sheaf
  is invertible and which is finite locally free of degree `d` over `T`,
  plus its functor-of-points naturality.  That much is statable.  What
  makes the axis a poor trade is the *second* half: "given `Div^d`
  representable, `Pic` is its quotient" still carries cohomology and base
  change and the projective-bundle argument, i.e. nearly all of BLR
  8.2/1.  The cut would isolate the Hilbert-scheme input and little else.
* *Zariski-local-on-`S`*: "representable over each member of an open
  cover of `S`" plus "glue".  Rejected **as it would naturally be
  written**, and the trap is worth recording: the obvious hypothesis
  "`S` affine" is NOT enough, because the genus is only *locally*
  constant and an affine scheme can have non-open connected components,
  so the local half would be FALSE as stated.  The correct hypothesis is
  constant genus, i.e. the disjoint-union decomposition described under
  `exists_relPicFull`; and mathlib's `Sites/Representability.lean`
  supplies the gluing half, so this axis becomes live the moment the
  functor can be built at all.
* *Degree decomposition `Pic ≅ ℤ_S × Pic⁰`*, available here because the
  section trivialises `Pic^d ≅ Pic⁰` by `L ↦ L(−d·o)`.  True, but it
  derives `exists_relPicFull` FROM `Pic⁰`: it inverts this cut rather
  than refining it, and would leave the composition circular.
* *Transport of the classification data along `J ⟶ P`* — mechanical in
  Lean, but it leaves `_hP`-plus-everything on the other side, so it is
  the "relocation with extra steps" shape rather than a cut.

Everything above is gated on the same thing as `exists_relPicFull`: the
missing monoidal structure on `SheafOfModules`.  See that leaf's ROUTE
AUDIT for the grep that establishes it and the check that refutes it.

**Amended 2026-07-28**: the last paragraph is now only half true.  The
gate on `SheafOfModules` has been split into the five named leaves in
the tensor-calculus section, one of which
(`modTensorUnitRightIso`, the right unitor) turned out to be available at
this pin and is PROVEN.  What remains gated is the associator and the
pullback/tensor interchange — both instances of "sheafification is
monoidal" — plus invertibility of a tensor product and the existence of
inverses.

**DECOMPOSED 2026-07-29, and the leaf is now PROVEN.**  Everything above
this paragraph is the audit written while it was a sorry; it is left
intact because the survey it records is still what a reader needs.  What
changed is that the leaf is no longer atomic: see the section heading
immediately below for the two halves it split into and why they are
independent.  `_hproper`, `_hsmooth`, `_hconn`, `_hpush` and `_hequiv`
are passed on to `exists_relPicZeroSubgroup`; `_hzero` and `_hadd` are
consumed HERE, in the `sheaf_zero` and `sheaf_add` fields, which is the
concrete sense in which "the group law is already supplied". -/

/-! ### BLR 9.4/4: the `𝒪(D)` dictionary and the identity component

`exists_relPicZeroOf_of_relPicGroupLaw` receives `Pic` together with the
group law on its points, so what it still owes is exactly the two halves
BLR 9.4/4 is made of.  They are **independent of each other**, which is
why they are cut apart rather than left as one node:

* the **`𝒪(D)` dictionary** — `exists_abelJacobiPoint` — the Abel–Jacobi
  map `x ↦ [x] − [o]` as a map into the points of `Pic`.  No identity
  component enters it: it is a statement about `sectionIdeal` on a smooth
  relative curve, plus `surj`;
* the **geometry** — `exists_relPicZeroSubgroup` — cutting `Pic⁰` out of
  `Pic` and showing it is proper, smooth and geometrically connected over
  `S`.  It takes the Abel–Jacobi map as an INPUT, because "contains the
  Abel–Jacobi image" is one of the three things that pin `Pic⁰` inside
  `Pic` (the audit above records the other two).

The assembly of `IsRelPicZeroOf` out of the two is written below and is
PROVEN; it is pure functor-of-points bookkeeping, and every field of the
structure is discharged by one rewrite along a clause of
`exists_relPicZeroSubgroup` followed by the corresponding fact about
`Pic`.

**Why `incl` rather than a subscheme.**  `exists_relPicZeroSubgroup`
delivers `Pic⁰ ⊆ Pic` as a natural INJECTION ON POINTS rather than as a
monomorphism of schemes.  By Yoneda the two are equivalent, and the
point-level form is what the assembly consumes; stating it as an open
immersion would force the caller to convert, and would add an `IsIso`/
`IsOpenImmersion` obligation that no field of `IsRelPicZeroOf` reads. -/

/-- **THE ABEL–JACOBI MAP INTO `Pic`** (sorry leaf, cut 2026-07-29) — the
`𝒪(D)` dictionary for section divisors on a relative curve, which is BLR
9.4/4's first input and the only place `sectionIdeal` is consumed.

Classically: for `x` a `T`-point of the curve, `𝒪(x − o)` is an
invertible sheaf on `X_T`, so `surj` classifies it, and the resulting
point of `Pic` is natural in `T` and sends `o` to the origin.

**ROUTE, worked out 2026-07-29 far enough to price it; do not re-derive
the survey.**  Written out, the construction at one `(T, g)` is
`M := 𝒪(−o) ⊗ 𝒪(−x)⁻¹`, then `hP.surj M`, and `aj` is `choose` over
`(T, g, x)`.  So the route is fixed; what follows is what it costs.

*Two genuinely NEW geometric obligations, both about `sectionIdeal`
alone, and both small enough to dispatch on their own once there is a
consumer for them:*

* **`𝒪(−σ)` is invertible** for `σ` a section of a smooth relative curve
  — the regular-immersion statement, i.e. a section of a smooth curve is
  an effective Cartier divisor.  Nothing in the pin says so (there is no
  divisor theory at `a3364fa`), so it has to come out of `sectionIdeal`'s
  definition as a kernel.  Consumed for `Ix := 𝒪(−x)` and for
  `Io := 𝒪(−o_T)`;
* **`𝒪(−σ)` commutes with base change**,
  `φ^* 𝒪(−x) ≅ 𝒪(−x_{T'})` for `φ = curveBaseChangeMap strX h hg`.  Flat
  base change for that kernel.  Needed only by `aj_pre`.

*And the tensor bookkeeping, which is NOT free and is the reason this
leaf was left atomic rather than cut a third time.*  `aj_spec` is cheap:
`hP.sheaf (aj x) ∼ Io ⊗ Jx` (where `Ix ⊗ Jx ≅ 𝒪` from
`exists_modTensor_inv`), tensor on the right by `Ix`, then
`(Io ⊗ Jx) ⊗ Ix ≅ Io ⊗ (Jx ⊗ Ix) ≅ Io ⊗ 𝒪 ≅ Io` — associativity, one
braiding (see the tensor-calculus header: the braiding is FREE at this
pin), and the right unitor.  It needs two helpers that do not exist yet
and are each a few lines: `RelPicEquiv` is preserved by an isomorphism,
and `RelPicEquiv` is a congruence for `⊗` on the right (proof:
`(L' ⊗ π^*N) ⊗ M ≅ (L' ⊗ M) ⊗ π^*N`, the middle-four interchange).

`aj_pre` is where the cost is, and the blocking piece is neither of the
two geometric obligations above.  It needs `RelPicEquiv` to be preserved
by `φ^*` — and *that* needs **`IsInvertibleSheaf (modPullback h N)`**,
which is absent from this module.  (`RelPicEquiv` twists by `π^*N` with
`N` invertible on the BASE, and pushing the relation through `φ^*`
rewrites the twist as `π_{g'}^*(h^* N)` — via `pullback.lift_snd` for
`φ ≫ π_g = π_{g'} ≫ h`, then `modPullbackCompIso` and
`modPullbackCongrIso` — so the new twist is invertible only if pullback
preserves invertibility.)  That statement is about the tensor-calculus
section rather than about Picard theory, and `AmpleSheaf.lean` already
carries the restriction/`morphismRestrict` machinery a proof of it would
use.  **Whoever takes this leaf should state and prove it in the
tensor-calculus section above, next to `isInvertibleSheaf_modTensorPic`,
before touching `aj_pre`.**

`aj_base` needs none of it: it is `hP.inj` applied to `𝒪(o − o) ∼ 𝒪`.

One identity that looks like nothing and is not `rfl`:
`RelPoint.pre h hg (relBasePoint o g) = relBasePoint o g'`.  Both sides
are `⟨h ≫ (g ≫ o.1), _⟩` and `⟨(h ≫ g) ≫ o.1, _⟩`; it is `Subtype.ext`
plus `Category.assoc`, and `aj_pre` cannot start without it.

**Pinned.**  The `∃` looks under-pinned — an adversary might try to
replace `aj` by any other family of points — but `hP.inj` makes the point
satisfying the first clause UNIQUE, so the clause determines `aj`
pointwise and the other two clauses are then theorems about it rather
than extra freedom.  This is the same argument that makes
`IsRelPicOf.addPoint` well defined.

**Not vacuous.**  At `g ≥ 1` the map is non-constant (already at `T = X`,
`g = strX`, comparing the diagonal with the constant section `o_X`), and
at `g = 0` it is constant with value the origin; both are consistent with
the three clauses, and neither is excluded, because this leaf does not
claim injectivity of `aj` — that is false at `g = 0` and is not needed
anywhere. -/
theorem exists_abelJacobiPoint {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (o : RelPoint strX (𝟙 S)) (hP : IsRelPicOf strX pstr) :
    ∃ aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g,
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
          RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
            (sectionIdeal (relSection (relBasePoint o g)))) ∧
        (∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
            (x : RelPoint strX g),
            aj T' g' (RelPoint.pre h hg x) = RelPoint.pre h hg (aj T g x)) ∧
        aj S (𝟙 S) o = hP.zeroPoint (𝟙 S) :=
  sorry

/-- **`Pic⁰` IS AN ABELIAN SCHEME INSIDE `Pic`** (sorry leaf, cut
2026-07-29) — BLR 9.4/4's geometric half, and the whole of what that
theorem is usually cited for.

Given `Pic` and the Abel–Jacobi map into it, cut out the identity
component and show it is an abelian scheme over `S`.  Concretely the
three classical steps:

* `Pic ⟶ S` is **smooth and separated** — this is where `_hpush`
  (`f_*𝒪 = 𝒪` universally) and the vanishing of `H²` on a relative curve
  are spent;
* the **identity component** `Pic⁰ ⊆ Pic` exists as an open subgroup
  scheme.  Genuinely absent from the pin: there is no identity-component
  construction for group schemes at `a3364fa`;
* `Pic⁰ ⟶ S` is **proper**, the valuative criterion for line bundles on a
  relative curve.  Together with smoothness and connected fibres this is
  the `AbelianSchemeStruct`.

**The conclusion is stated on POINTS**, as a natural injection `incl`
that is a group homomorphism and whose image contains the Abel–Jacobi
points; by Yoneda that is the same as an open immersion of group schemes,
and it is what the assembly consumes.

**The three clauses that pin `Pic⁰`, and none may be dropped.**  The
audit on the parent records that what pins `Pic⁰` inside `Pic` is
*proper + open + contains the Abel–Jacobi image*.  Here:

* drop the **properness** in `ab` (a field of `AbelianSchemeStruct`) and
  `J = P` with `incl = id` satisfies everything else — `Pic` itself is
  the junk witness, exactly as recorded on `exists_relPicZero`;
* drop the **Abel–Jacobi clause** and `J = S`, `jstr = 𝟙 S` survives:
  `RelPoint (𝟙 S) g` is a singleton, so the injectivity, homomorphism and
  naturality clauses are all free and `𝟙 S` is proper, smooth and has
  connected (point) fibres.  This is the junk witness the parent's
  atomicity audit names, and the Abel–Jacobi clause is what kills it: at
  `T = X`, `g = strX` the classes of `𝒪(Δ − o_X)` and `𝒪` are distinct
  for `g ≥ 1`, so `aj` takes two values there and cannot factor through a
  singleton;
* drop **injectivity** of `incl` and `J` may be any abelian scheme
  mapping onto `Pic⁰`, e.g. `Pic⁰ × E` for an elliptic curve `E`, which
  makes `IsRelPicZeroOf.inj` false downstream.

**TRUE at genus 0 as well**, where `Pic⁰ = S` IS the junk witness above:
the Abel–Jacobi clause is then satisfiable by it, because every
`𝒪(x − o)` is trivial.  So the clause is a genuine constraint rather than
a hypothesis that only positive genus can meet.

`hequiv` is derivable in this file (`relPicEquiv_equivalence`) and is
passed in anyway, matching the parent's own hypothesis list: the
subfunctor of degree-zero classes is only well defined once
`Pic(X_T)/Pic(T)` is a quotient set. -/
theorem exists_relPicZeroSubgroup {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g)))) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (ab : AbelianSchemeStruct jstr)
      (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g),
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          incl T g p = incl T g q → p = q) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S), incl T g (ab.zero g) = hP.zeroPoint g) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
            incl T g (ab.add p q) = hP.addPoint (incl T g p) (incl T g q)) ∧
        (∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
            (p : RelPoint jstr g),
            incl T' g' (RelPoint.pre h hg p) = RelPoint.pre h hg (incl T g p)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
            ∃ p : RelPoint jstr g, incl T g p = aj T g x) :=
  sorry

/-- **`Pic⁰` IS AN ABELIAN SCHEME, GIVEN `Pic`** — BLR 9.4/4 (PROVEN
2026-07-29, over `exists_abelJacobiPoint` and `exists_relPicZeroSubgroup`).

The audit written while this was one node is the section comment above;
the split is described in the heading immediately before
`exists_abelJacobiPoint`.  What is left here is functor-of-points
bookkeeping, and it is worth reading once, because it is what makes the
split legitimate rather than a relocation: **every field of
`IsRelPicZeroOf` is discharged by ONE rewrite along a clause of
`exists_relPicZeroSubgroup`, followed by the corresponding fact about
`Pic`** — `hP.invertible`, `hP.inj`, `hP.sheaf_pre`, and the two supplied
hypotheses `_hzero`, `_hadd`.  Nothing is proven here that either leaf
could have been asked for instead.

The one step that is not a rewrite is `aj`, which is obtained by choice
from the Abel–Jacobi clause of `exists_relPicZeroSubgroup` — "the image
of `incl` contains every `aj x`".  Its two laws (`aj_pre`, `aj_base`)
then come from `hinj`: the point of `Pic⁰` above a given point of `Pic`
is unique, so an identity between Abel–Jacobi points of `Pic` transports
back up. -/
theorem exists_relPicZeroOf_of_relPicGroupLaw {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (_hzero : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      RelPicEquiv strX g (hP.sheaf (hP.zeroPoint g)) (modUnit _))
    (_hadd : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g),
      RelPicEquiv strX g (hP.sheaf (hP.addPoint p q))
        (modTensor (hP.sheaf p) (hP.sheaf q))) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsRelPicZeroOf strX ab o) := by
  obtain ⟨aj, hajSpec, hajPre, hajBase⟩ :=
    exists_abelJacobiPoint _hproper _hsmooth o hP
  obtain ⟨J, jstr, ab, incl, hinj, hzero, hadd, hpre, himg⟩ :=
    exists_relPicZeroSubgroup _hproper _hsmooth _hconn o hP _hpush _hequiv aj hajSpec
  choose aj' haj' using himg
  refine ⟨J, jstr, ab, ⟨?_⟩⟩
  exact
    { sheaf := fun {T} {g} p => hP.sheaf (incl T g p)
      invertible := fun {T} {g} p => hP.invertible (incl T g p)
      inj := fun {T} {g} p q hpq => hinj T g p q (hP.inj _ _ hpq)
      sheaf_zero := fun {T} g => by rw [hzero T g]; exact _hzero g
      sheaf_add := fun {T} {g} p q => by rw [hadd T g p q]; exact _hadd _ _
      sheaf_pre := fun {T'} {T} h {g} {g'} hg p => by
        rw [hpre T' T h g g' hg p]; exact hP.sheaf_pre h hg (incl T g p)
      aj := fun {T} {g} x => aj' T g x
      aj_spec := fun {T} {g} x => by rw [haj' T g x]; exact hajSpec T g x
      aj_pre := fun {T'} {T} h {g} {g'} hg x => by
        refine hinj T' g' _ _ ?_
        rw [haj' T' g' (RelPoint.pre h hg x), hpre T' T h g g' hg (aj' T g x),
          haj' T g x]
        exact hajPre T' T h g g' hg x
      aj_base := by
        refine hinj S (𝟙 S) _ _ ?_
        rw [haj' S (𝟙 S) o, hzero S (𝟙 S)]
        exact hajBase }

/-- **`Pic⁰` IS AN ABELIAN SCHEME, GIVEN `Pic`** (PROVEN 2026-07-28 over
`exists_relPicZeroOf_of_relPicGroupLaw`, discharging all four of that
leaf's extra hypotheses).

The four discharged inputs are the ones BLR 9.4/4 spends its first page
setting up, and none of them is ceremony:

* `_hpush` — `f_*𝒪_X = 𝒪_S` universally, from
  `hasUniversallyTrivialPushforward_of_isProper_of_smooth`; see
  `exists_relPicFull`.
* `_hequiv` — `RelPicEquiv` is an equivalence relation, from
  `relPicEquiv_equivalence`.  Needed here for the same reason as there,
  and additionally because every field of `IsRelPicZeroOf` is a
  `RelPicEquiv` statement that has to be CHAINED with others.
* `_hzero`, `_hadd` — the group law on the points of `Pic`, derived from
  `_hP` by `IsRelPicOf.zeroPoint` / `addPoint` and their specs.  This is
  the concrete content of the `IsRelPicOf` docstring's claim that
  dropping `sheaf_zero` and `sheaf_add` "costs nothing because the group
  law is determined rather than assumed": it is determined, and here it
  is, so what remains of BLR 9.4/4 is the GEOMETRY — smoothness and
  separatedness of `Pic ⟶ S`, cutting out the identity component,
  properness of `Pic⁰`, and the `𝒪(D)` dictionary for `aj` — with the
  functor-of-points bookkeeping already done.

What the remaining leaf still owes is therefore strictly the geometric
half, and it now has the algebraic half in hand. -/
theorem exists_relPicZero_of_isRelPicOf {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsRelPicZeroOf strX ab o) := by
  haveI := hproper
  haveI := hsmooth
  haveI := hconn
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth (n := 1) (f := strX)
  exact exists_relPicZeroOf_of_relPicGroupLaw hproper hsmooth hconn o hP
    (AlgebraicGeometry.hasUniversallyTrivialPushforward_of_isProper_of_smooth strX)
    (fun g => relPicEquiv_equivalence strX g)
    (fun g => hP.sheaf_zeroPoint g)
    (fun p q => hP.sheaf_addPoint p q)

/-- **GROTHENDIECK REPRESENTABILITY: `Pic⁰_{X/S}` is an abelian scheme,
for a smooth proper geometrically connected curve with a section, over an
ARBITRARY base** (PROVEN 2026-07-28 over `exists_relPicFull` and
`exists_relPicZero_of_isRelPicOf`; formerly a sorry node, and everything
below the decomposition heading is the audit that was written while it
was one).

TRUE and classical: FGA, exposé 232 (representability of `Pic_{X/S}` for
a projective flat morphism with integral geometric fibres);
Bosch–Lütkebohmert–Raynaud, *Néron Models*, 8.2/1 (existence) and 9.4/4
(`Pic⁰` of a relative curve is an abelian scheme); Stacks 0D2C.  The
section `o` is what makes the naive quotient `Pic(X_T)/Pic(T)` —
`RelPicEquiv` above — already equal to the relative Picard functor (BLR
8.1/4), which is the only reason `IsRelPicZeroOf` is statable with no
sheafification; and it is what the Abel–Jacobi fields `aj`, `aj_spec`,
`aj_base` are based at.

(Corrected 2026-07-28: this sentence read "statable at a pin with no site
theory", and that is FALSE of the pin — `Mathlib/AlgebraicGeometry/Sites/`
carries `fppfTopology` and `fpqcTopology`, both `Subcanonical`, plus a
Zariski representability criterion.  The substance is unaffected — the
section is what removes the *need* for sheafification — but the false
half would misdirect a prover into thinking the fppf route is closed.
The gate that IS live is the missing monoidal structure on
`SheafOfModules`; see the ROUTE AUDIT on `exists_relPicFull`.)

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
Cartier divisors exist.

**THE CONSTRUCTION AXIS, SEARCHED 2026-07-28 — AND IT CUTS.**  The cut
is not the `Sym^d` one anticipated above (that would still need relative
effective Cartier divisors); it is the split the two citations in the
first paragraph of this docstring were always naming as two different
theorems:

* `exists_relPicFull` — BLR **8.2/1**: `Pic_{X/S}` is representable, as
  the naive quotient `T ↦ Pic(X_T)/Pic(T)`, i.e. `IsRelPicOf`;
* `exists_relPicZero_of_isRelPicOf` — BLR **9.4/4**: given that, `Pic⁰`
  is an abelian scheme with the Abel–Jacobi map.

and this leaf is now their two-line composition.

**Why the rejection recorded above does not apply, and in fact points
here.**  The rejected cut was "a scheme carrying the classification data
exists" + "*any such scheme* is proper and smooth", refuted by
`Pic_{X/S}` itself as a witness of the first half that fails the second.
This cut differs in both halves.  The first half is strengthened by
exactly the field that rejection names as missing — `surj`, "every
invertible sheaf on `X_T` is classified" — so `Pic_{X/S}` is not a junk
witness of it but the INTENDED one, pinned up to unique isomorphism by
Yoneda.  And the second half does not assert that `P` is proper: it
produces a NEW scheme `J`, so the passage `Pic ↝ Pic⁰` and the proof
that the result is proper and smooth are still stated together, which is
what the rejection actually demanded.  The rejection was right; it was a
verdict about field-partitions of `IsRelPicZeroOf`, and this is not one.

**What would refute THIS cut**: a witness of `IsRelPicOf strX pstr` for
some `P` that is not the relative Picard scheme (which would make
`exists_relPicZero_of_isRelPicOf` false), or a proof that
`Pic(X_T)/Pic(T)` is not already the relative Picard functor here (which
would make `exists_relPicFull` false).  The second is BLR 8.1/4 and
depends only on the section `o` and on `f_*𝒪_X = 𝒪_S` universally, both
of which are hypotheses. -/
theorem exists_relPicZero {X S : Scheme.{u}} (strX : X ⟶ S)
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S)) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (ab : AbelianSchemeStruct jstr),
      Nonempty (IsRelPicZeroOf strX ab o) := by
  obtain ⟨_P, _pstr, ⟨hP⟩⟩ := exists_relPicFull strX hproper hsmooth hconn o
  exact exists_relPicZero_of_isRelPicOf hproper hsmooth hconn o hP

end Fermat
