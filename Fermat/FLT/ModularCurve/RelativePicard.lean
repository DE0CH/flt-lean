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

  **Amended 2026-07-30 (third amendment): `nonempty_modPullback_modTensorPic`
  is PROVEN, and the "hoist rather than proof" reading of it was wrong.**
  It is now a five-line composition over the single presheaf-level leaf
  `nonempty_presheafPullback_tensor` (`p(A ⊗ B) ≅ pA ⊗ pB` for the pullback
  of PRESHEAVES of modules).  The piece every audit of that leaf had missed
  is that mathlib ALREADY has "pullback commutes with sheafification"
  (`SheafOfModules.sheafificationCompPullback`), so no waiting on
  `AmpleSheaf.lean`'s owner was ever necessary.  The new leaf carries a
  falsity audit: the mathlib-shaped generalisation to an arbitrary functor
  between sites is FALSE, and it is `F = Opens.map h.base` having FILTERED
  comma categories that makes the scheme case true.

  **Amended 2026-07-29 (second amendment): `nonempty_modTensor_assocPic`
  is GONE.**  Its hoist was performed — the `modLocW` / `ModLM` /
  `modTensorLocIso` / `nonempty_modTensor_assoc` block was moved out of
  `AmpleSheaf.lean` into the "SHEAFIFICATION IS MONOIDAL" section of this
  module and the duplicate leaf deleted, its two uses redirected to
  `nonempty_modTensor_assoc`.  `nonempty_modPullback_modTensorPic` is NOT
  similarly ready: its twin is proven only over the still-open
  `isIso_modPullbackTensorComparison` in `AmpleSheaf.lean`, so hoisting it
  would move a leaf rather than remove one.  (Superseded by the third
  amendment above — the observation is still true, and the conclusion drawn
  from it, that waiting was the only option, was not.)

  **Amended 2026-07-29: `exists_modTensor_inv` is now PROVEN**, and the
  leaf under it is `exists_modDual` — the dual sheaf `L^∨` with its
  evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_Z`, asked for only up to LOCAL
  isomorphy of that one global map.  Both it and the global-from-local
  step `isIso_of_locally_isIso` that closes the gap were HOISTED here
  from `AmpleSheaf.lean`, where they had been written against a twin of
  this leaf named `exists_modTensor_inverse`; that module is DOWNSTREAM,
  so the two copies could never have merged any other way.
  `exists_modDual` is the one legitimate dispatch target of this section;
* `exists_relPicOf_isAffineOpen` — FGA 232 proper, i.e. representability
  over an AFFINE open of the base, where the curve is projective.  One of
  the two halves `exists_relPicOf_of_hasUniversallyTrivialPushforward`
  (FGA 232 with `f_*𝒪 = 𝒪` and the equivalence relation supplied) was cut
  into on 2026-07-29; that leaf is now PROVEN as their two-line assembly.
  See the section header above it;

  **Amended 2026-07-29 (same day, later): the other half,
  `exists_relPicOf_of_forall_isAffineOpen`, is now PROVEN too**, over a
  three-way cut of the Zariski-gluing argument —
  `exists_isRelPicOverAffines_of_forall_isAffineOpen` (the geometry: glue
  the local Picard schemes and the rigidified Poincaré bundles),
  `inj_of_isRelPicOverAffines` (unconditional) and
  `surj_of_isRelPicOverAffines` (BLR 8.1/4, the only consumer of the
  section and of `f_*𝒪 = 𝒪`).  The cut is forced by a gap in that leaf's
  own docstring, corrected in place: `sheaf` has no local definition to
  glue, because `_hloc` hands out structures that agree only up to an
  automorphism of the functor `Pic(X_-)/Pic(-)`.

  **Amended again 2026-07-30: the second of those three,
  `inj_of_isRelPicOverAffines`, is now PROVEN**, over the new transport
  lemma `relPicEquiv_modPullback` (stability of `RelPicEquiv` under change
  of test object) — and proven with the hypothesis-free signature the cut
  predicted, so the "unconditional" claim there is compiler-checked now
  rather than asserted.

  **Amended a third time, 2026-07-30 (later the same day): the third of
  the three, `surj_of_isRelPicOverAffines`, is now PROVEN too**, over the
  single new leaf `relPicEquiv_of_forall_restrict` — the statement that
  `T ↦ Pic(X_T)/Pic(T)` is a ZARISKI SHEAF, with no `pstr` and no
  representing scheme anywhere in it.  What that discharged is everything
  scheme-theoretic in BLR 8.1/4: the local classifying points, their
  agreement on overlaps (via the affine-local `inj` and the two new
  functoriality lemmas `curveBaseChangeMap_comp` /
  `curveBaseChangeMap_congr`), and their gluing to a global `T ⟶ P`.
  `_o` and `_hpush` are still consumed exactly once, but now inside the
  leaf, whose docstring carries the refutation of dropping either.  The
  ONE remaining dispatch target of this cut is
  `exists_isRelPicOverAffines_of_forall_isAffineOpen` (the geometry);
* `exists_relPicZeroOf_of_relPicGroupLaw` — BLR 9.4/4 with `f_*𝒪 = 𝒪`,
  the equivalence relation and the group law on `Pic`'s points supplied.
  **Amended 2026-07-29: this one is now PROVEN**, over a two-leaf cut of
  BLR 9.4/4 into its `𝒪(D)` half and its geometric half, which are
  independent of each other:

  * `exists_abelJacobiPoint` — the Abel–Jacobi map `x ↦ [x] − [o]` into
    the POINTS of `Pic`.  **Amended 2026-07-29: PROVEN**, over exactly the
    two facts about `sectionIdeal` its audit predicted, now the named
    leaves `isInvertibleSheaf_sectionIdeal` and
    `nonempty_modPullback_sectionIdeal`.  The tensor-calculus statement
    it also named is PROVEN, not a leaf — `isInvertibleSheaf_modPullback`.
    **Amended 2026-07-31**: the second of those two,
    `nonempty_modPullback_sectionIdeal`, is now PROVEN as well, over the
    cartesian-square lemmas `isPullback_curveBaseChangeMap`,
    `relSection_comp_curveBaseChangeMap` and
    `relSection_comp_curveBaseChangeProj` plus a leaf with no curve in it,
    `nonempty_modPullback_sectionIdeal_of_isPullback` (Stacks 062Y/0631);
  * `exists_relPicZeroSubgroup` — the geometry: cut `Pic⁰` out of `Pic`
    and show it is proper, smooth and geometrically connected.  This is
    what BLR 9.4/4 is usually cited FOR, and it is the leaf with real
    content: the identity component of a group scheme does not exist at
    this pin in any form.  Its FIRST classical step was cut out
    2026-07-30 as `smooth_isSeparated_of_isRelPicOf` and is received back
    as the hypotheses `_hPsmooth`/`_hPsep`; the parent
    `exists_relPicZeroOf_of_relPicGroupLaw` discharges them by that leaf,
    so nothing downstream changed.  Later the same day that conjunction
    was itself split into `smooth_of_isRelPicOf` (BLR 8.4/2) and
    `isSeparated_of_isRelPicOf` (BLR 8.2/1), which are the two dispatch
    targets; `smooth_isSeparated_of_isRelPicOf` is now their assembly and
    is PROVEN.  **Amended 2026-07-31**: `exists_relPicZeroSubgroup` is now
    PROVEN too, as the transport of a group law along an injection, over
    the new leaf `exists_relPicZeroSubfunctor` — which asks for the same
    geometry with the twelve fields of `AbelianSchemeStruct` replaced by
    three CLOSURE clauses (image contains `zeroPoint`, closed under
    `addPoint` and under `negPoint`).  The group axioms it no longer has
    to prove are now proven once and for all about `Pic` itself, in the
    `IsRelPicOf` group-law section.

So the direct-sorry set of this module is 9 (verified against the
compiler's `declaration uses 'sorry'` warnings, and against a
comment-stripped token count — 9 = 9, so there are no anonymous inner
sorries hiding behind a warning), and the five that belong to BLR 9.4/4
are `isInvertibleSheaf_sectionIdeal`,
`nonempty_modPullback_sectionIdeal_of_isPullback` (2026-07-31: this slot used to
be `nonempty_modPullback_sectionIdeal`, which is now its consumer and PROVEN),
`smooth_of_isRelPicOf`, `isSeparated_of_isRelPicOf` and
`exists_relPicZeroSubfunctor` (2026-07-31: likewise, this slot used to be
`exists_relPicZeroSubgroup`).

**A note on the count, since it did not move on 2026-07-31 and two leaves
closed that day.**  Both closures were CUTS: one leaf proven, one opened, net
zero.  That is the expected shape when a node is decomposed rather than
discharged, and reading the count alone would say nothing happened.  What did
happen is that the two open statements got strictly smaller — one lost every
mention of a curve, the other lost nine group axioms — and eleven declarations
that used to be inside them are now theorems.

**Amended 2026-07-30 (later the same day): 10 → 9 → 8 → 9.**  Both `modDual`
leaves closed, `isInvertibleSheaf_modDual` first and then `isIso_modDualEv`,
over one shared rank-one bridge across the `restrict` boundary
(`ModDual.trAt … ModDual.gen_res`, then `ModDual.dualRestrictIso` and
`ModDual.evLin_bijective`).  Read the count off the compiler, not off this
paragraph — every previous version of it went stale within a day.  Of the
eight that remain, ONE is not a dispatch target:
`nonempty_modPullback_modTensorPic` is the verbatim twin of
`Fermat.nonempty_modPullback_modTensor` in `Modularity/AmpleSheaf.lean`, and
re-surveyed 2026-07-30 that twin is PROVEN there over a written comparison
map whose own `IsIso` clause (`isIso_modPullbackTensorComparison`) is still
that module's leaf.  So the hoist its docstring prescribes would move a leaf
rather than close one, and mathlib has no monoidal structure on the pullback
of (pre)sheaves of modules at this pin to shortcut it —
`grep -rln Monoidal Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/`
returns `Monoidal.lean`, `PushforwardZeroMonoidal.lean` and
`ColimitFunctor.lean`, none of them about `pullback`.

The 8 → 9 in that chain is a SPLIT, not a regression:
`smooth_isSeparated_of_isRelPicOf` was a conjunction of BLR 8.4/2 and BLR
8.2/1 — different chapters, different arguments, different hypotheses — and is
now PROVEN as the assembly of `smooth_of_isRelPicOf` and
`isSeparated_of_isRelPicOf`, so the two can be owned separately.  Nothing
downstream changed; `exists_relPicZeroOf_of_relPicGroupLaw` still destructures
the same conjunction.

Also PROVEN here and worth knowing about before re-deriving them:
`modTensorMapIso`, `modTensorUnitLeftIso`, `modTensorUnitRightIso`,
`modTensorSymmIso` (the BRAIDING), `modPullbackUnitIso`,
`isInvertibleSheaf_modUnit`, `isInvertibleSheaf_modTensorPic`,
`isInvertibleSheaf_modPullback`, `nonempty_modTensor_middleFourPic`,
`nonempty_iso_of_modTensorPic_left` (cancellation),
`relPicEquiv_refl/symm/trans/equivalence`, the four congruence lemmas
`relPicEquiv_of_iso/tensor_right/modPullback/cancel_left`,
`IsRelPicOf.eq_of_relPicEquiv_tensor`,
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
`ModularCurve/X0.lean`, as two general-base leaves.  **Amended 2026-07-30:
those are no longer `IsRelPicZeroOf.exists_albaneseFactorisation` and
`IsRelPicZeroOf.eq_of_aj_eq` — both of THOSE are now PROVEN.**  They are
`IsRelPicZeroOf.exists_flatSurj_ajListSum` (`Sym^d C ↠ Pic^d`, i.e.
Riemann–Roch) and
`IsRelPicZeroOf.listSum_map_eq_of_listSum_aj_eq_of_compactSpace`
(Abel's theorem: `Σ c(yᵢ)` depends only on the class `Σ aj(yᵢ)`).  Those
two are the whole of what autoduality still owes, and since 2026-07-30 they
carry the SAME `[CompactSpace T]` hypothesis: the general-base form of the
second is PROVEN over it by Zariski-locality, so one subtree closes both
under one hypothesis.

Note that the phrase "autoduality and biduality" this paragraph used to
carry was ALSO wrong about the mathematics, not merely about which names
are open: the route actually taken needs no dual abelian scheme and no
biduality at all.  It defines `u` fppf-locally by `Σ aj(yᵢ) ↦ Σ c(yᵢ)`
and descends, and the descent is in the pin already
(`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`).

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

Amended 2026-07-30, and by the same method (the `declaration uses 'sorry'`
set for `X0.lean`, 109 warnings, neither of these among them): the
sentence immediately above is now STALE.  `IsRelPicZeroOf.eq_of_aj_eq` was
proven earlier the same day and `IsRelPicZeroOf.exists_albaneseFactorisation`
later on it; the two open leaves that replaced them are named in the
"autoduality half" paragraph above.  It is left visible rather than deleted
because it dates a claim that was true when written — which is exactly how
this file's leaf lists go stale, and worth one example.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward
public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalW
public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Presheaf.PullbackMonoidal

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

**PASTED IN 2026-07-29, with their consumer.**  Both are now declarations —
`presheafOfModulesSymm` and `modTensorSymmIso` below — because
`exists_abelJacobiPoint` is proven and consumes the braiding four times
(`nonempty_modTensor_middleFourPic`, `nonempty_iso_of_modTensorPic_left`, and
twice in `IsRelPicOf.eq_of_relPicEquiv_tensor`).  They were correct as written:
the two blocks below are the docstring's text verbatim.

Note `Modularity/AmpleSheaf.lean`, DOWNSTREAM, carries its own copies under the
names `presheafOfModulesSymmetric` and `modTensorComm`.  The names are
deliberately different so that nothing collides while that module has live
owners; the follow-up is the usual hoist — delete those two there and redirect
`nonempty_iso_of_modTensor_left`, `RelPicEquiv.symm` and `modLocW_whiskerLeft`'s
braiding uses to these.  A duplicate *instance* is harmless here because both are
`inferInstanceAs` of the very same mathlib instance, hence defeq.

The immediate consequences, so that nobody prices them as leaves:
`modTensor L M ≅ 𝒪 → modTensor M L ≅ 𝒪` is one line, and the
middle-four interchange `(L ⊗ N) ⊗ M ≅ (L ⊗ M) ⊗ N` is
`nonempty_modTensor_assoc` twice plus one braiding.

**Amended 2026-07-29: ASSOCIATIVITY IS NO LONGER MISSING EITHER.**  The
`modLocW` / `ModLM` / `modTensorLocIso` / `nonempty_modTensor_assoc` block
that used to live in `AmpleSheaf.lean` is now declared HERE, in the
"SHEAFIFICATION IS MONOIDAL" section below, and the duplicate leaf that
stood in its place (`nonempty_modTensor_assocPic`) is DELETED with its two
uses in `relPicEquiv_symm` / `relPicEquiv_trans` redirected — exactly the
hoist its own docstring prescribed, made possible by
`modLocW_whiskerLeft`/`Right` having been proven.  `AmpleSheaf.lean`
inherits the whole block by import and is otherwise untouched.

**What is genuinely still open** is exactly the part needing
*sheafification to commute with PULLBACK*: one leaf,
`nonempty_modPullback_modTensorPic`, whose twin
`nonempty_modPullback_modTensor` in `AmpleSheaf.lean` is proven only over
the still-open `isIso_modPullbackTensorComparison` there.  **It must not be
dispatched at independently** — hoisting it would drag that leaf up rather
than remove one; the correct action is the hoist, once it is settled.

**Amended 2026-07-31 — the paragraph above is WITHDRAWN in full.**
"Sheafification commutes with pullback" is not open and never was: it is
`SheafOfModules.sheafificationCompPullback` in the pin.
`nonempty_modPullback_modTensorPic` is PROVEN, the hoist is cancelled, and what
is genuinely still open is the PRESHEAF-level
`nonempty_presheafModPullback_tensor` — which is a statement about a filtered
colimit on the site of opens and mentions no sheaf at all.  Its section header,
just above it, also records the counterexample that shows it must NOT be
generalised to an arbitrary continuous functor between sites. -/

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

/-- Presheaves of modules over a presheaf of COMMUTATIVE rings form a SYMMETRIC
monoidal category; as with `presheafOfModulesMonoidal`, typeclass search cannot
invert the composition `Z.presheaf ⋙ forget₂ _ _` against `Z.ringCatSheaf.obj`
on its own, so the instance is supplied by hand. -/
noncomputable instance presheafOfModulesSymm (Z : Scheme.{u}) :
    SymmetricCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory
    (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- **THE BRAIDING**, `L ⊗ M ≅ M ⊗ L` (PROVEN 2026-07-29, one line) — `modTensor`
is SYMMETRIC at this pin.

Sheafify mathlib's presheaf-level braiding, exactly as `modTensorUnitLeftIso`
sheafifies the presheaf-level unitor.  See the section header for why the
"`modTensor` has no symmetry" claim that stood in three audits was false. -/
noncomputable def modTensorSymmIso {Z : Scheme.{u}} (L M : Z.Modules) :
    modTensor L M ≅ modTensor M L :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (β_ L.val M.val)

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

/-! #### Sheafification is monoidal, and the one leaf that remains

**Amended 2026-07-29.**  This used to read "the two leaves that remain, and
their downstream twins".  One of the two — `nonempty_modTensor_assocPic` —
is gone: the block that discharges it was hoisted here out of
`AmpleSheaf.lean` (next section) and the duplicate deleted.  What remains
is `nonempty_modPullback_modTensorPic`, whose twin is itself still open
downstream. -/

/-! ### SHEAFIFICATION IS MONOIDAL, via `CategoryTheory.LocalizedMonoidal`

The route recorded (and untried) in the old docstring of `nonempty_modTensor_assoc`:
pair `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`.  It works, and it
reduces the WHOLE associativity question to a single statement about local
isomorphisms, `modLocW_whiskerLeft` below.

The chain is:

* `PresheafOfModules.sheafification` is a LOCALIZATION functor, for the class
  `modLocW Z` of morphisms it inverts (mathlib:
  `PresheafOfModules.instIsLocalization`, or directly
  `Adjunction.isLocalization` applied to `sheafificationAdjunction`, which is
  what is used here since it avoids naming the Grothendieck topology);
* `PresheafOfModules Z.ringCatSheaf.obj` is symmetric monoidal at this pin;
* IF `modLocW Z` is compatible with `⊗` (`MorphismProperty.IsMonoidal`), then
  `CategoryTheory.LocalizedMonoidal` puts a monoidal structure on the localized
  category — which IS `Z.Modules`, as a type synonym — and makes sheafification
  a monoidal functor, with comparison isomorphism
  `Localization.Monoidal.μ : a(P) ⊗ a(Q) ≅ a(P ⊗ Q)`;
* `modTensor L M` is `a(L.val ⊗ M.val)`, and `a(M.val) ≅ M`
  (`modSheafifyValIso`), so `μ` identifies `modTensor` with the localized
  tensor product (`modTensorLocIso`), and the associator transports.

`MorphismProperty.IsMonoidal` asks for stability under BOTH whiskerings; the
right one follows from the left one by the braiding, so exactly one genuine
statement is left. -/

/-- **Local isomorphisms of presheaves of `𝒪_Z`-modules**: the morphisms that
become isomorphisms after sheafification.

Equal to `J.W.inverseImage (PresheafOfModules.toPresheaf _)` — mathlib's
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` —
i.e. to the locally bijective morphisms of underlying abelian presheaves; this
formulation is used because it names no Grothendieck topology. -/
def modLocW (Z : Scheme.{u}) : MorphismProperty (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  (MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj))

/-- Sheafification is the localization of presheaves of modules at `modLocW`. -/
instance modLocW_isLocalization (Z : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).IsLocalization (modLocW Z) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).isLocalization

instance modLocW_isMultiplicative (Z : Scheme.{u}) : (modLocW Z).IsMultiplicative := by
  unfold modLocW; infer_instance

instance modLocW_respectsIso (Z : Scheme.{u}) : (modLocW Z).RespectsIso := by
  unfold modLocW; infer_instance

/-- Presheaves of modules over a presheaf of COMMUTATIVE rings form a symmetric
monoidal category; as with `presheafOfModulesMonoidal`, typeclass search cannot
invert the composition `Z.presheaf ⋙ forget₂ _ _` against `Z.ringCatSheaf.obj`
on its own. -/
noncomputable instance presheafOfModulesSymmetric (Z : Scheme.{u}) :
    SymmetricCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory
    (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- **TENSORING PRESERVES LOCAL ISOMORPHISMS** — PROVEN (2026-07-28).  This is
the entire mathematical content of "sheafification is monoidal" for
`𝒪_Z`-modules: with it, `MorphismProperty.IsMonoidal (modLocW Z)` holds, and
every associativity and unit statement about `modTensor` follows formally.

Concretely: if `g` becomes an isomorphism after sheafification, so does
`X ◁ g : X ⊗ Y₁ ⟶ X ⊗ Y₂`.  Unfolded through
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` and
`GrothendieckTopology.WEqualsLocallyBijective`, it says that `X ⊗ -` preserves
LOCAL BIJECTIVITY of maps of abelian presheaves.

TRUE, and standard (Stacks 01LA; Mac Lane VII).  It is NOT a formal consequence
of right exactness alone: local surjectivity of `X ◁ g` is the easy half (a
section of `X ⊗ Y₂` is a finite sum of tensors, each of whose right factors
lifts locally, and finitely many covering sieves may be intersected), while
local INJECTIVITY has to rule out a `Tor`-type contribution.

The proof lives in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/MonoidalW.lean`
(`Fermat.SheafificationMonoidal.W_whiskerLeft`), stated for an ARBITRARY site
and an arbitrary presheaf of commutative rings, so nothing here is special to
`Z.Opens`.

ROUTE ACTUALLY TAKEN, and a correction to the three routes this docstring used
to record as the only candidates.  Routes 1 and 3 were both real but both cost
a missing theory:

* the *internal hom* route (mathlib's own proof of
  `CategoryTheory.GrothendieckTopology.W.whiskerLeft` in
  `Mathlib/CategoryTheory/Sites/Monoidal.lean`) needs `MonoidalClosed
  (PresheafOfModules R)`, which is still absent from this pin — re-checked
  2026-07-28 by `grep -rn MonoidalClosed
  Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/`, which is EMPTY;
* the *stalk* route (`Mathlib/CategoryTheory/Sites/Point/IsMonoidalW.lean`
  plus `Mathlib/Topology/Sheaves/Points.lean`) needs a MONOIDAL stalk functor
  for presheaves of modules, i.e.
  `colim_{U ∋ z} (X(U) ⊗_{𝒪(U)} Y(U)) ≅ X_z ⊗_{𝒪_{Z,z}} Y_z` — a filtered
  colimit of tensor products over a filtered system of base rings, which the pin
  does not have either.

Neither is needed.  The statement is ELEMENTARY, and the one non-formal input is
the EQUATIONAL CRITERION FOR VANISHING (Stacks 00HK; Altman–Kleiman Lemma 8.16):
if `∑ᵢ xᵢ ⊗ g(yᵢ) = 0` in `X(U) ⊗_{𝒪(U)} Y₂(U)`, the vanishing is witnessed by a
finite system of relations `g(qₛ) = ∑ⱼ aₛⱼ wⱼ`, `∑ₛ aₛⱼ pₛ = 0`.  Cover `U` so
that every `wⱼ` lifts to some `vⱼ` (local surjectivity of `g`), refine so that
`qₛ − ∑ⱼ aₛⱼ vⱼ` dies (local injectivity of `g`), and on that cover
`∑ₛ pₛ ⊗ qₛ = ∑ⱼ (∑ₛ aₛⱼ pₛ) ⊗ vⱼ = 0`.

Mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` states the
criterion only when the `xᵢ` GENERATE the module, which is exactly what is
unavailable here (and the hypothesis is not removable: `2 ⊗ 1 = 0` in
`ℤ ⊗ ℤ/2` while `2 ⊗ 1 ≠ 0` in `2ℤ ⊗ ℤ/2`).  `SheafificationMonoidal
.exists_relations` is the general form, obtained by the same argument over a
free presentation indexed by `Fin k ⊕ M` — the `⊕` is what keeps the original
family from being identified when two `xᵢ` coincide. -/
theorem modLocW_whiskerLeft {Z : Scheme.{u}} (X : PresheafOfModules.{u} Z.ringCatSheaf.obj)
    {Y₁ Y₂ : PresheafOfModules.{u} Z.ringCatSheaf.obj} {g : Y₁ ⟶ Y₂}
    (hg : modLocW Z g) : modLocW Z (X ◁ g) := by
  have key : modLocW Z = _ :=
    (PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 Z.ringCatSheaf.obj)).symm
  rw [key] at hg ⊢
  exact SheafificationMonoidal.W_whiskerLeft (R := Z.presheaf) X hg

/-- The right-hand whiskering, from the left-hand one by the braiding. -/
theorem modLocW_whiskerRight {Z : Scheme.{u}}
    {X₁ X₂ : PresheafOfModules.{u} Z.ringCatSheaf.obj} {f : X₁ ⟶ X₂}
    (hf : modLocW Z f) (Y : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    modLocW Z (f ▷ Y) :=
  ((modLocW Z).arrow_mk_iso_iff (Arrow.isoMk (β_ X₁ Y) (β_ X₂ Y)
    (BraidedCategory.braiding_naturality_left f Y).symm)).2 (modLocW_whiskerLeft Y hf)

instance modLocW_isMonoidal (Z : Scheme.{u}) : (modLocW Z).IsMonoidal where
  whiskerLeft X _ _ _ hg := modLocW_whiskerLeft X hg
  whiskerRight _ hf Y := modLocW_whiskerRight hf Y

/-- The unit isomorphism required by `LocalizedMonoidal`.  Nothing here consumes
the monoidal unit of the localized structure, so the tautological choice is
taken and no identification with `modUnit Z` is needed. -/
noncomputable abbrev modLocEps (Z : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj
        (𝟙_ (PresheafOfModules.{u} Z.ringCatSheaf.obj)) ≅
      (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj
        (𝟙_ (PresheafOfModules.{u} Z.ringCatSheaf.obj)) := Iso.refl _

/-- `Z.Modules`, carrying the localized monoidal structure.  This is a TYPE
SYNONYM for `Z.Modules`, which is why `toModLM` below is the identity. -/
noncomputable abbrev ModLM (Z : Scheme.{u}) : Type (u + 1) :=
  LocalizedMonoidal (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj))
    (modLocW Z) (modLocEps Z)

/-- Sheafification, seen as a monoidal functor into `ModLM Z`. -/
noncomputable abbrev modLocA (Z : Scheme.{u}) :
    PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ ModLM Z :=
  Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)) (modLocW Z) (modLocEps Z)

/-- An `𝒪_Z`-module, seen as an object of `ModLM Z`.  The identity; it exists
only to stop the elaborator from immediately unfolding the type synonym and
losing the monoidal instance. -/
def toModLM {Z : Scheme.{u}} (M : Z.Modules) : ModLM Z := M

/-- `modSheafifyValIso`, read in `ModLM Z`. -/
noncomputable def modSheafifyValIsoLM {Z : Scheme.{u}} (M : Z.Modules) :
    (modLocA Z).obj M.val ≅ toModLM M where
  hom := (modSheafifyValIso M).hom
  inv := (modSheafifyValIso M).inv
  hom_inv_id := (modSheafifyValIso M).hom_inv_id
  inv_hom_id := (modSheafifyValIso M).inv_hom_id

/-- **`modTensor` IS the localized monoidal product**: `a(L.val ⊗ M.val)` is
identified with `L ⊗ M` in `ModLM Z` by the monoidal-functor comparison `μ`
together with `a(M.val) ≅ M`. -/
noncomputable def modTensorLocIso {Z : Scheme.{u}} (L M : Z.Modules) :
    toModLM (modTensor L M) ≅ toModLM L ⊗ toModLM M :=
  (Localization.Monoidal.μ _ (modLocW Z) (modLocEps Z) L.val M.val).symm ≪≫
    MonoidalCategory.tensorIso (modSheafifyValIsoLM L) (modSheafifyValIsoLM M)

/-- **THE ASSOCIATOR** — PROVEN (2026-07-28): `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` for
`𝒪_Z`-modules.

The route recorded in the previous version of this docstring — pair
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean` — is the one that
works; see the section above.  The whole associativity question reduces to
`modLocW_whiskerLeft` ("tensoring preserves local isomorphisms") — itself PROVEN
since 2026-07-28 — from which the localized monoidal structure, and with it this
associator, both unitors and the braiding, are formal.

Everything about tensor powers in `Modularity/AmpleSheaf.lean`
(`nonempty_modTensorPow_add`, `nonempty_modTensorPow_mul`, and hence
`isAmpleSheaf_modTensorPow`) is DERIVED from this statement, as are
`relPicEquiv_symm` and `relPicEquiv_trans` below, so NO open associativity
obligation is left anywhere in the tree.

**HOISTED here from `Modularity/AmpleSheaf.lean` on 2026-07-29**, together
with the whole `modLocW` / `ModLM` / `modTensorLocIso` section above, and
byte-identical to what stood there.  The point of the move is that
`AmpleSheaf.lean` `public import`s THIS module, so its copy could not serve
the relative-Picard calculus here and the duplicate leaf
`nonempty_modTensor_assocPic` could only ever have stayed open.  That leaf
is now deleted and its two uses point at this declaration; `AmpleSheaf.lean`
inherits everything by import and is otherwise untouched. -/
theorem nonempty_modTensor_assoc {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor L (modTensor M N)) := by
  have e : toModLM (modTensor (modTensor L M) N) ≅ toModLM (modTensor L (modTensor M N)) :=
    modTensorLocIso (modTensor L M) N ≪≫
      MonoidalCategory.tensorIso (modTensorLocIso L M) (Iso.refl (toModLM N)) ≪≫
      α_ (toModLM L) (toModLM M) (toModLM N) ≪≫
      MonoidalCategory.tensorIso (Iso.refl (toModLM L)) (modTensorLocIso M N).symm ≪≫
      (modTensorLocIso L (modTensor M N)).symm
  exact ⟨{ hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }⟩

/-! #### Pullback and `modTensor`: the sheafification is FREE, the presheaf pullback is not

**Amended 2026-07-31, and this REVERSES the route this section used to record.**
The old docstring of `nonempty_modPullback_modTensorPic` said

> `Scheme.Modules.pullback` is a left adjoint and the presheaf pullback is
> strong monoidal, so the content is again that sheafification is monoidal:
> the sheafification inside `modTensor` has to move across the pullback.

**Both halves are wrong, and they are wrong in opposite directions.**

* *Moving sheafification across the pullback is FREE* — it is
  `SheafOfModules.sheafificationCompPullback` in the pin,
  `a_Z ⋙ f^*_{sheaf} ≅ f^*_{presheaf} ⋙ a_W`, together with
  `SheafOfModules.pullbackIso`.  Nothing has to be proven for it.
* *The presheaf pullback is NOT strong monoidal in general.*  It is the left
  adjoint of `pushforward φ`, which factors as restriction of scalars along
  `φ` (left adjoint = base change, strong monoidal) after precomposition with
  `F` (left adjoint = a relative left Kan extension, **not** monoidal).  For
  `F : C ⥤ D` collapsing two objects `x, y` of a discrete `C` to one object
  `a` of `D`, with constant ring `k`, `(Lan M)(a) = M x ⊕ M y`, so
  `Lan M ⊗ Lan N` has four summands where `Lan (M ⊗ N)` has two.  So a proof
  of the leaf below may NOT be attempted at the generality of an arbitrary
  morphism of presheaves of rings over an arbitrary continuous functor — it is
  false there.

What rescues it here is that the site is `Opens`: `Opens.map h.base` preserves
finite meets, so `{U : Z.Opens // V ≤ h ⁻¹ᵁ U}` is CODIRECTED, the Kan extension
`(Lan M)(V) = colim_{U ⊇ h(V)} M(U) ⊗_{Γ(Z,U)} Γ(W,V)` is a FILTERED colimit,
and tensor products commute with filtered colimits.  That is the whole
mathematical content, and it is now isolated in one leaf,
`nonempty_presheafModPullback_tensor`, with no sheaf theory in it at all.

The consequence for dispatch is the reverse of what stood here: the leaf below
is PROVEN and is no longer a dispatch target, and there is no hoist to wait for.
Its twin `Fermat.nonempty_modPullback_modTensor` in
`Fermat/FLT/Modularity/AmpleSheaf.lean` — which is DOWNSTREAM and is proven
there only over that module's still-open `isIso_modPullbackTensorComparison` —
should now be redirected to this declaration, and
`isIso_modPullbackTensorComparison` together with `modPullbackTensorComparison`
and `modPullbackTensorComparison_tensorSection` DELETED.  That is a strict
removal of a leaf, not a hoist, and it is left to that module's owner because it
is a downstream edit.

**Amended again 2026-07-31 (fourth amendment), and it corrects the ROUTE advice above
as well as the leaf count.**

* The route recommended above — establish the filtered-colimit formula for the Kan
  extension and run "tensor commutes with filtered colimits" — was NOT the one that
  worked, and is not needed.  What the argument actually needs is only that `pullback`
  and `− ⊗ Q` preserve colimits, both of which are already instances in the pin.  The
  *generators* route, listed above as the second option, carries the whole dévissage,
  and the codirectedness of `{U // V ≤ h ⁻¹ᵁ U}` is replaced by the single fact that
  `Opens.map` preserves binary meets.
* The paragraph above says the presheaf pullback "is NOT strong monoidal in general" and
  that "a proof of the leaf below may NOT be attempted at the generality of an arbitrary
  morphism of presheaves of rings over an arbitrary continuous functor".  Both remain
  true, and the counterexample is unchanged — but note WHERE the generality now bites:
  the oplax structure `δ` and the two-variable dévissage
  (`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean`) are
  valid for an ARBITRARY `F`, with no hypothesis on the site at all.  The only statement
  that is false for a general `F` is the GENERATOR case,
  `isIso_presheafModPullback_delta_freeYoneda`.  So the counterexample does not forbid
  working in general — it forbids only concluding in general, and it localises to one
  leaf about `free (yoneda U) ⊗ free (yoneda U')`.
* Two leaves in this file, `nonempty_presheafModPullback_tensor` and
  `nonempty_presheafPullback_tensor` ninety lines below it, were the SAME statement:
  `presheafModPullback h` and `presheafPullback h` both unfold to
  `PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom h).hom`, once with dot
  notation and once without.  Both are now proven, the second by `exact` over the first.
  Worth a general moral: a wrapper `abbrev` hides identity as effectively as it hides
  complexity, and two wrappers around one term will not be noticed by any frontier
  scan, which counts declarations. -/

/-- **The PRESHEAF-level pullback** of presheaves of modules along a morphism of
schemes, i.e. `Scheme.Modules.pullback h` before sheafification.

`SheafOfModules.pullbackIso` and `SheafOfModules.sheafificationCompPullback`
relate it to `modPullback`; it exists as a named abbreviation only so that the
one genuine leaf about it can be stated. -/
noncomputable abbrev presheafModPullback {Z W : Scheme.{u}} (h : W ⟶ Z) :
    PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ PresheafOfModules.{u} W.ringCatSheaf.obj :=
  PresheafOfModules.pullback.{u} (Scheme.Hom.toRingCatSheafHom h).hom

/-- **SHEAFIFYING A PRESHEAF TENSOR PRODUCT IS `modTensor` OF THE SHEAFIFICATIONS**
(PROVEN — free from the localized monoidal structure): `a(A ⊗ B) ≅ a A ⊗ a B`.

This is the step that lets an identity proven for PRESHEAVES be pushed into
`Z.Modules`, and it is exactly where `modLocW_isMonoidal` is spent: `μ` compares
`a A ⊗ a B` with `a (A ⊗ B)` in `ModLM W`, and `modTensorLocIso` compares
`modTensor (a A) (a B)` — which is `a ((a A).val ⊗ (a B).val)` by definition —
with the same thing.  No comparison of `A` with `(a A).val` is needed anywhere,
which is why the unit of the sheafification adjunction never appears. -/
noncomputable def modSheafifyTensorIso {W : Scheme.{u}}
    (A B : PresheafOfModules.{u} W.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj (A ⊗ B) ≅
      modTensor ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj A)
        ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj B) :=
  letI e : toModLM ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj (A ⊗ B)) ≅
      toModLM (modTensor ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj A)
        ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj B)) :=
    (Localization.Monoidal.μ _ (modLocW W) (modLocEps W) A B).symm ≪≫
      (modTensorLocIso ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj A)
        ((PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj B)).symm
  { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

/-- The comparison map `p(P ⊗ Q) ⟶ pP ⊗ pQ` for the PRESHEAF pullback, as the `δ` of an
oplax monoidal structure.

**Where it comes from (2026-07-31, and it is not an ad-hoc construction).**
`pushforward φ` is `pushforward₀OfCommRingCat` — which mathlib knows is STRONG monoidal,
`PresheafOfModules.instMonoidalPushforward₀OfCommRingCat` — followed by `restrictScalars φ`,
which is LAX monoidal (`PresheafOfModules.restrictScalarsLaxMonoidal`, proven sectionwise
over `ModuleCat.instLaxMonoidalRestrictScalars` in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean`).  So
`pushforward φ` is lax monoidal and its left adjoint `pullback φ` is OPLAX monoidal by
`Adjunction.leftAdjointOplaxMonoidal`.  `δ` is natural in both variables — which is what
makes the dévissage below legitimate. -/
noncomputable abbrev presheafModPullbackDelta {Z W : Scheme.{u}} (h : W ⟶ Z)
    (P Q : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    (presheafModPullback h).obj (P ⊗ Q) ⟶
      (presheafModPullback h).obj P ⊗ (presheafModPullback h).obj Q :=
  Functor.OplaxMonoidal.δ
    (PresheafOfModules.pullback.{u} (PresheafOfModules.ringCatHomOfCommRingCatHom h.c)) P Q

/-- **THE GENERATOR CASE OF "THE PRESHEAF PULLBACK IS STRONG MONOIDAL"** (sorry leaf, cut
2026-07-31 out of `nonempty_presheafModPullback_tensor` — which is now PROVEN over it).

This is ALL that is left of "pullback commutes with `⊗`" at presheaf level: the comparison
`δ` on the free presheaves of modules on representables.  Everything else — the existence
of `δ`, its naturality, and the dévissage from arbitrary `P`, `Q` down to this case — is
proven, in `Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean`
(`PresheafOfModules.pullbackOplaxMonoidal` and `isIso_pullback_delta`).

**THIS IS EXACTLY WHERE THE SITE ENTERS, AND IT IS THE ONLY PLACE IT DOES.**  See the
section header for why the statement is FALSE one generality up: for a functor `F`
collapsing two objects of a discrete `C` onto one, `δ` compares `k²` with `k⁴` on
generators and is not invertible.  The dévissage above is valid for ANY `F`; it is this
leaf that is false for a general `F` and true for `Opens.map h.base`.

**ROUTE.**  Write `S := Z.ringCatSheaf.obj`, `R := W.ringCatSheaf.obj`, `L := pullback`.
Three ingredients, and the meet-preservation of `Opens.map h.base` is used twice:

1. `L ((free S).obj (yoneda.obj U)) ≅ (free R).obj (yoneda.obj (h ⁻¹ᵁ U))`.  Free from the
   pin: `PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy` corepresents
   `N ↦ ((free S).obj (yoneda.obj U) ⟶ (pushforward φ).obj N)` by
   `(free R).obj (yoneda.obj (h ⁻¹ᵁ U))`, and `Adjunction.corepresentableBy` corepresents
   the same functor by `L ((free S).obj (yoneda.obj U))`; then
   `Functor.CorepresentableBy.uniqueUpToIso`.
2. `(free S).obj (yoneda.obj U) ⊗ (free S).obj (yoneda.obj U') ≅
   (free S).obj (yoneda.obj (U ⊓ U'))`, and the same on the `W` side.  Sectionwise at `V`
   this is `Free(V ≤ U) ⊗_{S(V)} Free(V ≤ U') ≅ Free(V ≤ U ⊓ U')`: in a POSET both
   `Hom`-types are subsingletons, so both sides are `S(V)` when `V ≤ U ⊓ U'` and `0`
   otherwise.  **This is the first use of binary meets, and it is the step that has no
   analogue for a general site.**
3. `h ⁻¹ᵁ (U ⊓ U') = h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U'` (`TopologicalSpace.Opens.map` preserves `⊓` — it
   is `rfl` for the underlying sets).  **Second use.**

With 1–3, both source and target of `δ` are isomorphic to
`(free R).obj (yoneda.obj (h ⁻¹ᵁ (U ⊓ U')))`.  What is then left, and it is the real work,
is to check that `δ` ITSELF is the resulting isomorphism and not some other map.  The
cheapest way found so far avoids computing `δ` on elements: `δ = (adj.homEquiv).symm ν`
with `ν = (unit ⊗ₘ unit) ≫ μ (pushforward φ)`, so `δ ≫ g` transposes to `ν ≫ (pushforward
φ).map g` (`Adjunction.homEquiv_naturality_right_symm`), and `δ` is invertible iff
`g ↦ ν ≫ (pushforward φ).map g` is bijective for every `N` — which by 1–3 and
`PresheafOfModules.freeYonedaEquiv` is a map `N.obj (op (h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U')) →
N.obj (op (h ⁻¹ᵁ (U ⊓ U')))` between two hom-sets that 1–3 identify.

**NOT VACUOUS and NOT trivially reducible.**  Take `h` a closed immersion of a
point into `𝔸¹` and `P = Q` the ideal sheaf of the point: `h^*P` is the
one-dimensional conormal space, `h^*(P ⊗ P)` is one-dimensional too, and the
comparison is an isomorphism only because the tensor product is taken over the
pulled-back ring `Γ(W, −)` and not over `Γ(Z, −)`.  Nothing here is formal in
the sense of holding for any adjunction. -/
theorem isIso_presheafModPullback_delta_freeYoneda {Z W : Scheme.{u}} (h : W ⟶ Z)
    (U U' : Z.Opens) :
    IsIso (presheafModPullbackDelta h
      ((PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U))
      ((PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U'))) :=
  sorry

/-- **THE PRESHEAF PULLBACK IS STRONG MONOIDAL ON THE SITE OF OPENS** (**PROVEN
2026-07-31** over the single generator leaf `isIso_presheafModPullback_delta_freeYoneda`;
formerly a bare sorry leaf).

No sheaf, no sheafification, no Grothendieck topology: `PresheafOfModules.pullback`
is the left adjoint of `PresheafOfModules.pushforward`, and the claim is that it
carries the pointwise tensor product of presheaves of modules to the pointwise
tensor product.

The old docstring here recorded two routes — "establish the colimit formula" and "run the
generators argument" — and recommended the first.  The second is the one that worked, and
it did not need the colimit formula at any point: what the *dévissage* needs is only that
`pullback` and `− ⊗ Q` preserve colimits, both of which are pin instances
(`Adjunction.leftAdjoint_preservesColimits`, and mathlib's `PreservesColimitsOfSize` on
`tensorLeft`/`tensorRight` for presheaves of modules).  The filtered-colimit description of
the Kan extension is never used, and the codirectedness of `{U // V ≤ h ⁻¹ᵁ U}` is replaced
by the single fact that `Opens.map` preserves `⊓`, which is where the generator leaf spends
it. -/
theorem nonempty_presheafModPullback_tensor {Z W : Scheme.{u}} (h : W ⟶ Z)
    (P Q : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    Nonempty ((presheafModPullback h).obj (P ⊗ Q) ≅
      (presheafModPullback h).obj P ⊗ (presheafModPullback h).obj Q) := by
  refine ⟨@asIso _ _ _ _ (presheafModPullbackDelta h P Q) ?_⟩
  exact isIso_pullback_delta h.c (isIso_presheafModPullback_delta_freeYoneda h) P Q

/-- **Pullback of PRESHEAVES of `𝒪`-modules along a morphism of schemes** — the
functor mathlib's `sheafificationCompPullback` moves the sheafification past.

A thin wrapper, for the same reason `modPullback` is one: it keeps the statement
below readable and pins the `F`/`φ` pair to the one coming from `h`. -/
noncomputable abbrev presheafPullback {Z W : Scheme.{u}} (h : W ⟶ Z) :
    PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ PresheafOfModules.{u} W.ringCatSheaf.obj :=
  PresheafOfModules.pullback h.toRingCatSheafHom.hom

/-- **THE PRESHEAF-LEVEL TENSOR COMPARISON** — `p(A ⊗ B) ≅ pA ⊗ pB` for the pullback of
PRESHEAVES of modules along a morphism of schemes.

**PROVEN 2026-07-31 by `exact`, because it is a VERBATIM DUPLICATE of
`nonempty_presheafModPullback_tensor` above.**  `presheafPullback h` is
`PresheafOfModules.pullback h.toRingCatSheafHom.hom` and `presheafModPullback h` is
`PresheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom h).hom` — the SAME term written
once with dot notation and once without, so the two abbreviations are equal on the nose and
the two statements differ only in the names of their bound variables.  Two agents cut the
same leaf out of `nonempty_modPullback_modTensorPic` on the same day, in the same file,
ninety lines apart, and neither could see the other's copy because nothing about the names
`presheafModPullback` / `presheafPullback` says they denote one functor.

Kept (rather than deleted) because `modPullbackSheafifyIso` and `modPullbackValIso` below
are stated in terms of `presheafPullback`; deleting it would be a rename touching those,
which is a bigger edit than a one-line delegation.  Anyone doing that rename should collapse
the two abbreviations too. -/
theorem nonempty_presheafPullback_tensor {Z W : Scheme.{u}} (h : W ⟶ Z)
    (A B : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    Nonempty ((presheafPullback h).obj (A ⊗ B) ≅
      (presheafPullback h).obj A ⊗ (presheafPullback h).obj B) :=
  nonempty_presheafModPullback_tensor h A B

/-- **`f^*(a A) ≅ a(p A)`: PULLBACK COMMUTES WITH SHEAFIFICATION** — mathlib's
`SheafOfModules.sheafificationCompPullback`, read on an object.

Free from the pin, and the piece every audit of this leaf missed. -/
noncomputable def modPullbackSheafifyIso {Z W : Scheme.{u}} (h : W ⟶ Z)
    (A : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    modPullback h ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj A) ≅
      (PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj ((presheafPullback h).obj A) :=
  (SheafOfModules.sheafificationCompPullback h.toRingCatSheafHom).app A

/-- **`f^*L ≅ a(p L.val)`** — the previous isomorphism composed with
`modSheafifyValIso`, which is what lets a SHEAF be fed to a statement about
presheaf pullback. -/
noncomputable def modPullbackValIso {Z W : Scheme.{u}} (h : W ⟶ Z) (L : Z.Modules) :
    modPullback h L ≅
      (PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).obj
        ((presheafPullback h).obj L.val) :=
  modPullbackMapIso h (modSheafifyValIso L).symm ≪≫ modPullbackSheafifyIso h L.val

/-- `modPullbackValIso`, read in `ModLM W`.  Same field-copy as
`modSheafifyValIsoLM`: `ModLM W` is a type synonym for `W.Modules`, so an
isomorphism there is the same data, but the elaborator will not see it without
being told. -/
noncomputable def modPullbackValIsoLM {Z W : Scheme.{u}} (h : W ⟶ Z) (L : Z.Modules) :
    toModLM (modPullback h L) ≅ (modLocA W).obj ((presheafPullback h).obj L.val) where
  hom := (modPullbackValIso h L).hom
  inv := (modPullbackValIso h L).inv
  hom_inv_id := (modPullbackValIso h L).hom_inv_id
  inv_hom_id := (modPullbackValIso h L).inv_hom_id

/-- `modPullbackSheafifyIso` at a tensor product, read in `ModLM W`.  Note the
left-hand side is `modPullback h (modTensor L M)` on the nose: `modTensor L M` is
`a (L.val ⊗ M.val)` by definition. -/
noncomputable def modPullbackTensorValIsoLM {Z W : Scheme.{u}} (h : W ⟶ Z) (L M : Z.Modules) :
    toModLM (modPullback h (modTensor L M)) ≅
      (modLocA W).obj ((presheafPullback h).obj (L.val ⊗ M.val)) where
  hom := (modPullbackSheafifyIso h (L.val ⊗ M.val)).hom
  inv := (modPullbackSheafifyIso h (L.val ⊗ M.val)).inv
  hom_inv_id := (modPullbackSheafifyIso h (L.val ⊗ M.val)).hom_inv_id
  inv_hom_id := (modPullbackSheafifyIso h (L.val ⊗ M.val)).inv_hom_id

/-- **PULLBACK COMMUTES WITH `modTensor`** (**PROVEN 2026-07-30** over the single
presheaf-level leaf `nonempty_presheafPullback_tensor`; formerly a bare sorry
leaf carrying a "do not dispatch, wait for the hoist" instruction).

The old note was right that this is the twin of
`Fermat.nonempty_modPullback_modTensor` in `Modularity/AmpleSheaf.lean` and
right that hoisting that declaration would have moved a leaf rather than removed
one.  What it missed is that the SHEAF-THEORETIC half of the statement is free
from the pin — `SheafOfModules.sheafificationCompPullback` — so the leaf does not
have to be waited for at all; see the section note above for the reduction, the
falsity audit on its obvious generalisation, and what is left to prove. -/
theorem nonempty_modPullback_modTensorPic {Z W : Scheme.{u}} (h : W ⟶ Z) (L M : Z.Modules) :
    Nonempty (modPullback h (modTensor L M) ≅ modTensor (modPullback h L) (modPullback h M)) := by
  obtain ⟨cmp⟩ := nonempty_presheafModPullback_tensor h L.val M.val
  refine ⟨?_⟩
  refine (SheafOfModules.sheafificationCompPullback
    (Scheme.Hom.toRingCatSheafHom h)).app (L.val ⊗ M.val) ≪≫ ?_
  refine (PresheafOfModules.sheafification (𝟙 W.ringCatSheaf.obj)).mapIso cmp ≪≫ ?_
  refine modSheafifyTensorIso _ _ ≪≫ ?_
  exact modTensorMapIso
    ((SheafOfModules.pullbackIso (Scheme.Hom.toRingCatSheafHom h)).app L).symm
    ((SheafOfModules.pullbackIso (Scheme.Hom.toRingCatSheafHom h)).app M).symm

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

/-- **PULLBACK PRESERVES INVERTIBILITY** (PROVEN 2026-07-29, and NOT a leaf).

`exists_abelJacobiPoint`'s route audit named this as the one statement blocking
`aj_pre` — "absent from this module … whoever takes this leaf should state and
prove it in the tensor-calculus section above".  Here it is, and it needs no new
leaf: every component of the chain was already proven above.

**Route.**  For `w : W` trivialize `L` on a neighbourhood `U` of `f w` and take
the preimage `f ⁻¹ᵁ U`.  Then

    (f^*L)|_{f⁻¹U} ≅ ((f⁻¹U).ι)^*(f^*L) ≅ ((f⁻¹U).ι ≫ f)^*L
                   ≅ ((f ∣_ U) ≫ U.ι)^*L ≅ (f ∣_ U)^*(U.ι^* L)
                   ≅ (f ∣_ U)^*(L|_U) ≅ (f ∣_ U)^*𝒪_U ≅ 𝒪_{f⁻¹U},

by `modRestrictPullbackIso`, `modPullbackCompIso`, mathlib's `morphismRestrict_ι`
(the base-change identity `(f⁻¹U).ι ≫ f = (f ∣_ U) ≫ U.ι`), `modPullbackCompIso`
again, `modPullbackMapIso` applied to the trivialization, and
`modPullbackUnitIso`.  Membership of `w` in `f ⁻¹ᵁ U` is definitionally
membership of `f w` in `U`.

The same chain is written as real code, with its section identity, in
`Modularity/AmpleSheaf.lean` as `trivializationOfPullback`; that module is
DOWNSTREAM, so it could not be used here and the chain is inlined instead rather
than hoisting a declaration out from under that module's live owners. -/
theorem isInvertibleSheaf_modPullback {Z W : Scheme.{u}} (f : W ⟶ Z) {L : Z.Modules}
    (hL : IsInvertibleSheaf L) : IsInvertibleSheaf (modPullback f L) := by
  intro w
  obtain ⟨U, hU, ⟨φ⟩⟩ := hL (f.base w)
  refine ⟨f ⁻¹ᵁ U, hU, ⟨?_⟩⟩
  exact modRestrictPullbackIso (f ⁻¹ᵁ U).ι (modPullback f L) ≪≫
    modPullbackCompIso (f ⁻¹ᵁ U).ι f L ≪≫
    modPullbackCongrIso (morphismRestrict_ι f U).symm L ≪≫
    (modPullbackCompIso (f ∣_ U) U.ι L).symm ≪≫
    modPullbackMapIso (f ∣_ U) ((modRestrictPullbackIso U.ι L).symm ≪≫ φ) ≪≫
    modPullbackUnitIso (f ∣_ U)

/-- **THE MIDDLE-FOUR INTERCHANGE**, `(L ⊗ M) ⊗ N ≅ (L ⊗ N) ⊗ M` (PROVEN over
`nonempty_modTensor_assocPic` and the braiding).

Exactly the "assoc twice plus one braiding" the section header prices.  It is
what makes `RelPicEquiv` a congruence for `⊗` on the right
(`relPicEquiv_tensor_right`): a twist by `π^*N` on the left factor has to be
moved past the new right factor `M`. -/
theorem nonempty_modTensor_middleFourPic {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor (modTensor L N) M) := by
  obtain ⟨a1⟩ := nonempty_modTensor_assoc L M N
  obtain ⟨a2⟩ := nonempty_modTensor_assoc L N M
  exact ⟨a1 ≪≫ modTensorMapIso (Iso.refl L) (modTensorSymmIso M N) ≪≫ a2.symm⟩

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

/-! #### `L^∨` AS A SHEAF OF COMPATIBLE FAMILIES, AND ITS EVALUATION PAIRING

**Built 2026-07-30, and this is the route `exists_modDual`'s own docstring below
prescribed** ("the dual as a presheaf of COMPATIBLE FAMILIES … What then remains:
the sheaf condition for `L^∨`, its local triviality, and `ev` out of
`PresheafOfModules.Monoidal.tensorObj` through the sheafification adjunction").

Two of those three are DONE here, unconditionally and for an arbitrary
`L : Z.Modules` — no invertibility hypothesis is used anywhere in this
subsection:

* `ModDual.modDualPre_isSheaf` — `L^∨` really is a sheaf.  This is the deep half:
  a compatible family over `U` is glued from compatible families over a cover by
  gluing its VALUES in `𝒪_Z`, one open `V ≤ U` at a time, and `𝒪_Z`'s own
  `TopCat.Sheaf.existsUnique_gluing'` supplies each value.  Additivity,
  linearity, naturality and the uniqueness of the glued family are then all
  instances of `𝒪_Z`-separatedness (`TopCat.Sheaf.eq_of_locally_eq'`, wrapped as
  `ModDual.sec_ext`).
* `modDualEv` — the evaluation `L ⊗ L^∨ ⟶ 𝒪_Z`.  Because `L^∨` is a sheaf and
  not a sheafification, this is direct: a bilinear pairing at each open,
  `ModDual.modDualEvPre`, then `PresheafOfModules.sheafification` applied to it
  and `modSheafifyValIso` on the target.

What remains is exactly the LOCAL half, isolated as the two leaves
`isInvertibleSheaf_modDual` and `isIso_modDualEv` below.

**WHY THE INDEXING IS `{V : Z.Opens // V ≤ U}` AND NOT `U.Opens`, recorded
because it is the whole reason this construction is possible at all.**  The
naive dual `U ↦ (L.restrict U.ι ⟶ modUnit U)` is not a presheaf: restriction of
`𝒪`-modules is only pseudo-functorial.  Indexing by AMBIENT opens below `U` and
restricting by FORGETTING makes `L^∨` strictly functorial — `map_id` and
`map_comp` are discharged by `cat_disch` with nothing to say — and keeps every
section a map between `Z`-modules, so `Γ(Z,·)`-linearity is available
throughout.

**AND THE PRICE, measured 2026-07-30 — read this before touching
`Scheme.Modules.restrict`.**  `Γ(L.restrict U.ι, V₁)` and `Γ(L, U.ι ''ᵁ V₁)` are
the same TYPE (`Scheme.Modules.restrict_obj` is `rfl`) carrying two different
`Module` instances, defeq only at DEFAULT transparency: `restrictFunctor` is
`SheafOfModules.pushforward` along `(U.ι.appIso _).inv`, and `Iso.inv` is not
`@[expose]`d, so unfolding it is not available downstream of mathlib.
Consequences, all observed:

* `rw`/`simp` cannot cross the boundary — instance arguments differ
  syntactically and unification runs at `instances` transparency.  The
  diagnostic is Lean's own "The target expression is not type-correct under the
  `instances` transparency level".
* `exact` cannot cross it either, and says so: "the following definitions were
  not unfolded because their definition is not exposed: `inv`".
  `set_option backward.isDefEq.respectTransparency false` does NOT help — this
  is an exposure barrier, not a transparency one.
* What DOES work is mathlib's own lemmas about the boundary
  (`Scheme.Modules.Hom.app_smul`, `Scheme.Modules.smul_restrictAppIso_hom`,
  `Scheme.Opens.ι_appIso : U.ι.appIso V = Iso.refl _`,
  `Scheme.Opens.toScheme_presheaf_obj`), used as rewrites rather than relied on
  for defeq.  A `rfl`-proved bridge lemma stated inside this module does NOT
  work: instance search silently picks the AMBIENT instance on both sides, so
  the bridge is vacuous and proves nothing.

That is why `isInvertibleSheaf_modDual` below is a separate leaf rather than
three lines: every step of it crosses this boundary. -/

namespace ModDual

/-- Restriction of a section of the structure sheaf, twice, is restriction once. -/
lemma res_res {Z : Scheme.{u}} {V W U : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (r : Γ(Z, U)) :
    Z.presheaf.map (homOfLE h1).op (Z.presheaf.map (homOfLE h2).op r) =
      Z.presheaf.map (homOfLE (h1.trans h2)).op r := by
  rw [← CommRingCat.comp_apply, ← Z.presheaf.map_comp]
  congr 1

/-- Restriction of a section of `L`, twice, is restriction once. -/
lemma resL_resL {Z : Scheme.{u}} (L : Z.Modules) {V W U : Z.Opens} (h1 : W ≤ V) (h2 : V ≤ U)
    (x : Γ(L, U)) :
    L.presheaf.map (homOfLE h1).op (L.presheaf.map (homOfLE h2).op x) =
      L.presheaf.map (homOfLE (h1.trans h2)).op x := by
  rw [← ConcreteCategory.comp_apply, ← L.presheaf.map_comp]
  congr 1

/-- Restricting along `V ≤ V` does nothing: `Z.Opens` is a poset, so the hom is
the identity by `Subsingleton.elim`. -/
lemma res_self {Z : Scheme.{u}} {V : Z.Opens} (h : V ≤ V) (r : Γ(Z, V)) :
    Z.presheaf.map (homOfLE h).op r = r := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 _), CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]

/-- `res_self` for sections of `L`: restricting along `V ≤ V` does nothing. -/
lemma resL_self {Z : Scheme.{u}} (L : Z.Modules) {V : Z.Opens} (h : V ≤ V) (x : Γ(L, V)) :
    L.presheaf.map (homOfLE h).op x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 _), CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

/-- The ambient type of a dual section over `U`: a functional on `Γ(L, V)` for
every ambient open `V ≤ U`. -/
abbrev DualPi {Z : Scheme.{u}} (L : Z.Modules) (U : Z.Opens) : Type u :=
  ∀ (V : {V : Z.Opens // V ≤ U}), (Γ(L, V.1) →ₗ[Γ(Z, V.1)] Γ(Z, V.1))

/-- The compatible families: the subgroup of `DualPi` cut out by naturality. -/
def dualSub {Z : Scheme.{u}} (L : Z.Modules) (U : Z.Opens) : AddSubgroup (DualPi L U) where
  carrier := {φ | ∀ (V W : {V : Z.Opens // V ≤ U}) (hWV : W.1 ≤ V.1) (x : Γ(L, V.1)),
    φ W (L.presheaf.map (homOfLE hWV).op x) =
      Z.presheaf.map (homOfLE hWV).op (φ V x)}
  zero_mem' := by intro V W hWV x; simp
  add_mem' := by
    intro a b ha hb V W hWV x
    simp only [Pi.add_apply, LinearMap.add_apply, ha V W hWV x, hb V W hWV x, map_add]
  neg_mem' := by
    intro a ha V W hWV x
    simp only [Pi.neg_apply, LinearMap.neg_apply, ha V W hWV x, map_neg]

/-- **Sections of the dual sheaf over `U`.** -/
def DualSec {Z : Scheme.{u}} (L : Z.Modules) (U : Z.Opens) : Type u := dualSub L U

noncomputable instance {Z : Scheme.{u}} (L : Z.Modules) (U : Z.Opens) :
    AddCommGroup (DualSec L U) :=
  inferInstanceAs (AddCommGroup (dualSub L U))

namespace DualSec

variable {Z : Scheme.{u}} {L : Z.Modules} {U : Z.Opens}

/-- The underlying family of functionals. -/
def φ (a : DualSec L U) : DualPi L U := a.1

@[ext] lemma ext {a b : DualSec L U} (h : ∀ V, a.φ V = b.φ V) : a = b :=
  Subtype.ext (funext h)

@[simp] lemma add_φ (a b : DualSec L U) (V) : (a + b).φ V = a.φ V + b.φ V := rfl
@[simp] lemma zero_φ (V) : (0 : DualSec L U).φ V = 0 := rfl

lemma compat (a : DualSec L U) (V W : {V : Z.Opens // V ≤ U}) (hWV : W.1 ≤ V.1) (x : Γ(L, V.1)) :
    a.φ W (L.presheaf.map (homOfLE hWV).op x) =
      Z.presheaf.map (homOfLE hWV).op (a.φ V x) := a.2 V W hWV x

/-- Scalar multiplication: restrict the scalar to each `V` and scale there. -/
noncomputable instance : SMul Γ(Z, U) (DualSec L U) where
  smul r a := ⟨fun V => (Z.presheaf.map (homOfLE V.2).op r) • a.φ V, by
    intro V W hWV x
    simp only [LinearMap.smul_apply, a.compat V W hWV x, smul_eq_mul, map_mul,
      res_res hWV V.2 r]⟩

@[simp] lemma smul_φ (r : Γ(Z, U)) (a : DualSec L U) (V : {V : Z.Opens // V ≤ U}) :
    (r • a).φ V = (Z.presheaf.map (homOfLE V.2).op r) • a.φ V := rfl

noncomputable instance : Module Γ(Z, U) (DualSec L U) where
  one_smul a := by ext V; simp
  mul_smul r s a := by ext V; simp [mul_smul]
  smul_zero r := by ext V; simp
  smul_add r a b := by ext V; simp
  add_smul r s a := by ext V; simp [add_smul]
  zero_smul a := by ext V; simp

/-- Restriction of a compatible family along `U' ≤ U`: FORGET the opens that are
not below `U'`.  This is what makes `L^∨` strictly functorial. -/
noncomputable def res {U' : Z.Opens} (h : U' ≤ U) (a : DualSec L U) : DualSec L U' :=
  ⟨fun V => a.φ ⟨V.1, V.2.trans h⟩,
    fun V W hWV x => a.compat ⟨V.1, V.2.trans h⟩ ⟨W.1, W.2.trans h⟩ hWV x⟩

@[simp] lemma res_φ {U' : Z.Opens} (h : U' ≤ U) (a : DualSec L U)
    (V : {V : Z.Opens // V ≤ U'}) : (res h a).φ V = a.φ ⟨V.1, V.2.trans h⟩ := rfl

lemma res_smul {U' : Z.Opens} (h : U' ≤ U) (r : Γ(Z, U)) (a : DualSec L U) :
    res h (r • a) = (Z.presheaf.map (homOfLE h).op r) • res h a := by
  refine DualSec.ext (fun V => ?_)
  simp only [res_φ, smul_φ, res_res V.2 h r]

end DualSec

/-- The `RingCat`-keyed module structure the presheaf-of-modules API asks for. -/
noncomputable instance dualSecModule' {Z : Scheme.{u}} (L : Z.Modules) (U : (Opens Z)ᵒᵖ) :
    Module ↑(Z.ringCatSheaf.obj.obj U) (DualSec L U.unop) :=
  inferInstanceAs (Module Γ(Z, U.unop) (DualSec L U.unop))

/-- **The dual PRESHEAF of modules `L^∨`.** -/
noncomputable def modDualPre {Z : Scheme.{u}} (L : Z.Modules) : Z.PresheafOfModules where
  obj U := ModuleCat.of _ (DualSec L U.unop)
  map {U U'} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (Z.ringCatSheaf.obj.map f).hom).obj
        (ModuleCat.of _ (DualSec L U'.unop)))
    { toFun := DualSec.res (leOfHom f.unop)
      map_add' := fun a b => rfl
      map_smul' := fun r a => DualSec.res_smul (leOfHom f.unop) r a }

@[simp] lemma modDualPre_presheaf_map_apply {Z : Scheme.{u}} (L : Z.Modules)
    {U U' : (Opens Z)ᵒᵖ} (f : U ⟶ U') (a : DualSec L U.unop) :
    (modDualPre L).presheaf.map f a = DualSec.res (leOfHom f.unop) a := rfl

/-! ##### The sheaf condition for `L^∨` -/

section SheafCondition

variable {Z : Scheme.{u}} {L : Z.Modules} {ι : Type u} {U : ι → Z.Opens}
  {sf : ∀ i, DualSec L (U i)}

/-- The compatibility hypothesis of the gluing axiom, unpacked to sections: on an
open below both `U i` and `U j`, the two families are the SAME functional. -/
lemma dual_compat (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    (i j : ι) {W : Z.Opens} (hi : W ≤ U i) (hj : W ≤ U j) (x : Γ(L, W)) :
    (sf i).φ ⟨W, hi⟩ x = (sf j).φ ⟨W, hj⟩ x :=
  congrArg (fun f => f x)
    (congrArg (fun a => DualSec.φ a ⟨W, le_inf hi hj⟩) (h i j))

variable (U) in
/-- `V ⊓ U i` covers `V`, for `V` below the sup.  Frame distributivity. -/
lemma le_iSup_inf {V : Z.Opens} (hV : V ≤ iSup U) : V ≤ ⨆ i, V ⊓ U i := by
  rw [← inf_iSup_eq]
  exact le_inf le_rfl hV

/-- Restriction of a section of `L`. -/
noncomputable abbrev resX {V : Z.Opens} (x : Γ(L, V)) (W : Z.Opens) (h : W ≤ V) : Γ(L, W) :=
  L.presheaf.map (homOfLE h).op x

/-- The local values that will be glued to define the glued functional at `x`. -/
noncomputable def glueFam (sf : ∀ i, DualSec L (U i)) {V : Z.Opens} (x : Γ(L, V)) (i : ι) :
    Γ(Z, V ⊓ U i) :=
  (sf i).φ ⟨V ⊓ U i, inf_le_right⟩ (resX x _ (inf_le_left : V ⊓ U i ≤ V))

/-- The local values agree on overlaps: naturality of each `sf i` moves both to
`(V ⊓ U i) ⊓ (V ⊓ U j)`, where `dual_compat` identifies them. -/
lemma glueFam_compat (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V : Z.Opens} (x : Γ(L, V)) (i j : ι) :
    Z.presheaf.map (homOfLE (inf_le_left : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U i)).op
        (glueFam sf x i) =
      Z.presheaf.map (homOfLE (inf_le_right : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U j)).op
        (glueFam sf x j) := by
  rw [glueFam, glueFam,
    ← (sf i).compat ⟨V ⊓ U i, inf_le_right⟩
      ⟨(V ⊓ U i) ⊓ (V ⊓ U j), le_trans inf_le_left inf_le_right⟩ inf_le_left _,
    ← (sf j).compat ⟨V ⊓ U j, inf_le_right⟩
      ⟨(V ⊓ U i) ⊓ (V ⊓ U j), le_trans inf_le_right inf_le_right⟩ inf_le_right _,
    resX, resX, resL_resL, resL_resL]
  exact dual_compat h i j _ _ _

/-- The value of the glued functional at `x`, from `𝒪_Z`'s own gluing. -/
noncomputable def glueVal (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V : Z.Opens} (hV : V ≤ iSup U) (x : Γ(L, V)) : Γ(Z, V) :=
  (Z.sheaf.existsUnique_gluing' (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (le_iSup_inf U hV) (glueFam sf x) (glueFam_compat h x)).choose

lemma glueVal_res (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V : Z.Opens} (hV : V ≤ iSup U) (x : Γ(L, V)) (i : ι) :
    Z.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op (glueVal h hV x) =
      glueFam sf x i :=
  (Z.sheaf.existsUnique_gluing' (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (le_iSup_inf U hV) (glueFam sf x) (glueFam_compat h x)).choose_spec.1 i

/-- Two sections of `𝒪_Z` over `V` agreeing on every `V ⊓ U i` are equal.  This
single separatedness statement discharges every remaining obligation below. -/
lemma sec_ext {V : Z.Opens} (hV : V ≤ iSup U) (r s : Γ(Z, V))
    (hrs : ∀ i, Z.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op r =
      Z.presheaf.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op s) : r = s :=
  Z.sheaf.eq_of_locally_eq' (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (le_iSup_inf U hV) r s hrs

lemma glueVal_add (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V : Z.Opens} (hV : V ≤ iSup U) (x y : Γ(L, V)) :
    glueVal h hV (x + y) = glueVal h hV x + glueVal h hV y := by
  refine sec_ext hV _ _ (fun i => ?_)
  rw [map_add, glueVal_res, glueVal_res, glueVal_res, glueFam, glueFam, glueFam, resX, resX, resX,
    map_add, map_add]

lemma glueVal_smul (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V : Z.Opens} (hV : V ≤ iSup U) (r : Γ(Z, V)) (x : Γ(L, V)) :
    glueVal h hV (r • x) = r • glueVal h hV x := by
  refine sec_ext hV _ _ (fun i => ?_)
  rw [glueVal_res, glueFam, resX, Scheme.Modules.map_smul, LinearMap.map_smul]
  simp only [smul_eq_mul]
  rw [map_mul, glueVal_res, glueFam, resX]

/-- Naturality of the glued family in the open. -/
lemma glueVal_nat (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    {V W : Z.Opens} (hV : V ≤ iSup U) (hWV : W ≤ V) (x : Γ(L, V)) :
    glueVal h (hWV.trans hV) (resX x W hWV) =
      Z.presheaf.map (homOfLE hWV).op (glueVal h hV x) := by
  refine sec_ext (hWV.trans hV) _ _ (fun i => ?_)
  rw [glueVal_res, glueFam, resX, resX, resL_resL, res_res,
    ← res_res (inf_le_inf_right (U i) hWV) (inf_le_left : V ⊓ U i ≤ V),
    glueVal_res, glueFam, resX, ← (sf i).compat ⟨V ⊓ U i, inf_le_right⟩
      ⟨W ⊓ U i, inf_le_right⟩ (inf_le_inf_right (U i) hWV) _, resL_resL]

/-- The glued compatible family. -/
noncomputable def glueSec (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf) :
    DualSec L (iSup U) :=
  ⟨fun V =>
    { toFun := fun x => glueVal h V.2 x
      map_add' := glueVal_add h V.2
      map_smul' := glueVal_smul h V.2 },
   fun V _ hWV x => glueVal_nat h V.2 hWV x⟩

@[simp] lemma glueSec_φ (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    (V : {V : Z.Opens // V ≤ iSup U}) (x : Γ(L, V.1)) :
    (glueSec h).φ V x = glueVal h V.2 x := rfl

lemma glueSec_isGluing (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf) :
    TopCat.Presheaf.IsGluing (modDualPre L).presheaf U sf (glueSec h) := by
  intro i
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  refine sec_ext (V.2.trans (le_iSup U i)) _ _ (fun j => ?_)
  rw [modDualPre_presheaf_map_apply, DualSec.res_φ, glueSec_φ, glueVal_res, glueFam, resX,
    ← (sf i).compat V ⟨V.1 ⊓ U j, le_trans inf_le_left V.2⟩ inf_le_left x]
  exact dual_compat h j i _ _ _

lemma glueSec_unique (h : TopCat.Presheaf.IsCompatible (modDualPre L).presheaf U sf)
    (s : DualSec L (iSup U))
    (hs : TopCat.Presheaf.IsGluing (modDualPre L).presheaf U sf s) : s = glueSec h := by
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  refine sec_ext V.2 _ _ (fun i => ?_)
  rw [glueSec_φ, glueVal_res, glueFam, resX,
    ← s.compat V ⟨V.1 ⊓ U i, le_trans inf_le_left V.2⟩ inf_le_left x]
  exact congrArg (fun f => f (resX x (V.1 ⊓ U i) inf_le_left))
    (congrArg (fun a => DualSec.φ a ⟨V.1 ⊓ U i, inf_le_right⟩) (hs i))

end SheafCondition

/-- **`L^∨` IS A SHEAF** (PROVEN 2026-07-30, for an arbitrary `L`). -/
theorem modDualPre_isSheaf {Z : Scheme.{u}} (L : Z.Modules) :
    TopCat.Presheaf.IsSheaf (X := Z.toPresheafedSpace.carrier) (modDualPre L).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf h
  exact ⟨glueSec h, glueSec_isGluing h, fun s hs => glueSec_unique h s hs⟩

/-- Evaluating a scaled dual section against a section, over the SAME open. -/
lemma dualSec_smul_apply_self {Z : Scheme.{u}} {L : Z.Modules} (V : Z.Opens) (r : Γ(Z, V))
    (ψ : DualSec L V) (x : Γ(L, V)) :
    (r • ψ).φ ⟨V, le_rfl⟩ x = r * ψ.φ ⟨V, le_rfl⟩ x := by
  rw [DualSec.smul_φ, LinearMap.smul_apply, res_self, smul_eq_mul]

/-- **THE EVALUATION PAIRING, at the level of presheaves**: `L ⊗ L^∨ ⟶ 𝒪_Z`,
`x ⊗ ψ ↦ ψ_V(x)`.  Naturality is exactly the compatibility clause of `ψ`. -/
noncomputable def modDualEvPre {Z : Scheme.{u}} (L : Z.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val (modDualPre L) ⟶
      (modUnit Z).val where
  app V := ModuleCat.MonoidalCategory.tensorLift
    (fun x ψ => DualSec.φ ψ ⟨V.unop, le_rfl⟩ x)
    (fun x y ψ => map_add (DualSec.φ ψ ⟨V.unop, le_rfl⟩) x y)
    (fun r x ψ => (DualSec.φ ψ ⟨V.unop, le_rfl⟩).map_smul r x)
    (fun _ _ _ => rfl)
    (fun r x ψ => dualSec_smul_apply_self V.unop r ψ x)
  naturality {V V'} f := ModuleCat.MonoidalCategory.tensor_ext (fun x ψ =>
    ψ.compat ⟨V.unop, le_rfl⟩ ⟨V'.unop, leOfHom f.unop⟩ (leOfHom f.unop) x)

end ModDual

/-- **THE DUAL SHEAF `L^∨ = Hom_{𝒪_Z}(L, 𝒪_Z)`** (PROVEN 2026-07-30) — the
presheaf of compatible families `ModDual.modDualPre`, together with
`ModDual.modDualPre_isSheaf`. -/
noncomputable def modDual {Z : Scheme.{u}} (L : Z.Modules) : Z.Modules :=
  ⟨ModDual.modDualPre L, ModDual.modDualPre_isSheaf L⟩

/-- **THE EVALUATION PAIRING** `ev : L ⊗ L^∨ ⟶ 𝒪_Z` (PROVEN 2026-07-30) —
sheafify `ModDual.modDualEvPre` and use that `𝒪_Z` is already a sheaf. -/
noncomputable def modDualEv {Z : Scheme.{u}} (L : Z.Modules) :
    modTensor L (modDual L) ⟶ modUnit Z :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (ModDual.modDualEvPre L) ≫
    (modSheafifyValIso (modUnit Z)).hom

/-! ### The rank-one bridge across the `restrict` boundary

`L` trivialized on `U` is free of rank one on every AMBIENT open `V ≤ U`, and
this section says so in ambient sections — which is what both `modDual` leaves
below need and what the subsection docstring above prices as the real cost.

The crossing lemma is `smul_restrict_eq`, and it is the whole trick: state the
scalar action in BUNDLED `Scheme.Modules.smul` form, so the two sides pin their
two different modules instead of letting instance search collapse them; then
mathlib's `smul_restrictAppIso_hom_apply` plus `Scheme.Opens.ι_appIso` proves
it.  Everything after that is transport along
`U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V` for `V ≤ U`, done in one direction only
(`le_image_preimage` plus `Scheme.Hom.image_preimage_le`), so no equality of
opens is ever rewritten. -/

namespace ModDual

section Bridge

variable {Z : Scheme.{u}} {L : Z.Modules} {U : Z.Opens}

/-- **THE CROSSING LEMMA.**  The `Γ(U,·)`-action on sections of `L.restrict U.ι`
and the `Γ(Z,·)`-action on the corresponding ambient sections of `L` agree. -/
lemma smul_restrict_eq (W : (U : Scheme.{u}).Opens) (r : Γ((U : Scheme.{u}), W))
    (x : Γ(L.restrict U.ι, W)) :
    ((L.restrict U.ι).smul r).hom x = (L.smul r).hom x := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι L W r x
  rw [Scheme.Opens.ι_appIso] at h
  exact h

/-- A morphism `L|_U ⟶ 𝒪_U`, read as a map of AMBIENT sections. -/
noncomputable def trAt (ψ : L.restrict U.ι ⟶ modUnit (U : Scheme.{u}))
    (W : (U : Scheme.{u}).Opens) (x : Γ(L, U.ι ''ᵁ W)) : Γ(Z, U.ι ''ᵁ W) :=
  ψ.val.app (op W) x

/-- A morphism `𝒪_U ⟶ L|_U`, read as a map of AMBIENT sections. -/
noncomputable def trAtInv (χ : modUnit (U : Scheme.{u}) ⟶ L.restrict U.ι)
    (W : (U : Scheme.{u}).Opens) (r : Γ(Z, U.ι ''ᵁ W)) : Γ(L, U.ι ''ᵁ W) :=
  χ.val.app (op W) r

lemma trAt_add (ψ : L.restrict U.ι ⟶ modUnit (U : Scheme.{u}))
    (W : (U : Scheme.{u}).Opens) (x y : Γ(L, U.ι ''ᵁ W)) :
    trAt ψ W (x + y) = trAt ψ W x + trAt ψ W y :=
  map_add (ψ.val.app (op W)).hom x y

lemma trAt_smul (ψ : L.restrict U.ι ⟶ modUnit (U : Scheme.{u}))
    (W : (U : Scheme.{u}).Opens) (r : Γ(Z, U.ι ''ᵁ W)) (x : Γ(L, U.ι ''ᵁ W)) :
    trAt ψ W (r • x) = r * trAt ψ W x := by
  calc trAt ψ W (r • x)
      = trAt ψ W ((L.smul r).hom x) := by rw [Scheme.Modules.smul_apply]
    _ = trAt ψ W (((L.restrict U.ι).smul r).hom x) :=
        congrArg (trAt ψ W) (smul_restrict_eq W r x).symm
    _ = r * trAt ψ W x := Scheme.Modules.Hom.app_smul ψ r x

lemma trAt_nat (ψ : L.restrict U.ι ⟶ modUnit (U : Scheme.{u}))
    {W W' : (U : Scheme.{u}).Opens} (h : W' ≤ W) (x : Γ(L, U.ι ''ᵁ W)) :
    trAt ψ W' (L.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι h)).op x) =
      Z.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι h)).op (trAt ψ W x) :=
  PresheafOfModules.naturality_apply ψ.val (homOfLE h).op x

lemma trAtInv_trAt (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (W : (U : Scheme.{u}).Opens) (x : Γ(L, U.ι ''ᵁ W)) :
    trAtInv φ.inv W (trAt φ.hom W x) = x := by
  show ((φ.hom ≫ φ.inv).val.app (op W)) x = x
  rw [φ.hom_inv_id]
  rfl

lemma trAt_trAtInv (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (W : (U : Scheme.{u}).Opens) (r : Γ(Z, U.ι ''ᵁ W)) :
    trAt φ.hom W (trAtInv φ.inv W r) = r := by
  show ((φ.inv ≫ φ.hom).val.app (op W)) r = r
  rw [φ.inv_hom_id]
  rfl

lemma le_image_preimage {V : Z.Opens} (hV : V ≤ U) : V ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ V) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf hV le_rfl

section
variable (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))

/-- The trivialization read at an AMBIENT open `V ≤ U`. -/
noncomputable def tr {V : Z.Opens} (hV : V ≤ U) (x : Γ(L, V)) : Γ(Z, V) :=
  Z.presheaf.map (homOfLE (le_image_preimage hV)).op
    (trAt φ.hom (U.ι ⁻¹ᵁ V) (L.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x))

/-- The inverse trivialization read at an AMBIENT open `V ≤ U`. -/
noncomputable def trInv {V : Z.Opens} (hV : V ≤ U) (r : Γ(Z, V)) : Γ(L, V) :=
  L.presheaf.map (homOfLE (le_image_preimage hV)).op
    (trAtInv φ.inv (U.ι ⁻¹ᵁ V) (Z.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op r))

lemma tr_add {V : Z.Opens} (hV : V ≤ U) (x y : Γ(L, V)) :
    tr φ hV (x + y) = tr φ hV x + tr φ hV y := by
  simp only [tr, map_add, trAt_add]

lemma tr_smul {V : Z.Opens} (hV : V ≤ U) (r : Γ(Z, V)) (x : Γ(L, V)) :
    tr φ hV (r • x) = r * tr φ hV x := by
  rw [tr, tr, Scheme.Modules.map_smul, trAt_smul, map_mul, res_res, res_self]

lemma trInv_tr {V : Z.Opens} (hV : V ≤ U) (x : Γ(L, V)) : trInv φ hV (tr φ hV x) = x := by
  rw [trInv, tr, res_res, res_self, trAtInv_trAt, resL_resL, resL_self]

lemma tr_trInv {V : Z.Opens} (hV : V ≤ U) (r : Γ(Z, V)) : tr φ hV (trInv φ hV r) = r := by
  rw [trInv, tr, resL_resL, resL_self, trAt_trAtInv, res_res, res_self]

lemma tr_injective {V : Z.Opens} (hV : V ≤ U) : Function.Injective (tr φ hV) :=
  Function.LeftInverse.injective (trInv_tr φ hV)

lemma tr_nat {V W : Z.Opens} (hV : V ≤ U) (hWV : W ≤ V) (x : Γ(L, V)) :
    tr φ (hWV.trans hV) (L.presheaf.map (homOfLE hWV).op x) =
      Z.presheaf.map (homOfLE hWV).op (tr φ hV x) := by
  have hpre : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ V := fun a ha => hWV ha
  rw [tr, tr, resL_resL,
    ← resL_resL L (Scheme.Hom.image_mono U.ι hpre) (U.ι.image_preimage_le V),
    trAt_nat, res_res, res_res]
  exact hpre

/-- The local generator: the preimage of `1`. -/
noncomputable def gen {V : Z.Opens} (hV : V ≤ U) : Γ(L, V) := trInv φ hV 1

lemma tr_gen {V : Z.Opens} (hV : V ≤ U) : tr φ hV (gen φ hV) = 1 := tr_trInv φ hV 1

/-- **`L` IS FREE OF RANK ONE ON `U`, IN AMBIENT SECTIONS.** -/
lemma eq_smul_gen {V : Z.Opens} (hV : V ≤ U) (x : Γ(L, V)) :
    x = tr φ hV x • gen φ hV := by
  refine tr_injective φ hV ?_
  rw [tr_smul, tr_gen, mul_one]

lemma gen_res {V W : Z.Opens} (hV : V ≤ U) (hWV : W ≤ V) :
    L.presheaf.map (homOfLE hWV).op (gen φ hV) = gen φ (hWV.trans hV) := by
  refine tr_injective φ (hWV.trans hV) ?_
  rw [tr_nat (hV := hV), tr_gen, tr_gen, map_one]

/-- **THE FORWARD MAP** `L^∨(A) ⟶ 𝒪(A)` for `A ≤ U`: evaluate against the
local generator. -/
noncomputable def dualFwd {A : Z.Opens} (hA : A ≤ U) (ψ : DualSec L A) : Γ(Z, A) :=
  ψ.φ ⟨A, le_rfl⟩ (gen φ hA)

/-- The functional attached to `r : Γ(Z, A)` at an open `V ≤ A`. -/
noncomputable def dualBwdMap {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A))
    (V : {V : Z.Opens // V ≤ A}) : Γ(L, V.1) →ₗ[Γ(Z, V.1)] Γ(Z, V.1) where
  toFun x := tr φ (V.2.trans hA) x * Z.presheaf.map (homOfLE V.2).op r
  map_add' x y := by rw [tr_add, add_mul]
  map_smul' c x := by rw [tr_smul]; simp [mul_assoc]

@[simp] lemma dualBwdMap_apply {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A))
    (V : {V : Z.Opens // V ≤ A}) (x : Γ(L, V.1)) :
    dualBwdMap φ hA r V x = tr φ (V.2.trans hA) x * Z.presheaf.map (homOfLE V.2).op r := rfl

/-- **THE BACKWARD MAP** `𝒪(A) ⟶ L^∨(A)`: the functional `x ↦ tr(x) · r`. -/
noncomputable def dualBwd {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A)) : DualSec L A :=
  ⟨dualBwdMap φ hA r, fun V W hWV x => by
    rw [dualBwdMap_apply, dualBwdMap_apply, tr_nat (hV := V.2.trans hA) (hWV := hWV),
      map_mul, res_res]⟩

@[simp] lemma dualBwd_φ {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A))
    (V : {V : Z.Opens // V ≤ A}) (x : Γ(L, V.1)) :
    (dualBwd φ hA r).φ V x = tr φ (V.2.trans hA) x * Z.presheaf.map (homOfLE V.2).op r := rfl

lemma dualFwd_add {A : Z.Opens} (hA : A ≤ U) (ψ χ : DualSec L A) :
    dualFwd φ hA (ψ + χ) = dualFwd φ hA ψ + dualFwd φ hA χ := by
  simp only [dualFwd, DualSec.add_φ, LinearMap.add_apply]

lemma dualFwd_smul {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A)) (ψ : DualSec L A) :
    dualFwd φ hA (r • ψ) = r * dualFwd φ hA ψ :=
  dualSec_smul_apply_self A r ψ (gen φ hA)

lemma dualFwd_dualBwd {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A)) :
    dualFwd φ hA (dualBwd φ hA r) = r := by
  rw [dualFwd, dualBwd_φ, tr_gen, res_self, one_mul]

lemma dualBwd_dualFwd {A : Z.Opens} (hA : A ≤ U) (ψ : DualSec L A) :
    dualBwd φ hA (dualFwd φ hA ψ) = ψ := by
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  have hg : ψ.φ V (gen φ (V.2.trans hA)) =
      Z.presheaf.map (homOfLE V.2).op (dualFwd φ hA ψ) := by
    rw [dualFwd, ← gen_res φ hA V.2, ψ.compat ⟨A, le_rfl⟩ V V.2]
  rw [dualBwd_φ, ← hg, ← smul_eq_mul, ← LinearMap.map_smul]
  exact congrArg (ψ.φ V) (eq_smul_gen φ (V.2.trans hA) x).symm

lemma dualFwd_nat {A A' : Z.Opens} (hA : A ≤ U) (h : A' ≤ A) (ψ : DualSec L A) :
    dualFwd φ (h.trans hA) (DualSec.res h ψ) =
      Z.presheaf.map (homOfLE h).op (dualFwd φ hA ψ) := by
  rw [dualFwd, dualFwd, DualSec.res_φ, ← gen_res φ hA h,
    ψ.compat ⟨A, le_rfl⟩ ⟨A', h⟩ h (gen φ hA)]

/-- **`L^∨` IS FREE OF RANK ONE ON `U`**, as an additive equivalence at each
ambient open `A ≤ U`. -/
noncomputable def dualEquivAt {A : Z.Opens} (hA : A ≤ U) : DualSec L A ≃+ Γ(Z, A) where
  toFun := dualFwd φ hA
  invFun := dualBwd φ hA
  left_inv := dualBwd_dualFwd φ hA
  right_inv := dualFwd_dualBwd φ hA
  map_add' := dualFwd_add φ hA

/-- The scalar action crossing the `restrict` boundary, at `modDual L`. -/
lemma dualFwd_smul_restrict (W : (U : Scheme.{u}).Opens) (r : Γ((U : Scheme.{u}), W))
    (ψ : Γ((modDual L).restrict U.ι, W)) :
    dualFwd φ (U.ι_image_le W) ((((modDual L).restrict U.ι).smul r).hom ψ) =
      ((modUnit (U : Scheme.{u})).smul r).hom (dualFwd φ (U.ι_image_le W) ψ) :=
  (congrArg (dualFwd φ (U.ι_image_le W)) (smul_restrict_eq (L := modDual L) W r ψ)).trans
    (dualFwd_smul φ (U.ι_image_le W) r ψ)

/-- Naturality of `dualFwd` across the `restrict` boundary. -/
lemma dualFwd_map_restrict {W W' : (U : Scheme.{u}).Opens} (h : W' ≤ W)
    (ψ : Γ((modDual L).restrict U.ι, W)) :
    dualFwd φ (U.ι_image_le W') (((modDual L).restrict U.ι).presheaf.map (homOfLE h).op ψ) =
      Z.presheaf.map (homOfLE (Scheme.Hom.image_mono U.ι h)).op
        (dualFwd φ (U.ι_image_le W) ψ) :=
  dualFwd_nat φ (U.ι_image_le W) (Scheme.Hom.image_mono U.ι h) ψ

set_option maxHeartbeats 1000000 in
/-- **`L^∨` IS TRIVIAL ON A TRIVIALIZING OPEN OF `L`.**  Note
`Γ((modDual L).restrict U.ι, W) = DualSec L (U.ι ''ᵁ W)` BY RFL, because
`modDual L` is an honest presheaf and `Scheme.Modules.restrict_obj` is `rfl`;
there is no sheafification to move past. -/
noncomputable def dualRestrictIso : (modDual L).restrict U.ι ≅ modUnit (U : Scheme.{u}) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun W ↦ ModuleCat.isoMk
      (AddEquiv.toAddCommGrpIso (dualEquivAt φ (U.ι_image_le W.unop))) ?_) ?_
  · intro r
    ext ψ
    exact (dualFwd_smul_restrict φ W.unop r ψ).symm
  · intro W W' f
    ext ψ
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact dualFwd_map_restrict φ (leOfHom f.unop) ψ

/-! ##### The evaluation pairing on a trivializing open

The same bridge, run once more: on `A ≤ U` the pairing
`Γ(L,A) ⊗_{Γ(Z,A)} L^∨(A) ⟶ Γ(Z,A)` is BIJECTIVE, with explicit inverse
`r ↦ g_A ⊗ (x ↦ tr(x)·r)`.  This is the whole local input of
`isIso_modDualEv`; everything after it is the sites machinery. -/

/-- The evaluation pairing at a single open, read as an honest `Γ(Z,A)`-linear
map out of the honest tensor product.  Stating it this way is what makes `rw`
usable: the `ModuleCat`-side instances are replaced by the ones a reader would
write. -/
noncomputable def evLin (L : Z.Modules) (A : Z.Opens) :
    TensorProduct Γ(Z, A) Γ(L, A) (DualSec L A) →ₗ[Γ(Z, A)] Γ(Z, A) :=
  ModuleCat.Hom.hom ((modDualEvPre L).app (op A))

@[simp] lemma evLin_tmul (A : Z.Opens) (x : Γ(L, A)) (ψ : DualSec L A) :
    evLin L A (x ⊗ₜ[Γ(Z, A)] ψ) = ψ.φ ⟨A, le_rfl⟩ x := rfl

lemma dualBwd_zero {A : Z.Opens} (hA : A ≤ U) : dualBwd φ hA 0 = 0 := by
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  rw [dualBwd_φ, map_zero, mul_zero]
  rfl

lemma dualBwd_add {A : Z.Opens} (hA : A ≤ U) (r s : Γ(Z, A)) :
    dualBwd φ hA (r + s) = dualBwd φ hA r + dualBwd φ hA s := by
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  rw [dualBwd_φ, map_add, mul_add, DualSec.add_φ, LinearMap.add_apply, dualBwd_φ, dualBwd_φ]

lemma dualBwd_mul {A : Z.Opens} (hA : A ≤ U) (r s : Γ(Z, A)) :
    dualBwd φ hA (r * s) = r • dualBwd φ hA s := by
  refine DualSec.ext (fun V => LinearMap.ext (fun x => ?_))
  rw [dualBwd_φ, DualSec.smul_φ, LinearMap.smul_apply, dualBwd_φ, map_mul, smul_eq_mul]
  ring

/-- **THE BACKWARD MAP OF THE EVALUATION PAIRING** on a trivializing open:
`r ↦ g_A ⊗ (x ↦ tr(x)·r)`. -/
noncomputable def evBwd {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A)) :
    TensorProduct Γ(Z, A) Γ(L, A) (DualSec L A) :=
  gen φ hA ⊗ₜ[Γ(Z, A)] dualBwd φ hA r

lemma evLin_evBwd {A : Z.Opens} (hA : A ≤ U) (r : Γ(Z, A)) :
    evLin L A (evBwd φ hA r) = r := by
  rw [evBwd, evLin_tmul]
  exact dualFwd_dualBwd φ hA r

lemma evBwd_evLin {A : Z.Opens} (hA : A ≤ U)
    (t : TensorProduct Γ(Z, A) Γ(L, A) (DualSec L A)) :
    evBwd φ hA (evLin L A t) = t := by
  induction t with
  | zero => rw [map_zero, evBwd, dualBwd_zero, TensorProduct.tmul_zero]
  | tmul x ψ =>
      have hx : ψ.φ ⟨A, le_rfl⟩ x = tr φ hA x * dualFwd φ hA ψ := by
        conv_lhs => rw [eq_smul_gen φ hA x]
        rw [LinearMap.map_smul, smul_eq_mul, dualFwd]
      rw [evLin_tmul, hx, evBwd, dualBwd_mul, dualBwd_dualFwd, ← TensorProduct.smul_tmul,
        ← eq_smul_gen]
  | add a b ha hb =>
      rw [map_add, evBwd, dualBwd_add, TensorProduct.tmul_add, ← evBwd, ← evBwd, ha, hb]

/-- **THE EVALUATION PAIRING IS BIJECTIVE ON A TRIVIALIZING OPEN.**  `φ` is
explicit because the statement does not mention it. -/
lemma evLin_bijective (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    {A : Z.Opens} (hA : A ≤ U) : Function.Bijective (evLin L A) :=
  Function.bijective_iff_has_inverse.2
    ⟨evBwd φ hA, evBwd_evLin φ hA, evLin_evBwd φ hA⟩

end

/-! ##### Local bijectivity of the evaluation pairing

A sieve on `Opens Z` is covering exactly when it contains a neighbourhood of
each point (`TopologicalSpace.Opens.mem_grothendieckTopology`), so "for each `z`
a trivializing `U`, intersected with the ambient open" IS the covering
condition, and both clauses fall straight out of `evLin_bijective`. -/

section LocalBijectivity

variable {Z : Scheme.{u}} (L : Z.Modules)

/-- Naturality of the evaluation pairing, read through `evLin`. -/
lemma evLin_nat {A B : Z.Opens} (h : B ≤ A)
    (t : TensorProduct Γ(Z, A) Γ(L, A) (DualSec L A)) :
    evLin L B
        ((PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val
          (modDualPre L)).map (homOfLE h).op t) =
      Z.presheaf.map (homOfLE h).op (evLin L A t) :=
  PresheafOfModules.naturality_apply (modDualEvPre L) (homOfLE h).op t

lemma isLocallyInjective_modDualEvPre (hL : IsInvertibleSheaf L) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (modDualEvPre L)) where
  equalizerSieve_mem {X} x y h := by
    intro z hz
    obtain ⟨U, hzU, ⟨φ⟩⟩ := hL z
    refine ⟨X.unop ⊓ U, homOfLE inf_le_left, ?_, hz, hzU⟩
    have key : ∀ t s : TensorProduct Γ(Z, X.unop) Γ(L, X.unop) (DualSec L X.unop),
        evLin L X.unop t = evLin L X.unop s →
        (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val (modDualPre L)).map
            (homOfLE (inf_le_left : X.unop ⊓ U ≤ X.unop)).op t =
          (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val (modDualPre L)).map
            (homOfLE (inf_le_left : X.unop ⊓ U ≤ X.unop)).op s := by
      intro t s hts
      refine (evLin_bijective φ (inf_le_right : X.unop ⊓ U ≤ U)).injective ?_
      rw [evLin_nat, evLin_nat, hts]
    exact key x y h

lemma isLocallySurjective_modDualEvPre (hL : IsInvertibleSheaf L) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((PresheafOfModules.toPresheaf _).map (modDualEvPre L)) where
  imageSieve_mem {A} s := by
    intro z hz
    obtain ⟨U, hzU, ⟨φ⟩⟩ := hL z
    refine ⟨A ⊓ U, homOfLE inf_le_left, ?_, hz, hzU⟩
    exact ⟨evBwd φ (inf_le_right : A ⊓ U ≤ U)
        (Z.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op s),
      evLin_evBwd φ _ _⟩

end LocalBijectivity

end Bridge

end ModDual

/-- **`L^∨` IS INVERTIBLE WHEN `L` IS** (PROVEN 2026-07-30 over the rank-one
bridge `ModDual.dualRestrictIso` just above; formerly a bare sorry leaf, and the
audit below is the docstring written while it was one).

**The mathematics is one line** and needs no geometry: if `φ : L|_U ≅ 𝒪_U` then
`Γ(L, V)` is free of rank one on `g_V := φ⁻¹(1)|_V` for every `V ≤ U`, so a
compatible family `ψ ∈ L^∨(V)` is determined by the single section
`ψ_V(g_V) ∈ Γ(Z, V)`, and `ψ ↦ ψ_V(g_V)` is an isomorphism `L^∨(V) ≅ Γ(Z, V)`
commuting with restriction — i.e. `(modDual L).restrict U.ι ≅ modUnit U`.  Note
`(modDual L).restrict U.ι` has sections `DualSec L (U.ι ''ᵁ V₁)` BY RFL, because
`modDual L` is an honest presheaf and `Scheme.Modules.restrict_obj` is `rfl`;
there is no sheafification to move past.

**The COST is entirely the `restrict` boundary described in the subsection
docstring above**, and it is a real barrier rather than a nuisance: extracting
`g_V` from `φ` means reading `φ.hom.val.app (op (U.ι ⁻¹ᵁ V))` as a map of
AMBIENT sections, and `U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V` for `V ≤ U`
(`Scheme.Hom.image_preimage_eq_opensRange_inf` with
`Scheme.Opens.opensRange_ι`) has to be transported through it.  The additive
half of that transport goes through (`map_add` on `φ.hom.val.app _` is accepted
verbatim); the `Γ(Z,·)`-LINEAR half is what hits the unexposed `Iso.inv`, and
`Scheme.Modules.Hom.app_smul` is the lemma to route it through.  A worked
precedent for this exact dance, 60 lines of it, is
`Fermat.trivializedSection_trivializationOfLE` in `Modularity/AmpleSheaf.lean`;
read it before starting.

Both leaves in this pair need the SAME bridge, so build it once as a
free-standing "`L` is free of rank one on `U`, in ambient sections" statement
and prove both from it.

**THE BRIDGE IS NOW REAL CODE** — `ModDual.trAt` … `ModDual.gen_res`, in the
`### The rank-one bridge across the `restrict` boundary` section above, ending
in `ModDual.dualRestrictIso`, which IS the "`L^∨` is trivial on a trivializing
open of `L`" statement this leaf needs.  The plumbing followed mathlib's own
`Scheme.Modules.restrictUnitIso` (`(fullyFaithfulForget _).preimageIso <|
PresheafOfModules.isoMk (fun U ↦ …) …`, then `ModuleCat.isoMk` from an `Ab`-iso
plus one linearity check), with `A := U.ι ''ᵁ W` for `W : U.Opens`, so
`hA : A ≤ U` is `U.ι_image_le W`.  The forward map is
`ψ ↦ ψ.φ ⟨A, le_rfl⟩ (gen φ hA)` — additive by `DualSec.add_φ`, `Γ(Z,A)`-linear
by `ModDual.dualSec_smul_apply_self`, which was declared above for exactly this
purpose; the backward map is `r ↦ (x ↦ tr φ _ x * r|_V)`, whose compatibility
clause is `tr_nat` + `res_res` + `map_mul`. -/
theorem isInvertibleSheaf_modDual {Z : Scheme.{u}} {L : Z.Modules}
    (hL : IsInvertibleSheaf L) : IsInvertibleSheaf (modDual L) := fun z =>
  let ⟨U, hzU, ⟨φ⟩⟩ := hL z
  ⟨U, hzU, ⟨ModDual.dualRestrictIso φ⟩⟩

/-- **THE EVALUATION PAIRING IS AN ISOMORPHISM** (PROVEN 2026-07-30; cut the
same day out of `exists_modDual`, and the audit below is the docstring written
while it was a sorry leaf — the route it records is the route taken) — the
second local half.

Note this is the GLOBAL statement, deliberately stronger than the local clause
`exists_modDual` asks for; `exists_modDual`'s own docstring already records that
the two are equivalent, and the global form is what makes the local clause free
(take `U = ⊤` and let the restriction functor preserve the isomorphism).

**Route, and it avoids `isIso_of_locally_isIso` entirely.**  A morphism of
sheaves of modules is an isomorphism as soon as the underlying map of
`Ab`-presheaves is LOCALLY BIJECTIVE — mathlib's
`CategoryTheory.GrothendieckTopology.W_of_isLocallyBijective` together with
`Sheaf.isLocallyBijective_iff_isIso`, and
`SheafOfModules.toSheaf`/`PresheafOfModules.toPresheaf` both reflect
isomorphisms.  Since `modDualEv` is `sheafification.map (modDualEvPre L)`
composed with an isomorphism, and `CategoryTheory.toSheafify` is itself locally
bijective, it suffices to prove that the PRESHEAF map `ModDual.modDualEvPre L`
is locally injective and locally surjective — and both are computations on
honest sections of `L`, `L^∨` and `𝒪_Z`, with no sheafified object anywhere:

* *locally surjective*: given `r ∈ Γ(Z, W)` and `z ∈ W`, restrict to
  `V := W ⊓ U` for a trivializing `U ∋ z` and write
  `r|_V = evPre(g_V ⊗ (r|_V · g^∨))`;
* *locally injective*: on such a `V` the trivialization identifies
  `Γ(L,V) ⊗_{Γ(Z,V)} L^∨(V)` with `Γ(Z,V) ⊗ Γ(Z,V) ≅ Γ(Z,V)` and `evPre`
  with the multiplication, which is injective.

A covering sieve on `Opens Z` is checked pointwise —
`TopologicalSpace.Opens.mem_grothendieckTopology` — so "for each `z` a
trivializing neighbourhood" is literally the covering condition.

The one input both bullets need is the same rank-one bridge that
`isInvertibleSheaf_modDual` needs; see its docstring.

**WHAT THE PROOF ACTUALLY DOES, and the two places it can go wrong.**  The
route above is right, with one simplification: `modLocW Z` is ALREADY defined in
this file as "becomes an isomorphism after sheafification", and
`modLocW_whiskerLeft` above already contains the rewrite
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` that
turns it into `J.W` on underlying `Ab`-presheaves.  So the whole global half is
that rewrite plus `GrothendieckTopology.W_iff_isLocallyBijective`, and the local
half is `ModDual.isLocallyInjective_modDualEvPre` /
`ModDual.isLocallySurjective_modDualEvPre`, both one screen long over
`ModDual.evLin_bijective`.

*First trap — instance arguments do not match reducibly.*
`GrothendieckTopology.W_of_isLocallyBijective` takes its two hypotheses as
INSTANCES, and a `haveI` of them is not found: the lemmas above elaborate
`PresheafOfModules.toPresheaf _` to `Z.presheaf ⋙ forget₂ CommRingCat RingCat`
while the goal carries `Z.ringCatSheaf.obj`, which is the same thing at default
but not at reducible transparency.  Use the `_iff_` form and `exact` the two
lemmas as ordinary propositions.

*Second trap, the same disease one level up.*  `Z.Modules` is a `def` for
`SheafOfModules Z.ringCatSheaf` carrying its OWN `Category` instance, and
`modDualEv`'s two factors are typed in `Z.Modules` while the sheafification
functor's `map` is typed in `SheafOfModules _`.  So after `rw [modDualEv]`,
`infer_instance` and `exact IsIso.comp_isIso` both fail even with the first
factor's `IsIso` in context.  `IsIso.comp_isIso'` takes both as EXPLICIT
arguments, so the defeq check happens at `exact` rather than in instance
search, and it goes through. -/
theorem isIso_modDualEv {Z : Scheme.{u}} {L : Z.Modules} (hL : IsInvertibleSheaf L) :
    IsIso (modDualEv L) := by
  have key : modLocW Z = _ :=
    (PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 Z.ringCatSheaf.obj)).symm
  have hW : modLocW Z (ModDual.modDualEvPre L) := by
    rw [key]
    exact (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨ModDual.isLocallyInjective_modDualEvPre L hL,
        ModDual.isLocallySurjective_modDualEvPre L hL⟩
  rw [modDualEv]
  exact IsIso.comp_isIso' hW inferInstance

/-- **THE DUAL SHEAF AND ITS EVALUATION PAIRING** (PROVEN 2026-07-30 over
`modDual`, `modDualEv`, `isInvertibleSheaf_modDual` and `isIso_modDualEv`;
formerly a bare sorry leaf, and the docstring below is the audit written while
it was one — every word of it still applies, now to the two leaves it was
decomposed into) — an invertible `L` admits an invertible `M`
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
statement that local triviality globalises to an inverse.

**WHAT THE 2026-07-30 CONSTRUCTION SETTLED, and what it did not.**  `M` is
`modDual L` and `ev` is `modDualEv L`; the dual sheaf, its SHEAF CONDITION and
the pairing are all proven above with no hypothesis on `L` at all.  The
invertibility hypothesis enters only in the two leaves this now stands on, and
the survey and route notes above should be read as belonging to THEM. -/
theorem exists_modDual {Z : Scheme.{u}} {L : Z.Modules} (hL : IsInvertibleSheaf L) :
    ∃ (M : Z.Modules) (ev : modTensor L M ⟶ modUnit Z), IsInvertibleSheaf M ∧
      ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map ev) := by
  refine ⟨modDual L, modDualEv L, isInvertibleSheaf_modDual hL, fun _ => ⟨⊤, trivial, ?_⟩⟩
  haveI : IsIso (modDualEv L) := isIso_modDualEv hL
  infer_instance

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

/-- **CANCELLATION OF AN INVERTIBLE TENSOR FACTOR** (PROVEN 2026-07-29 over
`exists_modTensor_inv`, `nonempty_modTensor_assocPic` and the braiding): if `L`
is invertible then `L ⊗ A ≅ L ⊗ B` forces `A ≅ B`.

Tensor on the left with a left inverse `M` of `L` — obtained from the right
inverse `exists_modTensor_inv` supplies by composing with `modTensorSymmIso` —
and reassociate.  `A` and `B` are arbitrary `𝒪_Z`-modules; no invertibility of
them is used or needed.

This is the verbatim twin of `nonempty_iso_of_modTensor_left` in
`Modularity/AmpleSheaf.lean`, which is DOWNSTREAM and therefore unusable here;
the proof is that declaration's, unchanged but for the `Pic`-suffixed names.  It
is what pins the Abel–Jacobi point: `IsRelPicOf.eq_of_relPicEquiv_tensor` below
cancels `𝒪(−x)` from `𝒪(x − o) ⊗ 𝒪(−x)`. -/
theorem nonempty_iso_of_modTensorPic_left {Z : Scheme.{u}} {L A B : Z.Modules}
    (hL : IsInvertibleSheaf L) (e : modTensor L A ≅ modTensor L B) : Nonempty (A ≅ B) := by
  obtain ⟨M, -, ⟨eLM⟩⟩ := exists_modTensor_inv hL
  have eML : modTensor M L ≅ modUnit Z := modTensorSymmIso M L ≪≫ eLM
  obtain ⟨aA⟩ := nonempty_modTensor_assoc M L A
  obtain ⟨aB⟩ := nonempty_modTensor_assoc M L B
  exact ⟨(modTensorUnitLeftIso A).symm ≪≫ modTensorMapIso eML.symm (Iso.refl A) ≪≫ aA ≪≫
    modTensorMapIso (Iso.refl M) e ≪≫ aB.symm ≪≫ modTensorMapIso eML (Iso.refl B) ≪≫
    modTensorUnitLeftIso B⟩

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

/-- **The base point is natural** (PROVEN): `o_{T'} = (o_T)|_{T'}`.

Both sides are `⟨h ≫ (g ≫ o.1), _⟩` and `⟨g' ≫ o.1, _⟩` with `h ≫ g = g'`, so
this is `Subtype.ext` plus `Category.assoc` — recorded because it LOOKS like
`rfl`, is not, and `exists_abelJacobiPoint`'s `aj_pre` cannot start without
it. -/
theorem relBasePoint_pre {X S T T' : Scheme.{u}} {strX : X ⟶ S} (o : RelPoint strX (𝟙 S))
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') :
    RelPoint.pre h hg (relBasePoint o g) = relBasePoint o g' := by
  apply Subtype.ext
  show h ≫ (g ≫ o.1) = g' ≫ o.1
  rw [← hg, Category.assoc]

/-- **The base point at the identity base is the section itself** (PROVEN) —
again `Subtype.ext`, not `rfl`, and what `aj_base` needs. -/
theorem relBasePoint_id {X S : Scheme.{u}} {strX : X ⟶ S} (o : RelPoint strX (𝟙 S)) :
    relBasePoint o (𝟙 S) = o :=
  Subtype.ext (Category.id_comp o.1)

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
    (nonempty_modTensor_assoc L' (modPullback (curveBaseChangeProj strX g) N)
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
  refine (nonempty_modTensor_assoc L'' (modPullback (curveBaseChangeProj strX g) N')
    (modPullback (curveBaseChangeProj strX g) N)).some ≪≫ ?_
  exact modTensorMapIso (Iso.refl L'')
    (nonempty_modPullback_modTensorPic (curveBaseChangeProj strX g) N' N).some.symm

/-- **The relative Picard relation is an equivalence relation** — the
hypothesis both representability leaves below now receive in hand. -/
theorem relPicEquiv_equivalence : Equivalence (RelPicEquiv strX g) :=
  ⟨relPicEquiv_refl strX g, relPicEquiv_symm strX g, relPicEquiv_trans strX g⟩

end RelPicEquivIsEquivalence

/-! ### `RelPicEquiv` as a CONGRUENCE

Being an equivalence relation is not enough for the Abel–Jacobi construction:
the classes have to be manipulable.  Four PROVEN facts, added 2026-07-29 with
`exists_abelJacobiPoint` as their consumer, and none of them a leaf:

* an ISOMORPHISM is a relative-Picard equality (`relPicEquiv_of_iso`) — the
  bridge that lets a chain of coherence isomorphisms be spliced into a chain of
  `RelPicEquiv`s;
* `⊗` on the right is a CONGRUENCE (`relPicEquiv_tensor_right`) — this is where
  the middle-four interchange is spent;
* PULLBACK preserves the relation (`relPicEquiv_modPullback`) — the step
  `aj_pre` is built on, and the one that needs `isInvertibleSheaf_modPullback`,
  since the twisting sheaf `N` on `T` becomes `h^* N` on `T'`;
* an invertible factor CANCELS (`relPicEquiv_cancel_left`) — what makes `aj`
  determined by `aj_spec` rather than merely chosen.

Together these say `Pic(X_T)/Pic(T)` is a genuine abelian group, functorial in
`T`.  `Modularity/AmpleSheaf.lean` carries a twin of the last one
(`RelPicEquiv.cancel_left`); it is downstream, so the two coexist until the
hoist recorded on `modTensorSymmIso`. -/

/-- **An isomorphism is a relative-Picard equality** (PROVEN): take the twist
`N := 𝒪_T`, as in `relPicEquiv_refl`. -/
theorem relPicEquiv_of_iso {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)
    {L L' : (curveBaseChange strX g).Modules} (e : L ≅ L') : RelPicEquiv strX g L L' :=
  ⟨modUnit T, isInvertibleSheaf_modUnit T,
    ⟨e ≪≫ (modTensorUnitRightIso L').symm ≪≫
      modTensorMapIso (Iso.refl L') (modPullbackUnitIso (curveBaseChangeProj strX g)).symm⟩⟩

/-- **`RelPicEquiv` is a congruence for `⊗` on the right** (PROVEN over
`nonempty_modTensor_middleFourPic`).

`L ≅ L' ⊗ π^*N` gives `L ⊗ M ≅ (L' ⊗ π^*N) ⊗ M ≅ (L' ⊗ M) ⊗ π^*N`, which is the
middle-four interchange and nothing else.  The twisting sheaf is unchanged, so
no new invertibility obligation arises. -/
theorem relPicEquiv_tensor_right {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)
    {L L' : (curveBaseChange strX g).Modules} (M : (curveBaseChange strX g).Modules)
    (h : RelPicEquiv strX g L L') :
    RelPicEquiv strX g (modTensor L M) (modTensor L' M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨m4⟩ := nonempty_modTensor_middleFourPic L'
    (modPullback (curveBaseChangeProj strX g) N) M
  exact ⟨N, hN, ⟨modTensorMapIso e (Iso.refl M) ≪≫ m4⟩⟩

/-- **`RelPicEquiv` is a congruence for `⊗` on the LEFT** (PROVEN 2026-07-31) —
the braiding conjugate of `relPicEquiv_tensor_right`.

Needed because `RelPicEquiv` puts the twisting sheaf on the right, so the
right-hand congruence is the one that comes out of the middle-four
interchange; the left-hand one is then two applications of `modTensorSymmIso`
around it.  Its consumers are the group axioms for `IsRelPicOf.addPoint`
below — associativity moves the bracket, and only the left congruence can
rewrite inside `L ⊗ (M ⊗ N)`. -/
theorem relPicEquiv_tensor_left {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)
    {L L' : (curveBaseChange strX g).Modules} (M : (curveBaseChange strX g).Modules)
    (h : RelPicEquiv strX g L L') :
    RelPicEquiv strX g (modTensor M L) (modTensor M L') :=
  relPicEquiv_trans strX g (relPicEquiv_of_iso strX g (modTensorSymmIso M L))
    (relPicEquiv_trans strX g (relPicEquiv_tensor_right strX g M h)
      (relPicEquiv_of_iso strX g (modTensorSymmIso L' M)))

/-- **The base-change square commutes**: `φ ≫ π_g = π_{g'} ≫ h` for
`φ = curveBaseChangeMap strX h hg`.  One `pullback.lift_snd`, but it is an
equality of morphisms rather than a definitional identity, so it has to be fed
to `modPullbackCongrIso` by name. -/
theorem curveBaseChangeMap_proj {X S T T' : Scheme.{u}} (strX : X ⟶ S) {g : T ⟶ S}
    {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') :
    curveBaseChangeMap strX h hg ≫ curveBaseChangeProj strX g
      = curveBaseChangeProj strX g' ≫ h :=
  pullback.lift_snd _ _ _

/-- **`curveBaseChangeMap` IS FUNCTORIAL** (PROVEN): the base changes of the
curve along `T'' ⟶ T' ⟶ T` compose.  Both sides are maps into a pullback, so
`pullback.hom_ext` reduces this to the two projections, each a `lift` identity.

Note the direction: `curveBaseChangeMap` is CONTRAVARIANT, so the composite
`X_{T''} ⟶ X_{T'} ⟶ X_T` is written `map k ≫ map h` and equals `map (k ≫ h)`. -/
theorem curveBaseChangeMap_comp {X S T T' T'' : Scheme.{u}} (strX : X ⟶ S) {g : T ⟶ S}
    {g' : T' ⟶ S} {g'' : T'' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g')
    (k : T'' ⟶ T') (hk : k ≫ g' = g'') :
    curveBaseChangeMap strX k hk ≫ curveBaseChangeMap strX h hg
      = curveBaseChangeMap strX (k ≫ h) (by rw [Category.assoc, hg, hk]) := by
  apply pullback.hom_ext <;>
    simp [curveBaseChangeMap, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc]

/-- **`curveBaseChangeMap` depends only on the morphism, not on the proof**
(PROVEN) — `subst` plus proof irrelevance.

Needed because the factorisation hypothesis `h ≫ g = g'` is an argument: two
`curveBaseChangeMap`s built from EQUAL morphisms over DIFFERENT proofs are
propositionally but not syntactically equal, and `modPullbackCongrIso` wants
the equality by name. -/
theorem curveBaseChangeMap_congr {X S T T' : Scheme.{u}} (strX : X ⟶ S) {g : T ⟶ S}
    {g' : T' ⟶ S} {h h' : T' ⟶ T} (e : h = h') (hg : h ≫ g = g') (hg' : h' ≫ g = g') :
    curveBaseChangeMap strX h hg = curveBaseChangeMap strX h' hg' := by
  subst e; rfl

/-- **`k^*(h^* L) ≅ (k ≫ h)^* L` at the level of base-changed curves** (PROVEN)
— `modPullbackCompIso` transported along `curveBaseChangeMap_comp`.

This is the workhorse of `surj_of_isRelPicOverAffines` below: the compatibility
of two local classifying points on an overlap is stated over the overlap's own
structure morphism, and getting there from each point's own open requires
exactly this identification. -/
noncomputable def modPullbackCurveBaseChangeCompIso {X S T T' T'' : Scheme.{u}} (strX : X ⟶ S)
    {g : T ⟶ S} {g' : T' ⟶ S} {g'' : T'' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g')
    (k : T'' ⟶ T') (hk : k ≫ g' = g'') (L : (curveBaseChange strX g).Modules) :
    modPullback (curveBaseChangeMap strX k hk) (modPullback (curveBaseChangeMap strX h hg) L)
      ≅ modPullback (curveBaseChangeMap strX (k ≫ h)
          (by rw [Category.assoc, hg, hk])) L :=
  modPullbackCompIso _ _ L ≪≫ modPullbackCongrIso (curveBaseChangeMap_comp strX h hg k hk) L

/-- **PULLBACK PRESERVES `RelPicEquiv`** (PROVEN over
`nonempty_modPullback_modTensorPic` and `isInvertibleSheaf_modPullback`).

`L ≅ L' ⊗ π_g^* N` pulls back to
`φ^*L ≅ φ^*L' ⊗ φ^*π_g^*N = φ^*L' ⊗ (φ ≫ π_g)^*N = φ^*L' ⊗ (π_{g'} ≫ h)^*N
     ≅ φ^*L' ⊗ π_{g'}^*(h^*N)`,
so the new twist is `h^* N` — and it is invertible **only because pullback
preserves invertibility**.  That is the precise sense in which
`isInvertibleSheaf_modPullback` was the blocking piece of `aj_pre`: without it
the witness for the new twist has no `IsInvertibleSheaf` field. -/
theorem relPicEquiv_modPullback {X S T T' : Scheme.{u}} (strX : X ⟶ S) {g : T ⟶ S}
    {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g')
    {L L' : (curveBaseChange strX g).Modules} (hLL' : RelPicEquiv strX g L L') :
    RelPicEquiv strX g' (modPullback (curveBaseChangeMap strX h hg) L)
      (modPullback (curveBaseChangeMap strX h hg) L') := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hLL'
  refine ⟨modPullback h N, isInvertibleSheaf_modPullback h hN, ⟨?_⟩⟩
  refine modPullbackMapIso _ e ≪≫
    (nonempty_modPullback_modTensorPic (curveBaseChangeMap strX h hg) L'
      (modPullback (curveBaseChangeProj strX g) N)).some ≪≫
    modTensorMapIso (Iso.refl _) ?_
  refine modPullbackCompIso (curveBaseChangeMap strX h hg) (curveBaseChangeProj strX g) N ≪≫ ?_
  refine modPullbackCongrIso (curveBaseChangeMap_proj strX h hg) N ≪≫ ?_
  exact (modPullbackCompIso (curveBaseChangeProj strX g') h N).symm

/-- **CANCELLATION IN THE RELATIVE PICARD GROUP** (PROVEN over
`nonempty_iso_of_modTensorPic_left`): an invertible factor common to both sides
may be deleted.  Only the cancelled factor `L` has to be invertible; `A` and `B`
are arbitrary. -/
theorem relPicEquiv_cancel_left {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)
    {L A B : (curveBaseChange strX g).Modules} (hL : IsInvertibleSheaf L)
    (h : RelPicEquiv strX g (modTensor L A) (modTensor L B)) : RelPicEquiv strX g A B := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨a⟩ := nonempty_modTensor_assoc L B (modPullback (curveBaseChangeProj strX g) N)
  obtain ⟨f⟩ := nonempty_iso_of_modTensorPic_left hL (e ≪≫ a)
  exact ⟨N, hN, ⟨f⟩⟩

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

/-! ### TWO REPRESENTING OBJECTS ARE CANONICALLY ISOMORPHIC OVER `S`

Everything in this subsection is PROVEN, and it is what converts a
statement about EVERY representing object into a statement about SOME
representing object.  That conversion is the whole reason the subsection
exists: the classical literature never proves "any scheme representing
`Pic_{X/S}` is smooth/separated" — it CONSTRUCTS one and reads the
properties off the construction (BLR 8.2/1 builds `Pic` as a separated
`S`-scheme locally of finite type; 8.4/2 adds smoothness).  Without a
uniqueness statement those two shapes are different theorems, and a leaf
stated in the "every" shape cannot consume the literature at all.

The argument is pure Yoneda, carried out on `RelPoint` rather than
through a functor object (there is no functor object here — see the
universe note on `exists_relPicFull`):

* `cmp` sends a `T`-point of `P` to the unique `T`-point of `Q` carrying
  the same class, by `surj` for existence and `inj` for uniqueness;
* `cmp_cmp` is the round trip, by `inj` again;
* `cmp_pre` is naturality in the test object, and is the only step with
  any content: it chains `sheaf_pre` on both sides with the transport
  lemma `relPicEquiv_modPullback`;
* `toHom` evaluates `cmp` at the TAUTOLOGICAL point `𝟙 P`, and
  `toHom_comp_toHom` is `cmp_pre` at `h = toHom` composed with `cmp_cmp`.

Note what is NOT claimed: the isomorphism is not shown to be the unique
one over `S` (it is, by `inj` at `T = P`, but nothing below needs it), and
no compatibility with `zeroPoint`/`addPoint` is proven. -/

namespace IsRelPicOf

section Comparison

variable {X P Q S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S} {qstr : Q ⟶ S}

/-- **The comparison of two representing objects, on points** (PROVEN):
the `T`-point of `Q` carrying the same class as a given `T`-point of `P`.
Obtained by choice from `surj`; it is the CORRECT choice rather than an
arbitrary one because `inj` makes it unique. -/
noncomputable def cmp (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) : RelPoint qstr g :=
  (hQ.surj (hP.sheaf p) (hP.invertible p)).choose

/-- `cmp` preserves the classified class (PROVEN). -/
theorem sheaf_cmp (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    RelPicEquiv strX g (hQ.sheaf (hP.cmp hQ p)) (hP.sheaf p) :=
  (hQ.surj (hP.sheaf p) (hP.invertible p)).choose_spec

/-- `cmp` is an involution up to the two structures (PROVEN), by `inj`. -/
theorem cmp_cmp (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    hQ.cmp hP (hP.cmp hQ p) = p :=
  hP.inj _ _ (relPicEquiv_trans _ _ (hQ.sheaf_cmp hP (hP.cmp hQ p)) (hP.sheaf_cmp hQ p))

/-- `cmp` is NATURAL in the test object (PROVEN) — the only step of the
comparison with content, and where `relPicEquiv_modPullback` is spent. -/
theorem cmp_pre (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S} (hg : h ≫ g = g')
    (p : RelPoint pstr g) :
    hP.cmp hQ (RelPoint.pre h hg p) = RelPoint.pre h hg (hP.cmp hQ p) := by
  refine hQ.inj _ _ ?_
  have h1 : RelPicEquiv strX g' (hQ.sheaf (hP.cmp hQ (RelPoint.pre h hg p)))
      (modPullback (curveBaseChangeMap strX h hg) (hP.sheaf p)) :=
    relPicEquiv_trans _ _ (hP.sheaf_cmp hQ (RelPoint.pre h hg p)) (hP.sheaf_pre h hg p)
  have h2 : RelPicEquiv strX g' (hQ.sheaf (RelPoint.pre h hg (hP.cmp hQ p)))
      (modPullback (curveBaseChangeMap strX h hg) (hP.sheaf p)) :=
    relPicEquiv_trans _ _ (hQ.sheaf_pre h hg (hP.cmp hQ p))
      (relPicEquiv_modPullback strX h hg (hP.sheaf_cmp hQ p))
  exact relPicEquiv_trans _ _ h1 (relPicEquiv_symm _ _ h2)

/-- **The tautological point** `𝟙 P : RelPoint pstr pstr`, at which `cmp`
is evaluated to produce a morphism of schemes. -/
def selfPoint (pstr : P ⟶ S) : RelPoint pstr pstr := ⟨𝟙 P, Category.id_comp pstr⟩

/-- **The comparison morphism `P ⟶ Q` over `S`** (PROVEN). -/
noncomputable def toHom (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) : P ⟶ Q :=
  (hP.cmp hQ (selfPoint pstr)).1

/-- The comparison morphism is a morphism OVER `S` (PROVEN). -/
theorem toHom_comp (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) :
    hP.toHom hQ ≫ qstr = pstr := (hP.cmp hQ (selfPoint pstr)).2

/-- The two comparison morphisms are mutually inverse (PROVEN) — `cmp_pre`
at `h = toHom`, composed with `cmp_cmp`. -/
theorem toHom_comp_toHom (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) :
    hQ.toHom hP ≫ hP.toHom hQ = 𝟙 Q := by
  have key := hP.cmp_pre hQ (hQ.toHom hP) (hQ.toHom_comp hP) (selfPoint pstr)
  have hpre : RelPoint.pre (hQ.toHom hP) (hQ.toHom_comp hP) (selfPoint pstr)
      = hQ.cmp hP (selfPoint qstr) :=
    Subtype.ext (Category.comp_id _)
  rw [hpre, hQ.cmp_cmp hP (selfPoint qstr)] at key
  exact (congrArg Subtype.val key).symm

/-- **TWO SCHEMES REPRESENTING `Pic_{X/S}` ARE ISOMORPHIC OVER `S`**
(PROVEN).  The `S`-structure is `toHom_comp`. -/
noncomputable def isoOver (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) : P ≅ Q where
  hom := hP.toHom hQ
  inv := hQ.toHom hP
  hom_inv_id := hQ.toHom_comp_toHom hP
  inv_hom_id := hP.toHom_comp_toHom hQ

instance isIso_toHom (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) :
    IsIso (hP.toHom hQ) :=
  (hP.isoOver hQ).isIso_hom

end Comparison

end IsRelPicOf

/-- **EVERY ISOMORPHISM-INVARIANT PROPERTY OF THE STRUCTURE MORPHISM
TRANSPORTS BETWEEN REPRESENTING OBJECTS** (PROVEN): `pstr = toHom ≫ qstr`
with `toHom` an isomorphism, so `MorphismProperty.cancel_left_of_respectsIso`
finishes.

Stated at this generality on purpose.  `Smooth` and `IsSeparated` are only
the two that were needed first; `LocallyOfFiniteType`, `QuasiSeparated`,
`Flat`, `IsProper` and anything else in `MorphismProperty Scheme` with a
`RespectsIso` instance comes for free from the same line, and that is what
converts a "SOME representing object" existence statement — which is the only
shape the literature proves — into the "EVERY representing object" statement a
consumer wants. -/
theorem transport_of_isRelPicOf {X P Q S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    {qstr : Q ⟶ S} {W : MorphismProperty Scheme.{u}} [W.RespectsIso]
    (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr) (h : W qstr) : W pstr := by
  rw [← hP.toHom_comp hQ]
  exact (MorphismProperty.cancel_left_of_respectsIso W (hP.toHom hQ) qstr).mpr h

/-- **SMOOTHNESS TRANSPORTS BETWEEN REPRESENTING OBJECTS** (PROVEN) — the
`W = @Smooth` instance of `transport_of_isRelPicOf`. -/
theorem smooth_of_isRelPicOf_of_smooth {X P Q S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    {qstr : Q ⟶ S} (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    (h : Smooth qstr) : Smooth pstr :=
  transport_of_isRelPicOf (W := @Smooth) hP hQ h

/-- **SEPARATEDNESS TRANSPORTS BETWEEN REPRESENTING OBJECTS** (PROVEN) — the
`W = @IsSeparated` instance of `transport_of_isRelPicOf`. -/
theorem isSeparated_of_isRelPicOf_of_isSeparated {X P Q S : Scheme.{u}} {strX : X ⟶ S}
    {pstr : P ⟶ S} {qstr : Q ⟶ S} (hP : IsRelPicOf strX pstr) (hQ : IsRelPicOf strX qstr)
    (h : IsSeparated qstr) : IsSeparated pstr :=
  transport_of_isRelPicOf (W := @IsSeparated) hP hQ h

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

/-! #### Step (i) of FGA 232: the hypotheses base-change

All five are PROVEN, and they are what lets the leaf below be stated over
an ARBITRARY affine base rather than over an affine open of `S`.  Each is
one application of the corresponding mathlib stability instance to
`curveBaseChangeProj strX g = pullback.snd strX g`; the section is the
only one with any content, and even that content is `pullback.lift_snd`.

The docstring on `exists_relPicOf_isAffineOpen` used to say this transport
"belongs to whoever proves this, not to the assembly".  That was a pricing
decision, and it was wrong in the direction that matters: it left a leaf
whose statement did not match its citation, which is the exact defect
CLAUDE.md records under "A LEAF STATED FOR *EVERY* REPRESENTING OBJECT
CANNOT CONSUME ITS OWN CITATION".  BLR 8.2/1 is a theorem about a relative
curve over an affine base; it is not a theorem about a base change of a
relative curve over an open of some other scheme.  Discharging step (i)
here costs 20 lines and puts the leaf in the citation's own shape. -/

section BaseChangeOfHypotheses

variable {X S T : Scheme.{u}} (strX : X ⟶ S) (g : T ⟶ S)

/-- **Properness base-changes** (PROVEN) — step (i) of FGA 232. -/
theorem isProper_curveBaseChangeProj (h : IsProper strX) :
    IsProper (curveBaseChangeProj strX g) :=
  MorphismProperty.pullback_snd (P := @IsProper) strX g h

/-- **Smoothness of relative dimension `1` base-changes** (PROVEN).  The
mathlib stability fact is a `lemma`, not an `instance`, so it has to be
introduced by hand before `pullback_snd` can see it. -/
theorem smoothOfRelativeDimension_curveBaseChangeProj (h : SmoothOfRelativeDimension 1 strX) :
    SmoothOfRelativeDimension 1 (curveBaseChangeProj strX g) :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) strX g h

/-- **Geometric connectedness base-changes** (PROVEN). -/
theorem geometricallyConnected_curveBaseChangeProj (h : GeometricallyConnected strX) :
    GeometricallyConnected (curveBaseChangeProj strX g) :=
  MorphismProperty.pullback_snd (P := @GeometricallyConnected) strX g h

/-- **`f_*𝒪 = 𝒪` universally base-changes** (PROVEN) — and this one is
free by construction rather than by a stability theorem:
`HasUniversallyTrivialPushforward` is literally
`hasTrivialPushforwardProperty.universally`, and `.universally` of any
property is stable under base change. -/
theorem hasUniversallyTrivialPushforward_curveBaseChangeProj
    (h : AlgebraicGeometry.HasUniversallyTrivialPushforward strX) :
    AlgebraicGeometry.HasUniversallyTrivialPushforward (curveBaseChangeProj strX g) :=
  MorphismProperty.pullback_snd
    (P := AlgebraicGeometry.hasTrivialPushforwardProperty.universally) strX g h

/-- **The section base-changes** (PROVEN): `o : RelPoint strX (𝟙 S)` gives
a section of `X ×_S T ⟶ T`, namely `relSection` of the constant section
`o_T = relBasePoint o g`.  That `relSection x ≫ pullback.snd = 𝟙 T` is
`pullback.lift_snd`, which is also the whole proof. -/
noncomputable def relBasePointBaseChange (o : RelPoint strX (𝟙 S)) :
    RelPoint (curveBaseChangeProj strX g) (𝟙 T) :=
  ⟨relSection (relBasePoint o g), by
    simp only [relSection, curveBaseChangeProj, pullback.lift_snd]⟩

end BaseChangeOfHypotheses

/-- **THE RELATIVE PICARD SCHEME OF A RELATIVE CURVE OVER AN AFFINE BASE**
— FGA exposé 232 / BLR 8.2/1 (sorry leaf, cut 2026-07-31 out of
`exists_relPicOf_isAffineOpen` by discharging that leaf's step (i)).

This is where all of the geometry of the chain lives, and it is now stated
about the curve the citation is about: an arbitrary proper smooth
geometrically connected relative curve with a section over an AFFINE base.
No base change appears in the statement.

A prover owes, in order: (ii) `strY` is projective over `V`, by the finite
constant-genus decomposition and `𝒪((2g+1)·o)` (see the section note
above); (iii) FGA 232 for a projective flat morphism with integral
geometric fibres — the geometric fibres here are smooth connected curves
over an algebraically closed field, hence integral; (iv) BLR 8.1/4 to
identify the fppf sheaf with the naive quotient, which is what makes
`surj` statable without sheafification.

Step (i) — that the hypotheses survive base change — used to be part of
this obligation and is now PROVEN just above.

**THERE IS NO PROJECTIVITY API AT THIS PIN, so step (ii) cannot be cut out
as a leaf of its own.**  Re-checked 2026-07-31: `Mathlib/AlgebraicGeometry/`
contains no `IsProjective`, no relative ampleness and no very-ample sheaf
for MORPHISMS (the project's own `Fermat/FLT/Modularity/AmpleSheaf.lean`
has `IsAmpleSheaf` for a sheaf on a single scheme, which is not the same
predicate and does not carry a projective embedding).  So the reduction
(ii) has nothing to reduce TO, and whoever takes this leaf must either
state relative projectivity first or prove (iii) directly for a curve over
an affine base.  That is the honest reason this is the file's one
research-scale node, and it is worth knowing before starting rather than
after.

**FAITHFULNESS AUDIT (fresh — this is a NEW statement, so nothing is
inherited).**  TRUE: it is BLR 8.2/1 + 8.4/2 verbatim, which construct
`Pic_{Y/V}` as a smooth separated `V`-scheme locally of finite type for a
projective flat family of integral curves, and over an affine `V` the
hypotheses give exactly such a family.

*Every hypothesis is load-bearing.*  Drop `IsAffine V` and (ii) fails —
over a general base the constant-genus decomposition can be infinite and
there is no single relatively very ample sheaf, which is precisely why FGA
is stated for projective morphisms.  Drop `_hsmooth` and smoothness of
`Pic` fails at relative dimension `2` (`H²(Y_s, 𝒪)` need not vanish; a K3
over a non-reduced base is the standard witness).  Drop `_hpush` and
separatedness fails, already for `Y = V ⊔ V`, where
`0 ⟶ Pic T ⟶ Pic Y_T ⟶ P(T)` breaks.  Drop `_o` and BLR 8.1/4 is
unavailable, so `surj` would need the fppf sheafification that this
development cannot state.

*NOT VACUOUS*: `Y = ℙ¹_V` satisfies every hypothesis, and
`Pic_{ℙ¹_V/V} = ℤ × V ⟶ V` is étale (hence smooth) and separated.

*The strengthened conclusion admits no junk witness*: `P = V`,
`pstr = 𝟙 V` IS smooth and separated but fails `surj` at any curve of
positive genus, by the `𝒪(Δ) ⊗ 𝒪(−o)` computation in the `IsRelPicOf`
docstring. -/
theorem exists_relPicOf_of_isAffineBase {Y V : Scheme.{u}} (strY : Y ⟶ V) [IsAffine V]
    (_hproper : IsProper strY) (_hsmooth : SmoothOfRelativeDimension 1 strY)
    (_hconn : GeometricallyConnected strY) (_o : RelPoint strY (𝟙 V))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strY) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ V),
      Nonempty (IsRelPicOf strY pstr) ∧ Smooth pstr ∧ IsSeparated pstr :=
  sorry

namespace IsRelPicOf

variable {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S} (hP : IsRelPicOf strX pstr)

/-- **`Pic` is COMMUTATIVE** (PROVEN 2026-07-31) — the braiding, through
`inj`. -/
theorem addPoint_comm {T : Scheme.{u}} {g : T ⟶ S} (p q : RelPoint pstr g) :
    hP.addPoint p q = hP.addPoint q p :=
  hP.inj _ _ <| relPicEquiv_trans strX g (hP.sheaf_addPoint p q) <|
    relPicEquiv_trans strX g (relPicEquiv_of_iso strX g (modTensorSymmIso _ _))
      (relPicEquiv_symm strX g (hP.sheaf_addPoint q p))

/-- **`Pic` is ASSOCIATIVE** (PROVEN 2026-07-31) — the associator
`nonempty_modTensor_assoc`, with `relPicEquiv_tensor_right` used to rewrite the
left factor and `relPicEquiv_tensor_left` the right one. -/
theorem addPoint_assoc {T : Scheme.{u}} {g : T ⟶ S} (p q r : RelPoint pstr g) :
    hP.addPoint (hP.addPoint p q) r = hP.addPoint p (hP.addPoint q r) := by
  refine hP.inj _ _ ?_
  refine relPicEquiv_trans strX g (hP.sheaf_addPoint (hP.addPoint p q) r) ?_
  refine relPicEquiv_trans strX g
    (relPicEquiv_tensor_right strX g _ (hP.sheaf_addPoint p q)) ?_
  refine relPicEquiv_trans strX g
    (relPicEquiv_of_iso strX g (nonempty_modTensor_assoc _ _ _).some) ?_
  refine relPicEquiv_trans strX g
    (relPicEquiv_tensor_left strX g _ (relPicEquiv_symm strX g (hP.sheaf_addPoint q r))) ?_
  exact relPicEquiv_symm strX g (hP.sheaf_addPoint p (hP.addPoint q r))

/-- **`zeroPoint` IS a left unit** (PROVEN 2026-07-31) — the LEFT unitor
`modTensorUnitLeftIso`, which is the one mathlib's sheafified tensor already
had. -/
theorem zeroPoint_addPoint {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    hP.addPoint (hP.zeroPoint g) p = p := by
  refine hP.inj _ _ ?_
  refine relPicEquiv_trans strX g (hP.sheaf_addPoint (hP.zeroPoint g) p) ?_
  refine relPicEquiv_trans strX g
    (relPicEquiv_tensor_right strX g _ (hP.sheaf_zeroPoint g)) ?_
  exact relPicEquiv_of_iso strX g (modTensorUnitLeftIso _)

/-- **EVERY POINT OF `Pic` HAS AN INVERSE** (PROVEN 2026-07-31) — the inverse
sheaf `exists_modTensor_inv` is invertible, hence classified by `surj`.

Stated as an existential over the *defining property* rather than over a chosen
point, so that `negPoint` below is the `choose` of a spec that is already the
useful one. -/
theorem exists_negPoint {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    ∃ q : RelPoint pstr g,
      RelPicEquiv strX g (modTensor (hP.sheaf p) (hP.sheaf q)) (modUnit _) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_modTensor_inv (hP.invertible p)
  obtain ⟨q, hq⟩ := hP.surj M hM
  exact ⟨q, relPicEquiv_trans strX g (relPicEquiv_tensor_left strX g _ hq)
    (relPicEquiv_of_iso strX g e)⟩

/-- **Negation on the points of `Pic`** — the point classifying the inverse
sheaf.  Determined by its spec, since `inj` makes it unique. -/
noncomputable def negPoint {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    RelPoint pstr g := (hP.exists_negPoint p).choose

/-- `p + (−p) = 0` (PROVEN 2026-07-31). -/
theorem addPoint_negPoint {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    hP.addPoint p (hP.negPoint p) = hP.zeroPoint g := by
  refine hP.inj _ _ ?_
  refine relPicEquiv_trans strX g (hP.sheaf_addPoint p (hP.negPoint p)) ?_
  refine relPicEquiv_trans strX g (hP.exists_negPoint p).choose_spec ?_
  exact relPicEquiv_symm strX g (hP.sheaf_zeroPoint g)

/-- `(−p) + p = 0` (PROVEN 2026-07-31) — the form `AbelianSchemeStruct.neg_add`
asks for. -/
theorem negPoint_addPoint {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g) :
    hP.addPoint (hP.negPoint p) p = hP.zeroPoint g := by
  rw [hP.addPoint_comm]; exact hP.addPoint_negPoint p

/-- **The origin is NATURAL** (PROVEN 2026-07-31) — `sheaf_pre` followed by
`modPullbackUnitIso`: `φ^*𝒪 ≅ 𝒪`. -/
theorem pre_zeroPoint {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') : RelPoint.pre h hg (hP.zeroPoint g) = hP.zeroPoint g' := by
  refine hP.inj _ _ ?_
  refine relPicEquiv_trans strX g' (hP.sheaf_pre h hg (hP.zeroPoint g)) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_modPullback strX h hg (hP.sheaf_zeroPoint g)) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_of_iso strX g' (modPullbackUnitIso (curveBaseChangeMap strX h hg))) ?_
  exact relPicEquiv_symm strX g' (hP.sheaf_zeroPoint g')

/-- **Addition is NATURAL** (PROVEN 2026-07-31) — `sheaf_pre` followed by
`nonempty_modPullback_modTensorPic`, i.e. `φ^*(L ⊗ M) ≅ φ^*L ⊗ φ^*M`.

This is the one place in the group-law section that consumes an open leaf, and
it is `nonempty_modPullback_modTensorPic` (the pullback/tensor interchange),
not a new obligation. -/
theorem pre_addPoint {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (p q : RelPoint pstr g) :
    RelPoint.pre h hg (hP.addPoint p q)
      = hP.addPoint (RelPoint.pre h hg p) (RelPoint.pre h hg q) := by
  refine hP.inj _ _ ?_
  refine relPicEquiv_trans strX g' (hP.sheaf_pre h hg (hP.addPoint p q)) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_modPullback strX h hg (hP.sheaf_addPoint p q)) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_of_iso strX g'
      (nonempty_modPullback_modTensorPic (curveBaseChangeMap strX h hg)
        (hP.sheaf p) (hP.sheaf q)).some) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_tensor_right strX g' _
      (relPicEquiv_symm strX g' (hP.sheaf_pre h hg p))) ?_
  refine relPicEquiv_trans strX g'
    (relPicEquiv_tensor_left strX g' _
      (relPicEquiv_symm strX g' (hP.sheaf_pre h hg q))) ?_
  exact relPicEquiv_symm strX g'
    (hP.sheaf_addPoint (RelPoint.pre h hg p) (RelPoint.pre h hg q))

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
      Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) ∧
        Smooth pstr ∧ IsSeparated pstr :=
  haveI : IsAffine (V : Scheme.{u}) := _hV
  exists_relPicOf_of_isAffineBase (curveBaseChangeProj strX V.ι)
    (isProper_curveBaseChangeProj strX V.ι _hproper)
    (smoothOfRelativeDimension_curveBaseChangeProj strX V.ι _hsmooth)
    (geometricallyConnected_curveBaseChangeProj strX V.ι _hconn)
    (relBasePointBaseChange strX V.ι _o)
    (hasUniversallyTrivialPushforward_curveBaseChangeProj strX V.ι _hpush)

/-! ### The Zariski-local half, cut again

`exists_relPicOf_of_forall_isAffineOpen` below is PROVEN, over the three
leaves in this subsection.  The cut is forced by a gap in the note above,
which is corrected here.

**The gap.**  The docstring that used to sit on
`exists_relPicOf_of_forall_isAffineOpen` said the proof was
"`AlgebraicGeometry.Scheme.GlueData` for the construction, and then four
field-by-field checks on `IsRelPicOf`, of which `inj` and `sheaf_pre` are
local by inspection".  **`sheaf_pre` is NOT local by inspection, because
`sheaf` itself cannot be obtained by gluing the local `sheaf` functions.**
`IsRelPicOf` is a `Nonempty` existence statement, so `_hloc` hands out one
UNRELATED structure per affine open, and two structures on the same
`pstr` need not agree: if `hV : IsRelPicOf strX' pstr'` then so is `hV`
with `sheaf` replaced by `fun p => modDual (sheaf p)` — `inj` survives
because dualising is an involution on classes, `surj` because it is a
bijection, `sheaf_pre` because pullback commutes with duals.  So the local
`sheaf`s can differ by an automorphism of the functor `Pic(X_-)/Pic(-)`
and there is nothing to glue along.  (This is the same observation the
SECTION note above already makes for the Poincaré bundle — "local
representatives agree only up to a twist" — carried one level up, from
representatives of a class to the classifying function itself.  The
section note was right; the theorem docstring was the loose one.)

**What the correct cut is.**  `sheaf` has to be produced GLOBALLY, at the
same time as `P`, and the classical way to do that is the rigidified
Poincaré bundle: `_o` normalises the universal sheaf on `X ×_S P` along
the section, `_hpush` (`f_*𝒪 = 𝒪` universally) makes a rigidified sheaf
have no automorphisms, so the local universal sheaves glue canonically and
`sheaf p` is the pullback of the glued one along `p`.  That is exactly the
content of `IsRelPicOverAffines`: it carries a GLOBAL `sheaf`, global
`invertible` and global `sheaf_pre`, and asks for `inj`/`surj` only at
test objects lying over an affine open of `S`.

The three leaves are then:

* `exists_isRelPicOverAffines_of_forall_isAffineOpen` — the geometry:
  glue the `P_V` (Stacks 01JJ, or mathlib's
  `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, Stacks 01LH) and
  the rigidified universal sheaves.  **PROVEN 2026-07-31**, over a cut of
  its own into `exists_gluedRelPic_of_forall_isAffineOpen` (the scheme,
  and it needs NO geometric hypothesis) and
  `nonempty_isRelPicOverAffines_of_restrict` (the sheaf, where `_o` and
  `_hpush` are spent); its `Smooth ∧ IsSeparated` clause is discharged in
  the assembly by `transport_of_forall_isAffineOpen`;
* `inj_of_isRelPicOverAffines` — injectivity is Zariski-local on `T`.
  **PROVEN 2026-07-30, and the route below is what went through verbatim.**
  **Unconditional**: it needs neither `_o` nor `_hpush` nor any geometric
  hypothesis, and that is now a compiler-checked claim, not an omission.
  Given
  `RelPicEquiv strX g (sheaf p) (sheaf q)`, restrict along the open cover
  `g ⁻¹ᵁ V` of `T` by preimages of affine opens of `S`; `sheaf_pre` plus
  stability of `RelPicEquiv` under `modPullback` transports the relation,
  the affine-local `inj` gives `p|ᵢ = q|ᵢ`, and an open cover is jointly
  epimorphic, so `p = q`.  Nothing in that consumes a hypothesis;
* `surj_of_isRelPicOverAffines` — BLR 8.1/4, and the ONLY place `_o` and
  `_hpush` are consumed.  Local classifying points `pᵢ` glue by the
  previous leaf applied over the overlaps, but concluding
  `RelPicEquiv strX g (sheaf p) L` from its restrictions is precisely the
  Zariski-sheaf property of `T ↦ Pic(X_T)/Pic(T)`: separatedness needs
  `f_*𝒪 = 𝒪`, and the local twists `Nᵢ` glue into a global `N` only
  because the section kills the resulting class in `Br T`.  Drop either
  and this leaf is FALSE (for `X = S ⊔ S` the sequence
  `0 ⟶ Pic T ⟶ Pic X_T ⟶ P(T) ⟶ Br T` breaks) — see the section note.

**Not a relocation with extra steps.**  `IsRelPicOverAffines` is strictly
weaker than `IsRelPicOf`: every `IsRelPicOf strX pstr` gives one, by
ignoring the factorisation hypotheses, and the converse is exactly the two
descent leaves.  It is not vacuous either — the junk witness `P = S`,
`pstr = 𝟙 S` with the trivial `sheaf` fails `surj` already at
`T = X ×_S V`, `g` the projection to `V ⊆ S` affine, for any curve of
positive genus, by the same `𝒪(Δ) ⊗ 𝒪(−o)` computation the `IsRelPicOf`
docstring records. -/

/-- **`g : T ⟶ S` factors through an affine open of `S`.**

The locality hypothesis of `IsRelPicOverAffines`.  It is the honest form
of "`T` lies over an affine open": the affine opens of `S` cover `S`, so
every `g` is covered by such factoring restrictions, which is what makes
the two descent leaves below statable.

Stated as a factorisation rather than as `Set.range g.base ⊆ V` because
the fields it guards need the map `T ⟶ V` itself — they instantiate the
local structure `IsRelPicOf (curveBaseChangeProj strX V.ι) pstr_V` at the
`V`-scheme `(T, gV)`. -/
def FactorsThroughAffineOpen {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ V : S.Opens, IsAffineOpen V ∧ ∃ gV : T ⟶ (V : Scheme.{u}), gV ≫ V.ι = g

/-- **`pstr` represents `Pic_{X/S}` over the affine opens of `S`, with a
GLOBAL classifying sheaf.**

`IsRelPicOf` with `inj` and `surj` weakened to test objects lying over an
affine open of `S`, and `sheaf`, `invertible`, `sheaf_pre` left global.
See the section note above for why the global fields cannot be weakened
in the same way (the local `sheaf`s are only well defined up to an
automorphism of the functor, so there is nothing to glue), and hence why
this — and not "an `IsRelPicOf` over each affine open" — is the correct
intermediate object. -/
structure IsRelPicOverAffines {X P S : Scheme.{u}} (strX : X ⟶ S) (pstr : P ⟶ S) where
  /-- the invertible sheaf on `X_T` classified by a `T`-point of `P`, for EVERY `T` -/
  sheaf : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint pstr g → (curveBaseChange strX g).Modules
  /-- the classified sheaves are invertible -/
  invertible : ∀ {T : Scheme.{u}} {g : T ⟶ S} (p : RelPoint pstr g), IsInvertibleSheaf (sheaf p)
  /-- the classification is natural in the test object -/
  sheaf_pre : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (p : RelPoint pstr g),
    RelPicEquiv strX g' (sheaf (RelPoint.pre h hg p))
      (modPullback (curveBaseChangeMap strX h hg) (sheaf p))
  /-- `P ↪ Pic_{X/S}`, over an affine open of the base only -/
  inj : ∀ {T : Scheme.{u}} {g : T ⟶ S}, FactorsThroughAffineOpen g →
    ∀ p q : RelPoint pstr g, RelPicEquiv strX g (sheaf p) (sheaf q) → p = q
  /-- `P ↠ Pic_{X/S}`, over an affine open of the base only -/
  surj : ∀ {T : Scheme.{u}} {g : T ⟶ S}, FactorsThroughAffineOpen g →
    ∀ L : (curveBaseChange strX g).Modules, IsInvertibleSheaf L →
      ∃ p : RelPoint pstr g, RelPicEquiv strX g (sheaf p) L

/-! #### A property that is Zariski-local at the target transports from the
local Picard schemes to the glued one

Both lemmas are PROVEN, and together they are step 4 of the gluing route
below — the step that discharges the `Smooth ∧ IsSeparated` clause the
2026-07-31 restatement added to that leaf's conclusion.  Nothing about
`Pic` is used: the first is `IsZariskiLocalAtTarget.of_iSup_eq_top` over
`iSup_affineOpens_eq_top`, and the second feeds it
`transport_of_isRelPicOf`, which is where representability enters and is
the only mathematical input. -/

/-- **A Zariski-local-at-target property may be checked over the affine
opens of the base** (PROVEN). -/
theorem of_forall_isAffineOpen_morphismRestrict {P S : Scheme.{u}} (pstr : P ⟶ S)
    (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget W]
    (h : ∀ V : S.Opens, IsAffineOpen V → W (pstr ∣_ V)) : W pstr :=
  IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : S.affineOpens => (i : S.Opens)) (iSup_affineOpens_eq_top S) fun i => h _ i.2

/-- **A Zariski-local-at-target property passes from the LOCAL Picard
schemes to a GLOBAL scheme that restricts to them** (PROVEN).

`hres` says `pstr ∣_ V` represents `Pic` over each affine `V`; `hloc` says
SOME representing object over `V` has the property.  `transport_of_isRelPicOf`
moves the property across the canonical isomorphism of the two, and
`of_forall_isAffineOpen_morphismRestrict` globalises it.  Instantiated at
`W = @Smooth` and `W = @IsSeparated` below. -/
theorem transport_of_forall_isAffineOpen {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget W]
    (hres : ∀ V : S.Opens, IsAffineOpen V →
      Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) (pstr ∣_ V)))
    (hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (Q : Scheme.{u}) (qstr : Q ⟶ (V : Scheme.{u})),
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) qstr) ∧ W qstr) :
    W pstr := by
  refine of_forall_isAffineOpen_morphismRestrict pstr W fun V hV => ?_
  obtain ⟨hP⟩ := hres V hV
  obtain ⟨Q, qstr, ⟨hQ⟩, hWQ⟩ := hloc V hV
  exact transport_of_isRelPicOf hP hQ hWQ

/-- **THE SCHEME-THEORETIC GLUING** (sorry leaf, cut 2026-07-31 out of
`exists_isRelPicOverAffines_of_forall_isAffineOpen`) — Stacks 01JJ / 01LH.

Glue the local Picard schemes into a single `P ⟶ S` whose restriction to
each affine open of `S` again represents the local relative Picard functor.
This is step 1 (and the `inj`/`surj` half of step 3) of the route recorded
on the parent, and NOTHING ELSE: no classifying sheaf is produced here.

**IT IS UNCONDITIONAL, and that is deliberate.**  No properness, no
smoothness, no connectedness, no section, no `f_*𝒪 = 𝒪`.  The whole
argument is Yoneda plus mathlib's relative gluing:

1. The affine opens of `S`, ordered by inclusion, form a locally directed
   open cover (given `x ∈ V ⊓ W` there is an affine open `⊆ V ⊓ W`
   containing `x`, since affine opens are a basis), so
   `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` in
   `Mathlib/AlgebraicGeometry/RelativeGluing.lean` applies once the `P_V`
   are assembled into a functor with equifibered structure maps.
2. The structure map for `W ≤ V` is `P_W ≅ P_V ×_V W ⟶ P_V`.  Two
   sublemmas are wanted first and neither is stated as a leaf, because
   both are routine and neither is consumed anywhere else in this file:
   *`IsRelPicOf` is stable under base change of the base* (pullback
   pasting: `RelPoint (pullback.snd pstr g) h ≃ RelPoint pstr (h ≫ g)`,
   and `curveBaseChange (curveBaseChangeProj strX g) h ≅ curveBaseChange
   strX (h ≫ g)`), and *`IsRelPicOf` transports along an isomorphism of
   representing objects over the base* (relabel `RelPoint`s along the
   iso).  The comparison isomorphism itself is `IsRelPicOf.isoOver`,
   PROVEN above.
3. Functoriality and equifiberedness are then FORCED rather than checked:
   two maps `P_U ⟶ P_V` over `U ↪ V` are both `RelPoint`s of `pstr_V` at
   the same base map and classify the same sheaf, so `IsRelPicOf.inj`
   equates them.  This is the same "uniqueness makes the diagram
   commute" move that `inj_of_isRelPicOverAffines` runs one level down.
4. Finally `RelativeGluingData.isPullback_natTrans_ι_toBase` gives
   `P_V ≅ pstr ⁻¹ᵁ V` over `V`, and the second sublemma of (2) carries
   `IsRelPicOf` across it to `pstr ∣_ V`.

**FAITHFULNESS AUDIT (fresh statement, nothing inherited).**  TRUE, by the
route above.  The hypothesis is not vacuous — `exists_relPicOf_isAffineOpen`
supplies it — and the conclusion is not vacuous either, since it is an
existential whose witness the route constructs.

*Why dropping all the geometric hypotheses is SAFE rather than reckless.*
Dropping a hypothesis strengthens a leaf, so this is the direction that can
turn a true statement false, and it deserves the explicit check: every step
(1)–(4) above quantifies only over `IsRelPicOf` structures and mathlib
gluing, and `IsRelPicOf` is a bare functor-of-points condition with no
geometric content.  The precedent is `inj_of_isRelPicOverAffines`, which was
likewise expected to need `_o` and `_hpush` and turned out to need nothing.
**If a prover does find a step that needs one of them, the repair is local
and costs nothing:** re-add it to this signature, and the sole consumer
(`exists_isRelPicOverAffines_of_forall_isAffineOpen`, just below) has all
five in scope and passes them.  Record the failure in this docstring if so —
that is more valuable than the generality. -/
theorem exists_gluedRelPic_of_forall_isAffineOpen {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (P : Scheme.{u}) (pstr : P ⟶ (V : Scheme.{u})),
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S),
      ∀ V : S.Opens, IsAffineOpen V →
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) (pstr ∣_ V)) :=
  sorry

/-- **THE RIGIDIFIED POINCARÉ BUNDLE** (sorry leaf, cut 2026-07-31 out of
`exists_isRelPicOverAffines_of_forall_isAffineOpen`) — step 2 of that
leaf's route, and the ONLY place `_o` and `_hpush` are spent.

Given a `pstr : P ⟶ S` whose restriction to every affine open of `S`
represents the local relative Picard functor, produce the GLOBAL data of
`IsRelPicOverAffines`: a classifying sheaf `sheaf p` for a `T`-point of `P`
over an ARBITRARY `g : T ⟶ S`, its invertibility, its naturality
`sheaf_pre`, and `inj`/`surj` relative to it over the affine opens.

**Why this cannot be done by gluing the local `sheaf` functions**, which is
the whole reason the cut is here and not one field earlier: `IsRelPicOf` is
a `Nonempty` existence statement, so the hypothesis hands out one UNRELATED
structure per affine open, and two structures on the same `pstr ∣_ V` need
not agree — replace `sheaf` by `fun p => modDual (sheaf p)` and every field
survives (`inj` because dualising is an involution on classes, `surj`
because it is a bijection, `sheaf_pre` because pullback commutes with
duals).  So the local `sheaf`s differ by an automorphism of the functor
`Pic(X_-)/Pic(-)` and there is nothing to glue along.

**The classical route.**  Apply the local `surj` to the identity point of
`pstr ∣_ V` to get a universal sheaf on `X ×_S (pstr ⁻¹ᵁ V)`; rigidify it
along `_o` — normalise its pullback along the section to `𝒪` — and glue the
rigidified sheaves, which IS canonical because `_hpush` (`f_*𝒪 = 𝒪`
universally) makes a rigidified sheaf have only the identity automorphism.
`sheaf p` is then the pullback of the glued universal sheaf along the map
`X_T ⟶ X_P` induced by `p`; `invertible` and `sheaf_pre` are immediate from
that description, `sheaf_pre` because pullback along
`X_{T'} ⟶ X_T ⟶ X_P` composes.  `inj` and `surj` over an affine open then
transport the local structure through `pstr ∣_ V`, which is the hypothesis.

**Both `_o` and `_hpush` are load-bearing and must not be dropped "because
the gluing is formal"**: without them there is no canonical universal sheaf
to glue.  Contrast the sibling leaf
`exists_gluedRelPic_of_forall_isAffineOpen`, which needs neither — the
SCHEME glues unconditionally, the SHEAF does not.

**FAITHFULNESS AUDIT (fresh statement, nothing inherited).**  TRUE, by the
route above.  Drop `_hpush` and it is FALSE, not merely unprovable: for
`X = S ⊔ S` the sequence `0 ⟶ Pic T ⟶ Pic X_T ⟶ P(T) ⟶ Br T` breaks, a
class is locally but not globally in the image, and `surj` fails at a `T`
covered by two affine opens.  Drop `_o` and the Brauer obstruction is not
killed, so the local universal sheaves have no cocycle to glue along.
`_hproper`, `_hsmooth` and `_hconn` are the standing hypotheses of
`_hpush`'s own provenance and are kept for that reason; a prover who finds
them idle should say so rather than delete them, since deleting an input
from a released signature churns consumers for no mathematical gain (the
same policy `smooth_of_isRelPicOf` records for its own `_hpush`).

NOT VACUOUS: the hypothesis `_hres` is what
`exists_gluedRelPic_of_forall_isAffineOpen` produces. -/
theorem nonempty_isRelPicOverAffines_of_restrict {X P S : Scheme.{u}} (strX : X ⟶ S)
    {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hres : ∀ V : S.Opens, IsAffineOpen V →
      Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) (pstr ∣_ V))) :
    Nonempty (IsRelPicOverAffines strX pstr) :=
  sorry

/-- **THE GLUING STEP** (sorry leaf) — Stacks 01JJ / 01LH, plus the
rigidified Poincaré bundle.

From a relative Picard scheme over every affine open of `S`, produce a
single `P ⟶ S` carrying a GLOBAL classifying sheaf and representing
`Pic_{X/S}` over each affine open.  This is where all of the
scheme-theoretic gluing lives, and the only leaf of the three that
constructs anything.

Route, in the order a prover meets it:

1. `P` itself.  The affine opens of `S`, ordered by inclusion, form a
   locally directed open cover (given `x ∈ V ⊓ W` there is an affine open
   `⊆ V ⊓ W` containing `x`), so `AlgebraicGeometry.Scheme.Cover.RelativeGluingData`
   in `Mathlib/AlgebraicGeometry/RelativeGluing.lean` applies once the
   `P_V` are assembled into a functor with equifibered structure maps.
   The structure map for `W ≤ V` is the composite
   `P_W ≅ P_V ×_V W ⟶ P_V`, where the isomorphism is the comparison of two
   representing objects; it exists by Yoneda and is UNIQUE, which is what
   makes the assignment functorial and the squares pullback squares.  Two
   sublemmas are wanted first — `IsRelPicOf` is stable under base change
   of `S`, and two schemes representing `Pic_{X/S}` are canonically
   isomorphic over `S` — but neither is stated as a leaf here because
   nothing in the assembly consumes them.
2. `sheaf`.  NOT by gluing the local `sheaf` functions (see the section
   note: they differ by an automorphism of the functor).  Apply the local
   `surj` to the identity point of `P_V` to get a universal sheaf on
   `X ×_S P_V`, rigidify it along `_o` — i.e. normalise its pullback along
   the section to `𝒪` — and glue the rigidified sheaves, which is
   canonical because `_hpush` makes a rigidified sheaf have only the
   identity automorphism.  `sheaf p` is then the pullback of the glued
   universal sheaf along the map `X_T ⟶ X_P` induced by `p`, and
   `invertible` and `sheaf_pre` are immediate from that description —
   `sheaf_pre` because pullback along `X_{T'} ⟶ X_T ⟶ X_P` composes.
3. `inj`, `surj` over an affine open: transport the local structure
   through the isomorphism `P ×_S V ≅ P_V`.

Both `_o` and `_hpush` are load-bearing at step 2 and must not be dropped
"because the gluing is formal": without them there is no canonical
universal sheaf to glue.

**ROUTE AUDIT 2026-07-30 — step 1's tool EXISTS, and the obstacle is not
where the route above puts it.**  Checked against the pin rather than
recalled: `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` is real, in
`Mathlib/AlgebraicGeometry/RelativeGluing.lean` (195 lines, `@[stacks
01LH]`), and it does deliver what step 1 wants — `glued`, `toBase`,
`ι_toBase`, `cover`, and `isPullback_natTrans_ι_toBase` (the preimage of
`Uᵢ` in the glued scheme IS `Xᵢ`).  Its side conditions are all
satisfiable here: `[𝒰.LocallyDirected]` is the "affine opens are closed
under refinement inside an intersection" fact the route already cites,
and `[Small.{u} 𝒰.I₀]` / `[Quiver.IsThin 𝒰.I₀]` hold because the index
category is the POSET `S.Opens`.

**But its input is a FUNCTOR `𝒰.I₀ ⥤ Scheme` together with an EQUIFIBERED
natural transformation — not a family of schemes with comparison
isomorphisms.**  `_hloc` supplies a bare `∃` per affine open, i.e. after
choice an unrelated `P_V` for each `V` with NO maps between them.  Yoneda
gives a canonical iso `P_W ≅ P_V ×_V W` for each `W ≤ V`, so the maps
exist, but assembling them into a functor requires the composites to
agree ON THE NOSE, and chosen-by-`Classical.choice` objects give that
only after the uniqueness argument is made functorial.  That — not the
gluing — is where the first real work of this leaf sits, and no version
of the route note has named it.  A prover should expect to prove the two
sublemmas the route above dismisses as "not stated as a leaf here because
nothing in the assembly consumes them" (`IsRelPicOf` is stable under base
change of `S`; two representing objects are canonically isomorphic over
`S`), since they are exactly what makes the functor well defined.

Step 2 is untouched by this and remains the larger half: gluing the
rigidified universal sheaves needs descent for `SheafOfModules` along an
open cover, which this module does not have and mathlib does not supply
in the form wanted. -/
theorem exists_isRelPicOverAffines_of_forall_isAffineOpen {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (P : Scheme.{u}) (pstr : P ⟶ (V : Scheme.{u})),
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) ∧
          Smooth pstr ∧ IsSeparated pstr) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S),
      Nonempty (IsRelPicOverAffines strX pstr) ∧ Smooth pstr ∧ IsSeparated pstr := by
  obtain ⟨P, pstr, hres⟩ := exists_gluedRelPic_of_forall_isAffineOpen strX
    fun V hV => by obtain ⟨Q, qstr, hq, -⟩ := _hloc V hV; exact ⟨Q, qstr, hq⟩
  refine ⟨P, pstr,
    nonempty_isRelPicOverAffines_of_restrict strX _hproper _hsmooth _hconn _o _hpush hres,
    ?_, ?_⟩
  · exact transport_of_forall_isAffineOpen (W := @Smooth) hres
      fun V hV => by obtain ⟨Q, qstr, hq, hs, -⟩ := _hloc V hV; exact ⟨Q, qstr, hq, hs⟩
  · exact transport_of_forall_isAffineOpen (W := @IsSeparated) hres
      fun V hV => by obtain ⟨Q, qstr, hq, -, hs⟩ := _hloc V hV; exact ⟨Q, qstr, hq, hs⟩

/-- **INJECTIVITY IS ZARISKI-LOCAL ON THE BASE** (**PROVEN 2026-07-30**;
formerly a sorry leaf) — and it is UNCONDITIONAL: no `_o`, no `_hpush`,
no properness, smoothness or connectedness.

The absence of hypotheses was deliberate and is now compiler-checked
rather than merely claimed.  The proof is: cover `T` by the preimages
`g ⁻¹ᵁ V` of the affine opens of `S`, which do cover because the affine
opens cover `S`, and note that the restriction of `g` to `g ⁻¹ᵁ V`
factors through `V` (that factorisation is literally `g ∣_ V`, with
`morphismRestrict_ι`), so `hP.inj` applies there.  `hP.sheaf_pre`
identifies `sheaf (p|ᵢ)` with the pullback of `sheaf p`, the transport
lemma `relPicEquiv_modPullback` carries the hypothesis across, and
`relPicEquiv_trans`/`relPicEquiv_symm` compose the three relations.  So
`p|ᵢ = q|ᵢ` for every `i`, and a morphism out of a scheme is determined
by its restrictions to an open cover — `Scheme.hom_ext_of_forall`, after
`Subtype.ext` strips the `RelPoint` factorisation condition.

Two notes for whoever reads this next.  The route note's "the only step
with any content is the transport of `RelPicEquiv` along `modPullback`"
was accurate: that step is now `relPicEquiv_modPullback` above, and every
other line here is bookkeeping.  And the equality of `RelPoint`s really
does reduce to equality of the underlying morphisms, since `RelPoint` is
a subtype cut out by a Prop, which is why no compatibility of the
factorisations through `pstr` has to be checked separately. -/
theorem inj_of_isRelPicOverAffines {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hP : IsRelPicOverAffines strX pstr) {T : Scheme.{u}} {g : T ⟶ S}
    (p q : RelPoint pstr g) (h : RelPicEquiv strX g (hP.sheaf p) (hP.sheaf q)) :
    p = q := by
  apply Subtype.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x) (U := ⊤) trivial
  refine ⟨g ⁻¹ᵁ V, hxV, ?_⟩
  have hfac : FactorsThroughAffineOpen ((g ⁻¹ᵁ V).ι ≫ g) :=
    ⟨V, hV, g ∣_ V, morphismRestrict_ι g V⟩
  refine congrArg Subtype.val
    (hP.inj hfac (RelPoint.pre (g ⁻¹ᵁ V).ι rfl p) (RelPoint.pre (g ⁻¹ᵁ V).ι rfl q) ?_)
  refine relPicEquiv_trans _ _ (hP.sheaf_pre (g ⁻¹ᵁ V).ι rfl p) ?_
  refine relPicEquiv_trans _ _ (relPicEquiv_modPullback strX (g ⁻¹ᵁ V).ι rfl h) ?_
  exact relPicEquiv_symm _ _ (hP.sheaf_pre (g ⁻¹ᵁ V).ι rfl q)

/-- **THE RELATIVE PICARD RELATION IS A ZARISKI SHEAF CONDITION ON `T`**
(sorry leaf, cut 2026-07-31 out of `surj_of_isRelPicOverAffines`) — two
invertible sheaves on `X_T` that are `RelPicEquiv` locally on `T` are
`RelPicEquiv`.

This is the whole mathematical content of BLR 8.1/4 as this file needs it.
The other half of `surj_of_isRelPicOverAffines` — gluing the local
classifying points `pᵢ` into one `p : T ⟶ P` — is PROVEN below, over
`hP.inj` and `Scheme.Cover.glueMorphisms`.

**Route, and it is shorter than the parent's old note claimed.**  Write
`f := curveBaseChangeProj strX g` and `M := L ⊗ L'⁻¹`, invertible by `_hL`,
`_hL'` and `exists_modTensor_inv`.  The hypothesis says `M|_{f⁻¹Uᵢ} ≅ f^*Nᵢ`
for an open cover `Uᵢ` of `T`.  Then:

* **the local twists are CANONICAL, hence glue with nothing to check.**  The
  projection formula for an INVERTIBLE `Nᵢ` is local on the base, so it needs
  neither quasi-coherence nor properness, and it gives
  `f_*(M|_{f⁻¹Uᵢ}) ≅ f_*(f^*Nᵢ) ≅ Nᵢ ⊗ f_*𝒪 ≅ Nᵢ` — the last step by
  `_hpush`.  And `f_*(M|_{f⁻¹Uᵢ}) = (f_*M)|_{Uᵢ}`, because pushforward along
  `f` of a restriction to `f⁻¹Uᵢ` is by definition the restriction to `Uᵢ`.
  So `N := f_*M` is already invertible and `Nᵢ ≅ N|_{Uᵢ}`;
* **the counit `f^*f_*M ⟶ M` is then an isomorphism**, because over `Uᵢ` it is
  the counit at `f^*Nᵢ`, which the triangle identity makes the identity, and
  being an isomorphism is local.

So `M ≅ f^*N` with `N` invertible, which is `RelPicEquiv strX g L L'`.

**WHICH HYPOTHESES ARE LOAD-BEARING — this CORRECTS the parent's old route
note.**  That note said the descent had two hypothesis-consuming halves: a
separatedness one needing `_hpush`, and a glueing one where `_o` "kills the
resulting class in `Br T`".  The second half does not arise.  The `Nᵢ` are not
merely isomorphic on overlaps, they are the RESTRICTIONS of one sheaf `f_*M`,
so there is no cocycle to obstruct and no Brauer class to kill.  The route
above consumes `_hpush` and nothing else.

`_hproper`, `_hsmooth`, `_hconn` and `_o` are nevertheless kept in the
signature: the caller has all four, keeping them costs a prover nothing, and
someone who finds the rigidified route easier than the projection-formula one
should feel free to spend `_o`.  Do NOT read their presence as a claim that
they are needed.

**FAITHFULNESS.**  `_hpush` is genuinely load-bearing, and the statement is
FALSE for a proper morphism that has a section but has `f_*𝒪 ≠ 𝒪`.  Take
`X = S ⊔ S` with `strX` the codiagonal — proper, and WITH a section, namely
either inclusion — and `S = T = ℙ¹_k`, `g = 𝟙`.  Then `X_T = T ⊔ T`, a module
on it is a pair, and `f^*N = (N, N)`, so `RelPicEquiv (A, B) (A', B')` says
`A ≅ A' ⊗ N` and `B ≅ B' ⊗ N` for ONE `N`.  For `L = (𝒪, 𝒪(1))` and
`L' = (𝒪, 𝒪)` that forces `𝒪(1) ≅ 𝒪`, which is false; but on every affine
open `U ⊆ ℙ¹` the restriction `𝒪(1)|_U` IS trivial, so `L` and `L'` are
`RelPicEquiv` locally on `T`.

Note carefully what this does and does not show.  That `X` is not smooth of
relative dimension `1` and not geometrically connected, so the counterexample
refutes the statement for a GENERAL proper morphism with a section, not in the
presence of `_hsmooth`/`_hconn` — from which `_hpush` follows anyway (`H⁰` of a
proper geometrically connected curve over a field is the field).  `_hpush` is
the property actually doing the work, which is precisely why the parent carries
it as a hypothesis of its own.  The parent's old note cited the same
`X = S ⊔ S` but attributed the failure to the absence of a section; that
morphism has one, so the citation was right and its reading was not. -/
theorem relPicEquiv_of_locally_relPicEquiv {X S : Scheme.{u}} {strX : X ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    {T : Scheme.{u}} {g : T ⟶ S} {L L' : (curveBaseChange strX g).Modules}
    (_hL : IsInvertibleSheaf L) (_hL' : IsInvertibleSheaf L')
    (_hloc : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      RelPicEquiv strX (U.ι ≫ g) (modPullback (curveBaseChangeMap strX U.ι rfl) L)
        (modPullback (curveBaseChangeMap strX U.ι rfl) L')) :
    RelPicEquiv strX g L L' :=
  sorry

/-- **`Pic(X_-)/Pic(-)` IS A ZARISKI SHEAF — BLR 8.1/4** (sorry leaf).

The genuine content of `surj_of_isRelPicOverAffines` below, cut out of it
2026-07-30 so that the scheme-theoretic gluing (which is bookkeeping) and
the descent (which is not) have separate owners.  Nothing in this
statement mentions `pstr`, `IsRelPicOverAffines` or a representing
scheme: it is a statement about two invertible sheaves on `X_T`, and it
is reusable wherever the relative Picard relation has to be globalised.

**Route.**  Write `A ≅ B ⊗ π^*Nᵢ` over each `Uᵢ` of the cover.  Put
`M := A ⊗ B^{-1}`, so `M|_{X_{Uᵢ}} ≅ π^*Nᵢ`, and let `σ : T ⟶ X_T` be the
base-changed section `relBasePoint _o g`.  Then `N := σ^*M` is the global
candidate — `σ^*π^*Nᵢ ≅ Nᵢ` because `π ≫ σ = 𝟙`, so `N|_{Uᵢ} ≅ Nᵢ` — and
what has to be shown is `M ≅ π^*σ^*M`.  Locally both sides are `π^*Nᵢ`;
the local isomorphisms `φᵢ` differ on overlaps by an automorphism of an
invertible sheaf, i.e. by a unit in `Γ(X_{Uᵢⱼ}, 𝒪ˣ)`, and `_hpush`
(`f_*𝒪 = 𝒪` universally) identifies that group with `Γ(Uᵢⱼ, 𝒪ˣ)`.
RIGIDIFY: normalise each `φᵢ` so that `σ^*φᵢ = id`.  A unit pulled back
from `Uᵢⱼ` and restricted along the section is itself, so the normalised
cocycle is trivial and the `φᵢ` glue.  Both hypotheses are spent exactly
once: `_hpush` to know the automorphisms come from downstairs, `_o` to
have anything to rigidify along.

**FALSITY AUDIT (2026-07-30).**  This is not a first restatement of an
audited parent — the parent's audit was about `surj`'s consumption of the
same two hypotheses — so it is run here from scratch against THIS
statement.

*Dropping `_hpush` (equivalently `_hconn`) makes it FALSE, with an
explicit witness.*  Take `X = C ⊔ C` for `C ⟶ S` a smooth proper curve
with a section `o` — the disjoint union still has the section into the
first copy, so `_o` survives, and it is still proper and smooth of
relative dimension 1, so `_hproper` and `_hsmooth` survive; only
connectedness fails, and with it `f_*𝒪 = 𝒪` (it becomes `𝒪 × 𝒪`).  Pick
`T` with `Pic T ≠ 0` and `N` a nontrivial invertible sheaf on `T`.  Then
`X_T = C_T ⊔ C_T`; put `B := 𝒪` and `A := (π^*N, 𝒪)`, invertible.  Over
any open `U ⊆ T` trivialising `N` we get `A| ≅ B| ⊗ π^*𝒪`, so the
covering hypothesis holds.  Globally `A ≅ B ⊗ π^*N'` would read
`(π^*N, 𝒪) ≅ (π^*N', π^*N')`, forcing `N' ≅ 𝒪` on the second copy and
`N' ≅ N` on the first — each copy has a section, so `π^*` is faithful on
isomorphism classes — hence `N ≅ 𝒪`, contrary to choice.  Concretely
`S = Spec ℤ`, `C = E` an elliptic curve, `T = ℙ¹`, `N = 𝒪(1)`.

*Dropping `_o` makes it FALSE too, but the witness is not elementary.*
Without a section the rigidification is unavailable and the obstruction
to gluing the `φᵢ` is a class in `Br T`; the sequence
`0 ⟶ Pic T ⟶ Pic X_T ⟶ P(T) ⟶ Br T` is exact and its last map is nonzero
in general (a conic bundle over `T` with nontrivial Brauer class is the
standard source).  So `_o` is load-bearing and not decoration, but the
counterexample is cited rather than exhibited, and that is the honest
state of this clause.

*`_hA`/`_hB` are load-bearing.*  `B^{-1}` has to exist for `M` to be
formed; with `B` arbitrary the local isomorphisms cannot be compared.
*`_hproper`, `_hsmooth`, `_hconn` are carried but not directly used* —
they are what a prover will consume in producing `_hpush` and in knowing
`π` has the section, and they cost nothing here. -/
theorem relPicEquiv_of_forall_restrict {X S : Scheme.{u}} (strX : X ⟶ S)
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    {T : Scheme.{u}} {g : T ⟶ S} (A B : (curveBaseChange strX g).Modules)
    (_hA : IsInvertibleSheaf A) (_hB : IsInvertibleSheaf B)
    (_hcov : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧
      RelPicEquiv strX (U.ι ≫ g)
        (modPullback (curveBaseChangeMap strX U.ι rfl) A)
        (modPullback (curveBaseChangeMap strX U.ι rfl) B)) :
    RelPicEquiv strX g A B :=
  sorry

/-- **SURJECTIVITY IS ZARISKI-LOCAL ON THE BASE — BLR 8.1/4**
(**PROVEN 2026-07-30** over `relPicEquiv_of_forall_restrict`; formerly a
bare sorry leaf).  This is the one place `_o` and `_hpush` are consumed,
and the statement is FALSE without them — but they are now consumed
*through* that leaf rather than here, and this proof passes them straight
along without touching them.

The route the old docstring recorded is what went through, verbatim, so
it is kept below with the one correction that the last step is now a
named leaf rather than an aspiration.

Given `L` invertible on `X_T`, the affine-local `surj` gives classifying
points `pᵢ` over the cover `g ⁻¹ᵁ Vᵢ` of `T`; on overlaps
`sheaf (pᵢ|) ≡ L| ≡ sheaf (pⱼ|)`, so `hP.inj` — an overlap still lies
over `Vᵢ`, so the affine-local field applies directly, and
`inj_of_isRelPicOverAffines` is not needed — makes them agree, and they
glue to `p : T ⟶ P` via `Scheme.Cover.glueMorphisms`.  What is left is
the genuine content: `sheaf p` and `L` are `RelPicEquiv` locally on `T`
and must be shown `RelPicEquiv` globally, i.e. `T ↦ Pic(X_T)/Pic(T)` is a
Zariski sheaf.  That last sentence IS `relPicEquiv_of_forall_restrict`,
and its own docstring carries the two hypothesis-consuming halves
(separatedness from `_hpush`, glueing from `_o`) together with the
refutation that drops them.

**Two things this proof needed that the old note did not mention**, both
now hoisted next to `curveBaseChangeMap_proj` above.  The overlap
compatibility is an equation between two `RelPoint`s over the overlap's
own structure morphism, and reaching it from each side requires
`modPullbackCurveBaseChangeCompIso` (composition of base changes) and, on
the second side only, `curveBaseChangeMap_congr` to absorb
`pullback.condition`.  Neither is deep; both are invisible from the
mathematics and cost a prover real time to rediscover.

The cover used is the preimages `g ⁻¹ᵁ V` of affine opens of `S`, indexed
by the POINTS of `T` — the same device `inj_of_isRelPicOverAffines` uses,
and the reason no quasi-compactness of `T` is wanted anywhere. -/
theorem surj_of_isRelPicOverAffines {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (hP : IsRelPicOverAffines strX pstr) {T : Scheme.{u}} {g : T ⟶ S}
    (L : (curveBaseChange strX g).Modules) (hL : IsInvertibleSheaf L) :
    ∃ p : RelPoint pstr g, RelPicEquiv strX g (hP.sheaf p) L := by
  -- an affine open of `S` around the image of each point of `T`
  have hkey : ∀ t : T, ∃ V : S.Opens, IsAffineOpen V ∧ t ∈ g ⁻¹ᵁ V := fun t => by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := S) (x := g.base t) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hVaff hVmem using hkey
  have hfac : ∀ t : T, FactorsThroughAffineOpen ((g ⁻¹ᵁ V t).ι ≫ g) :=
    fun t => ⟨V t, hVaff t, g ∣_ V t, morphismRestrict_ι g (V t)⟩
  -- the local classifying points, one over each `g ⁻¹ᵁ V t`
  choose q hq using fun t : T => hP.surj (hfac t)
    (modPullback (curveBaseChangeMap strX (g ⁻¹ᵁ V t).ι rfl) L)
    (isInvertibleSheaf_modPullback _ hL)
  -- they agree on the overlaps, by `hP.inj` over the pullback of the two opens
  have hcompat : ∀ s t : T, pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ (q s).1
      = pullback.snd (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ (q t).1 := by
    intro s t
    have hab : pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ (g ⁻¹ᵁ V s).ι
        = pullback.snd (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ (g ⁻¹ᵁ V t).ι := pullback.condition
    have hb : pullback.snd (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ ((g ⁻¹ᵁ V t).ι ≫ g)
        = pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ ((g ⁻¹ᵁ V s).ι ≫ g) := by
      rw [← Category.assoc, ← hab, Category.assoc]
    have hfacW : FactorsThroughAffineOpen
        (pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ ((g ⁻¹ᵁ V s).ι ≫ g)) :=
      ⟨V s, hVaff s, pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ (g ∣_ V s), by
        rw [Category.assoc, morphismRestrict_ι]⟩
    -- the two ways of restricting `L` to the overlap agree
    have hmm : curveBaseChangeMap strX (pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι) rfl
          ≫ curveBaseChangeMap strX (g ⁻¹ᵁ V s).ι rfl
        = curveBaseChangeMap strX (pullback.snd (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι) hb
          ≫ curveBaseChangeMap strX (g ⁻¹ᵁ V t).ι rfl := by
      apply pullback.hom_ext
      · simp only [curveBaseChangeMap, Category.assoc, pullback.lift_fst]
      · simp only [curveBaseChangeMap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [hab]
    have heq : RelPicEquiv strX
        (pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι ≫ ((g ⁻¹ᵁ V s).ι ≫ g))
        (hP.sheaf (RelPoint.pre (pullback.fst (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι) rfl (q s)))
        (hP.sheaf (RelPoint.pre (pullback.snd (g ⁻¹ᵁ V s).ι (g ⁻¹ᵁ V t).ι) hb (q t))) := by
      refine relPicEquiv_trans _ _ (hP.sheaf_pre _ rfl (q s)) ?_
      refine relPicEquiv_trans _ _ (relPicEquiv_modPullback strX _ rfl (hq s)) ?_
      refine relPicEquiv_trans _ _ (relPicEquiv_of_iso _ _
        (modPullbackCompIso _ _ L ≪≫ modPullbackCongrIso hmm L
          ≪≫ (modPullbackCompIso _ _ L).symm)) ?_
      exact relPicEquiv_symm _ _ (relPicEquiv_trans _ _ (hP.sheaf_pre _ hb (q t))
        (relPicEquiv_modPullback strX _ hb (hq t)))
    exact congrArg Subtype.val (hP.inj hfacW _ _ heq)
  -- glue them into a single `T`-point of `P`
  let 𝒰 : T.OpenCover :=
    { I₀ := T
      X := fun t => ((g ⁻¹ᵁ V t : T.Opens) : Scheme.{u})
      f := fun t => (g ⁻¹ᵁ V t).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x, by simpa using hVmem x⟩, inferInstance⟩ }
  have hpi : ∀ t : T, (g ⁻¹ᵁ V t).ι ≫ 𝒰.glueMorphisms (fun t => (q t).1) hcompat = (q t).1 :=
    fun t => 𝒰.ι_glueMorphisms _ hcompat t
  have hp : 𝒰.glueMorphisms (fun t => (q t).1) hcompat ≫ pstr = g := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ (fun t => ?_)
    rw [← Category.assoc]
    show ((g ⁻¹ᵁ V t).ι ≫ _) ≫ pstr = _
    rw [hpi t, (q t).2]
  -- and the classification descends, which is the new leaf
  refine ⟨⟨_, hp⟩, ?_⟩
  refine relPicEquiv_of_locally_relPicEquiv hproper hsmooth hconn o hpush
    (hP.invertible _) hL (fun t => ⟨g ⁻¹ᵁ V t, hVmem t, ?_⟩)
  have hpre : RelPoint.pre (g ⁻¹ᵁ V t).ι rfl
      (⟨_, hp⟩ : RelPoint pstr g) = q t := Subtype.ext (hpi t)
  refine relPicEquiv_trans _ _ (relPicEquiv_symm _ _ ?_) (hq t)
  rw [← hpre]
  exact hP.sheaf_pre (g ⁻¹ᵁ V t).ι rfl _

/-- **REPRESENTABILITY OF THE RELATIVE PICARD FUNCTOR IS ZARISKI-LOCAL ON
THE BASE** — Stacks 01JJ for the gluing, BLR 8.1/4 for the descent of
`surj` (**PROVEN 2026-07-29** over `exists_isRelPicOverAffines_of_forall_isAffineOpen`,
`inj_of_isRelPicOverAffines` and `surj_of_isRelPicOverAffines`; formerly a
bare sorry leaf).

The affine opens cover `S`, so `_hloc` is a genuine cover hypothesis.  See
the section note above for why the existence statements in `_hloc` need
carry no compatibility data (Yoneda supplies it) and why the geometric
hypotheses are nevertheless load-bearing here (they are what makes
`T ↦ Pic(X_T)/Pic(T)` a Zariski sheaf, hence what lets `surj` be checked
locally).

**Superseded claim, kept here so it is not re-derived.**  This docstring
used to say the proof was "`AlgebraicGeometry.Scheme.GlueData` for the
construction, and then four field-by-field checks on `IsRelPicOf`, of
which `inj` and `sheaf_pre` are local by inspection".  `inj` is indeed
local (`inj_of_isRelPicOverAffines`, and unconditionally so), but
`sheaf_pre` is not "local by inspection" — `sheaf` itself has no local
definition to inspect, since `_hloc` hands out structures that agree only
up to an automorphism of the functor.  The subsection note above gives the
counterexample (dualise) and the repair (a rigidified Poincaré bundle).

The universe warning on the parent's ROUTE AUDIT still stands: do not
reach for `Scheme.LocalRepresentability.isRepresentable`, which takes a
`Type u`-valued sheaf while the naive quotient is a priori
`Type (u+1)`.

**Amended 2026-07-31**: `hloc` and the conclusion now also carry
`Smooth ∧ IsSeparated`, threaded verbatim from
`exists_isRelPicOverAffines_of_forall_isAffineOpen` — the gluing does not
change the scheme `P`, so the two clauses pass straight through with no
argument.  See the audits on `exists_relPicOf_isAffineOpen` and on the
gluing leaf for why they are carried. -/
theorem exists_relPicOf_of_forall_isAffineOpen {X S : Scheme.{u}} (strX : X ⟶ S)
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (hloc : ∀ V : S.Opens, IsAffineOpen V →
      ∃ (P : Scheme.{u}) (pstr : P ⟶ (V : Scheme.{u})),
        Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) ∧
          Smooth pstr ∧ IsSeparated pstr) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S),
      Nonempty (IsRelPicOf strX pstr) ∧ Smooth pstr ∧ IsSeparated pstr := by
  obtain ⟨P, pstr, ⟨hP⟩, hsm, hsep⟩ :=
    exists_isRelPicOverAffines_of_forall_isAffineOpen strX hproper hsmooth hconn o hpush hloc
  exact ⟨P, pstr, ⟨{ sheaf := hP.sheaf
                     invertible := hP.invertible
                     inj := fun p q h => inj_of_isRelPicOverAffines hP p q h
                     surj := fun L hL =>
                       surj_of_isRelPicOverAffines hproper hsmooth hconn o hpush hP L hL
                     sheaf_pre := hP.sheaf_pre }⟩, hsm, hsep⟩

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
  which is what the twins above were waiting on.  **Half of that hoist was
  done on 2026-07-29**: `nonempty_modTensor_assocPic` is gone and
  `nonempty_modTensor_assoc` is declared in this module; only
  `nonempty_modPullback_modTensorPic` still waits.  Do not price it as
  missing machinery again.
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
  MORPHISMS anywhere in `Mathlib/AlgebraicGeometry/` — RE-CHECKED
  2026-07-31, and the project's own `Fermat/FLT/Modularity/AmpleSheaf.lean`
  does not close it either, since `IsAmpleSheaf` is a predicate on a sheaf
  over ONE scheme and carries no projective embedding.  That is why
  `exists_relPicOf_of_isAffineBase` above has to say "affine base" instead
  of "projective", and why step (ii) of FGA 232 cannot be cut out as a leaf
  of its own — there is nothing to state it in terms of. -/
theorem exists_relPicOf_of_hasUniversallyTrivialPushforward {X S : Scheme.{u}} (strX : X ⟶ S)
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g)) :
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S),
      Nonempty (IsRelPicOf strX pstr) ∧ Smooth pstr ∧ IsSeparated pstr :=
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
    ∃ (P : Scheme.{u}) (pstr : P ⟶ S),
      Nonempty (IsRelPicOf strX pstr) ∧ Smooth pstr ∧ IsSeparated pstr := by
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
  relative curve, plus `surj`.  **PROVEN 2026-07-29**, leaving only its
  two `sectionIdeal` obligations open — `isInvertibleSheaf_sectionIdeal` and
  `nonempty_modPullback_sectionIdeal` then, and since 2026-07-31 their
  citation-shaped forms `isInvertibleSheaf_sectionIdeal_of_isSection` and
  `nonempty_modPullback_sectionIdeal_of_isPullback`, the originals having
  become PROVEN assemblies over them;
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

/-- **THE ABEL–JACOBI POINT IS UNIQUE** (PROVEN 2026-07-29 over
`relPicEquiv_cancel_left`) — two points of `Pic` whose classes solve the same
equation `[p] + [x] = [C]` are equal.

This is the formal content of the "Pinned." paragraph on
`exists_abelJacobiPoint` below: the first clause of that leaf determines `aj`
POINTWISE, so the naturality and base-point clauses are theorems about it rather
than extra freedom for an adversary.  It is also how both of those clauses are
proven — each is `hinj` applied to a chain of `RelPicEquiv`s, never a comparison
of the two `Classical.choose`s.

The braiding is spent twice here, to move the cancelled factor `I` from the
right of `sheaf p` to the left, where `relPicEquiv_cancel_left` wants it. -/
theorem IsRelPicOf.eq_of_relPicEquiv_tensor {X P S T : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hP : IsRelPicOf strX pstr) {g : T ⟶ S} {I C : (curveBaseChange strX g).Modules}
    (hI : IsInvertibleSheaf I) {p q : RelPoint pstr g}
    (hp : RelPicEquiv strX g (modTensor (hP.sheaf p) I) C)
    (hq : RelPicEquiv strX g (modTensor (hP.sheaf q) I) C) : p = q := by
  refine hP.inj p q (relPicEquiv_cancel_left strX g hI ?_)
  exact relPicEquiv_trans strX g (relPicEquiv_of_iso strX g (modTensorSymmIso I (hP.sheaf p)))
    (relPicEquiv_trans strX g (relPicEquiv_trans strX g hp (relPicEquiv_symm strX g hq))
      (relPicEquiv_of_iso strX g (modTensorSymmIso (hP.sheaf q) I)))

/-! #### Step (i) ONE MORE TIME: both `sectionIdeal` leaves were stated about a
BASE CHANGE of the curve their citations are about

(2026-07-31, and this is the third instance of the same defect in this file in
two days — see the two CLAUDE.md sections it now has.)  Both leaves below took
their hypotheses on `strX : X ⟶ S` and stated their conclusion about
`relSection x`, which is a section of `curveBaseChangeProj strX g : X ×_S T ⟶ T`.
Stacks 0C4S is a theorem about a section of a smooth relative curve.  It is not
a theorem about a section of the base change of a smooth relative curve over
some other scheme, so the transport had to be done before the citation applied —
and it was invisible, being neither in the statement nor a leaf but a sentence
in the docstring ("Here `Y = X ×_S T`, which is proper and smooth of relative
dimension `1` over `T` because both properties are stable under base change").

The three lemmas here discharge it, reusing the base-change stability lemmas
proven for `exists_relPicOf_of_isAffineBase` above.  Nothing mathematical
happens in any of them; the point is that after them the two leaves can be, and
are, stated in the shape their citations are stated in. -/

/-- **`SheafOfModules.pushforward` along a continuous functor of sites preserves
finite limits**, because it is a right adjoint.

Stated separately from the instance below only so that unification can see the
morphism of sheaves of rings that `Scheme.Modules.restrictFunctor` hides inside
a `letI`; `infer_instance` after `unfold` does not find it on its own. -/
theorem sheafOfModulesPushforward_preservesFiniteLimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [F.IsContinuous J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
  inferInstance

/-- **Restriction of `𝒪`-modules along an open immersion is left exact.**

Not available from `Scheme.Modules.restrictAdjunction`, which exhibits
`restrictFunctor` as a LEFT adjoint; it comes from the *other* description of the
same functor, as a site-level `SheafOfModules.pushforward`. -/
instance restrictFunctor_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  unfold Scheme.Modules.restrictFunctor
  exact sheafOfModulesPushforward_preservesFiniteLimits _

/-- **A sheaf of modules has no nonzero sections over the empty open.** -/
theorem isZero_sections_bot {T : Scheme.{u}} (M : T.Modules) :
    Limits.IsZero (M.presheaf.obj (op (⊥ : T.Opens))) :=
  (Limits.IsZero.iff_id_eq_zero _).2
    ((TopCat.Sheaf.isTerminalOfEmpty
      (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} T.toTopCat)).hom_ext _ _)

/-- **A morphism into a sectionwise-zero sheaf of modules is zero.** -/
theorem hom_eq_zero_of_isZero {Z : Scheme.{u}} {A B : Z.Modules} (f : A ⟶ B)
    (h : ∀ V : Z.Opens, Limits.IsZero (B.presheaf.obj (op V))) : f = 0 := by
  ext V x
  exact congrArg (fun m => AddCommGrpCat.Hom.hom m x) ((h V).eq_of_tgt _ _)

/-- **`𝒪(−σ)` is the whole structure sheaf away from the section.**

On an open `U` whose preimage under `σ` is empty, `σ_*σ^*𝒪` has no sections at
all, so the defining map of `sectionIdeal` restricts to `0` and its kernel
restricts to `𝒪_U`.  Left exactness of restriction — the instance above — is
what lets the kernel be taken after restricting rather than before. -/
noncomputable def sectionIdealRestrictIsoOfDisjoint {Z T : Scheme.{u}} (σ : T ⟶ Z)
    (U : Z.Opens) (hU : σ ⁻¹ᵁ U = ⊥) :
    (sectionIdeal σ).restrict U.ι ≅ modUnit (U : Scheme.{u}) := by
  set φ := (Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Z) with hφ
  have hmap : (Scheme.Modules.restrictFunctor U.ι).map φ = 0 := by
    refine hom_eq_zero_of_isZero _ (fun W => ?_)
    have hbot : σ ⁻¹ᵁ (U.ι ''ᵁ W) = ⊥ :=
      le_bot_iff.1 (hU ▸ Scheme.Hom.preimage_mono σ (Scheme.Opens.ι_image_le U W))
    show Limits.IsZero (((Scheme.Modules.pullback σ).obj (modUnit Z)).presheaf.obj
      (op (σ ⁻¹ᵁ (U.ι ''ᵁ W))))
    rw [hbot]
    exact isZero_sections_bot _
  exact (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) φ) ≪≫
    kernelIsoOfEq hmap ≪≫ kernelZeroIsoSource ≪≫ Scheme.Modules.restrictUnitIso U.ι

/-- **`relSection` really is a section of the base-changed curve** — LOOKS like
`rfl` and is not, since `relSection` is a `pullback.lift`. -/
theorem relSection_proj {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}
    (x : RelPoint strX g) :
    relSection x ≫ curveBaseChangeProj strX g = 𝟙 T := by
  simpa [relSection, curveBaseChangeProj] using pullback.lift_snd (f := strX) (g := g) x.1 (𝟙 T)
    (by rw [x.2, Category.id_comp])

/-- **Sections over a fixed open, as a functor `Z.Modules ⥤ Ab`.**

Named only so that `PreservesLimitsOfShape WalkingParallelPair` can be
registered on it: the composite is what carries the kernel of a map of
`𝒪`-modules to the kernel of the map on sections, which is the one thing the
off-image argument needs. -/
noncomputable def modSectionsAt (Z : Scheme.{u}) (W : Z.Opens) : Z.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf Z ⋙ (CategoryTheory.evaluation (Z.Opensᵒᵖ) Ab.{u}).obj (Opposite.op W)

instance (Z : Scheme.{u}) (W : Z.Opens) :
    PreservesLimitsOfShape WalkingParallelPair (modSectionsAt Z W) := by
  haveI h1 : PreservesLimitsOfShape WalkingParallelPair (Scheme.Modules.toPresheaf Z) := by
    haveI : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.toPresheaf Z) :=
      preservesLimitsOfSize_shrink _
    infer_instance
  haveI h2 : PreservesLimitsOfShape WalkingParallelPair
      ((CategoryTheory.evaluation (Z.Opensᵒᵖ) Ab.{u}).obj (Opposite.op W)) := inferInstance
  unfold modSectionsAt
  exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2

instance (Z : Scheme.{u}) (W : Z.Opens) : (modSectionsAt Z W).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- **Over an open where the TARGET has no sections, the kernel inclusion is an
isomorphism on sections** (PROVEN).  `modSectionsAt Z W` preserves kernels, so
`Γ(ker φ, W) = ker (Γ(φ, W))`, and `Γ(φ, W) = 0` because its target is zero. -/
theorem isIso_kernel_ι_app_of_isZero {Z : Scheme.{u}} {A B : Z.Modules} (φ : A ⟶ B)
    (W : Z.Opens) (hW : IsZero Γ(B, W)) : IsIso (Scheme.Modules.Hom.app (kernel.ι φ) W) := by
  have hz : (modSectionsAt Z W).map φ = 0 := hW.eq_zero_of_tgt _
  haveI : IsIso ((PreservesKernel.iso (modSectionsAt Z W) φ).inv ≫
      Scheme.Modules.Hom.app (kernel.ι φ) W) := by
    show IsIso ((PreservesKernel.iso (modSectionsAt Z W) φ).inv ≫
      (modSectionsAt Z W).map (kernel.ι φ))
    rw [PreservesKernel.iso_inv_ι]
    exact kernel.ι_of_zero hz
  exact IsIso.of_isIso_comp_left (PreservesKernel.iso (modSectionsAt Z W) φ).inv _

/-- **A pushforward has no sections over an open that misses the image**
(PROVEN) — `σ ⁻¹ᵁ W = ⊥`, and a sheaf's sections over `⊥` are terminal. -/
theorem isZero_sections_pushforward_of_notMem {Z T : Scheme.{u}} (σ : T ⟶ Z) (N : T.Modules)
    {W : Z.Opens} (hW : ∀ t : T, σ.base t ∉ W) :
    IsZero Γ((Scheme.Modules.pushforward σ).obj N, W) := by
  have h : σ ⁻¹ᵁ W = ⊥ := by
    ext t
    simpa using hW t
  exact (TopCat.Sheaf.isTerminalOfEqEmpty ⟨N.presheaf, N.isSheaf⟩ h).isZero

/-- **OFF THE IMAGE OF A CLOSED IMMERSION THE IDEAL SHEAF IS TRIVIAL** (PROVEN)
— the off-image half of `isInvertibleSheaf_sectionIdeal`, and it needs neither
smoothness nor a curve.

The trivializing neighbourhood is the whole complement of the (closed) image:
over any open contained in it the target of the adjunction unit has no sections,
so `kernel.ι` is an isomorphism on sections there, hence
`(sectionIdeal σ)|_U ≅ 𝒪_Z|_U ≅ 𝒪_U`. -/
theorem sectionIdeal_restrict_iso_unit_of_notMem_range {Z T : Scheme.{u}} (σ : T ⟶ Z)
    (hσ : IsClosedImmersion σ) (z : Z) (hz : z ∉ Set.range σ.base) :
    ∃ U : Z.Opens, z ∈ U ∧
      Nonempty ((sectionIdeal σ).restrict U.ι ≅ modUnit (U : Scheme.{u})) := by
  haveI := hσ
  have hcl : IsClosed (Set.range σ.base) := σ.isClosedEmbedding.isClosed_range
  refine ⟨⟨(Set.range σ.base)ᶜ, hcl.isOpen_compl⟩, hz, ?_⟩
  set U : Z.Opens := ⟨(Set.range σ.base)ᶜ, hcl.isOpen_compl⟩ with hU
  set η := (Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Z) with hη
  have hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (kernel.ι η)) := by
    refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun V => ?_
    have hzero : IsZero Γ((Scheme.Modules.pushforward σ).obj
        (modPullback σ (modUnit Z)), U.ι ''ᵁ V) := by
      refine isZero_sections_pushforward_of_notMem σ _ fun t ht => ?_
      have h1 : σ.base t ∈ U := U.ι_image_le V ht
      exact (h1 : σ.base t ∈ (Set.range σ.base)ᶜ) ⟨t, rfl⟩
    exact isIso_kernel_ι_app_of_isZero η (U.ι ''ᵁ V) hzero
  exact ⟨(@asIso _ _ _ _ _ hiso) ≪≫ Scheme.Modules.restrictUnitIso U.ι⟩

/-- **A relative point IS a section of the base-changed curve** (PROVEN) —
`relSection x ≫ π_g = 𝟙 T`, one `pullback.lift_snd`, named because three
arguments below start with it. -/
theorem relSection_comp_proj {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}
    (x : RelPoint strX g) : relSection x ≫ curveBaseChangeProj strX g = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- **A SECTION OF A PROPER MORPHISM IS A CLOSED IMMERSION** (PROVEN) — this is
the ONLY place `_hproper` enters `isInvertibleSheaf_sectionIdeal`, and it enters
only through separatedness of the base-changed projection: `relSection x`
followed by `π_g` is the identity, hence a closed immersion, and
`IsClosedImmersion.of_comp` then peels off the second factor because `π_g` is
separated. -/
theorem isClosedImmersion_relSection {X S T : Scheme.{u}} {strX : X ⟶ S}
    (_hproper : IsProper strX) {g : T ⟶ S} (x : RelPoint strX g) :
    IsClosedImmersion (relSection x) := by
  have h3 : IsClosedImmersion (relSection x ≫ curveBaseChangeProj strX g) := by
    rw [relSection_proj]; infer_instance
  exact IsClosedImmersion.of_comp _ (curveBaseChangeProj strX g)

/-- **A SECTION OF A PROPER MORPHISM IS A CLOSED IMMERSION** (PROVEN) — the bare
version of `isClosedImmersion_relSection` just above, for an arbitrary section of
an arbitrary morphism rather than for `relSection` on a base-changed curve.

Same three lines: `σ ≫ strY = 𝟙` is a closed immersion, and
`IsClosedImmersion.of_comp` peels off the second factor because `IsProper`
extends `IsSeparated`.  Properness is spent ONLY here, in the whole of the
`sectionIdeal` development. -/
theorem isClosedImmersion_of_isSection {Y T : Scheme.{u}} (strY : Y ⟶ T)
    (hproper : IsProper strY) {σ : T ⟶ Y} (hσ : σ ≫ strY = 𝟙 T) :
    IsClosedImmersion σ := by
  haveI := hproper
  haveI : IsClosedImmersion (σ ≫ strY) := by rw [hσ]; infer_instance
  exact IsClosedImmersion.of_comp σ strY

/-- **`𝒪(−σ)` IS LOCALLY TRIVIAL AT THE SECTION** (sorry leaf) — the ON-IMAGE
half of `isInvertibleSheaf_sectionIdeal_of_isSection` below, which is now PROVEN
over it, and the only place `_hsmooth` is spent anywhere in this development.

Stacks 0C4S / EGA IV 17.12.1.  At `σ(t)`, `strY` is smooth of relative dimension
`1`, so there is an affine neighbourhood on which `strY` is standard smooth of
relative dimension `1` and the section is cut out by a single element `s` whose
image in the fibre over `t` generates the maximal ideal of a regular
one-dimensional local ring.  `s` is then a nonzerodivisor, so `𝒪 ⟶ 𝒪`, `1 ↦ s`
is injective with image the ideal — i.e. `(sectionIdeal σ)|_U ≅ 𝒪_U`.

**DEDUPLICATED AND RESHAPED 2026-07-31.**  Until today this slot held TWO leaves,
`exists_trivialization_sectionIdeal_at_section` and
`exists_trivialization_sectionIdeal_at`, whose statements were
CHARACTER-FOR-CHARACTER IDENTICAL — two branches cut
`isInvertibleSheaf_sectionIdeal` the same way on 2026-07-30 and 2026-07-31 under
different names, and a union-style merge kept both.  Worse, by then BOTH were
consumerless: the 2026-07-31 reshaping of `isInvertibleSheaf_sectionIdeal` routed
it through the new `isInvertibleSheaf_sectionIdeal_of_isSection`, which is stated
about a bare morphism and so could not consume either.  So the file was carrying
one piece of mathematics three times, twice as free-floating code.  The survivor
is restated here in the bare-morphism shape its consumer needs; the duplicate is
deleted (recover it with `git show <this commit>^`).

**What a prover may assume, and what is already done.**  The complementary case
— a point NOT on the section — is PROVEN above
(`sectionIdeal_restrict_iso_unit_of_notMem_range`, over
`sectionIdealRestrictIsoOfDisjoint` and `isClosedImmersion_of_isSection`), so
nothing here needs to say anything about points off the image, and the section's
image being closed is already available.  The definition to work from is
`sectionIdeal σ = ker (𝒪_Y ⟶ σ_*σ^*𝒪_Y)`; there is no divisor theory at this
pin, which is why the leaf is stated as local triviality of that kernel rather
than as "effective Cartier divisor".

**FAITHFULNESS — re-run against the reshaped statement, since the reshaping
changes what `Y ⟶ T` ranges over (the old form quantified only over base changes
of a fixed curve, this one over every proper smooth relative curve, so the class
is strictly LARGER and an inherited audit would not transfer).  Both witnesses
survive verbatim, because both were always stated as curves over a base rather
than as base changes.**

* `_hsmooth` is the whole statement and cannot be dropped.  For the nodal cubic
  `y² = x³ + x²` over a field, the ideal of a section through the node needs two
  generators, because the local ring is not regular there.  The
  relative-dimension-`1` part is equally load-bearing and fails in the *other*
  direction: at relative dimension `2` a section is a regular immersion of
  CODIMENSION `2`, so its ideal has rank `2` along the section — `𝔸²_T` with the
  zero section is the smallest witness.
* `_hσ` — that `σ` is a SECTION — is load-bearing: an arbitrary `σ : T ⟶ Y` need
  not be an immersion at all, and `ker (𝒪_Y ⟶ σ_*𝒪_T)` is then not the ideal of a
  divisor.  Take `T = Y` and `σ = 𝟙 Y` for `Y` a curve of positive genus: the
  kernel is `0`, which is not locally trivial.  In the old form this was implicit
  in `σ = relSection x`; making it explicit is what lets the statement mention no
  base change.
* `_hproper` is **not known to be necessary for THIS half.**  The parent's audit
  refutes the properness-free statement with the affine line with doubled origin,
  and that witness works at the SECOND origin — a point which is *off* the image
  of the section, hence handled by
  `sectionIdeal_restrict_iso_unit_of_notMem_range` above, which is where
  properness is genuinely spent (through `isClosedImmersion_of_isSection`).  At a
  point ON the image, a section of a merely separated-or-worse morphism is still
  a closed immersion into some open neighbourhood, and the argument above goes
  through.  The hypothesis is kept because it costs the caller nothing and
  because dropping a hypothesis from a leaf is a signature change; a prover may
  ignore it.

**NOT VACUOUS.**  `t` ranges over the points of `T`, which is nonempty whenever
`T` is, and the conclusion is an honest local triviality — the trivial witness
`U = ⊤` is *not* available, since `sectionIdeal σ ≅ 𝒪_Y` globally would say the
divisor `[σ]` is trivial. -/
theorem exists_trivialization_sectionIdeal_at_section {Y T : Scheme.{u}} (strY : Y ⟶ T)
    (_hproper : IsProper strY) (_hsmooth : SmoothOfRelativeDimension 1 strY)
    {σ : T ⟶ Y} (_hσ : σ ≫ strY = 𝟙 T) (t : T) :
    ∃ U : Y.Opens, σ.base t ∈ U ∧
      Nonempty ((sectionIdeal σ).restrict U.ι ≅ modUnit (U : Scheme.{u})) := sorry


/-! #### THE COMPARISON MAP `φ^*𝒪(−σ) ⟶ 𝒪(−σ')` IS CONSTRUCTED, NOT MERELY
ASSERTED TO EXIST

(2026-07-31.)  `nonempty_modPullback_sectionIdeal_of_isPullback` used to be a
bare `Nonempty (… ≅ …)` leaf.  Everything below `isIso_modPullbackSectionIdealMap`
is now PROVEN: the canonical map is written down (`modPullbackSectionIdealMap`),
the factorisation through the kernel that defines `sectionIdeal σ'` is checked,
and the leaf that remains says that ONE NAMED MAP is an isomorphism.  That is
strictly stronger than the old statement and it is what every route needs
first, since no route can compare two ideal sheaves without a comparison map.

**The construction spends `_hcompat` and nothing else.**  `_hsq`, `_hσ`, `_hσ'`,
`_hproper`, `_hsmooth` are all still open credit, spent only in the remaining
leaf. -/

/-- **A NATURAL ISOMORPHISM TRANSPORTS "THIS FUNCTOR KILLS THIS MORPHISM"**
(PROVEN) — if `F ≅ G` and `G.map u = 0` then `F.map u = 0`.

Pure naturality: `F.map u = e.hom.app A ≫ G.map u ≫ e.inv.app B`.  Stated
because the pullback pseudofunctor identifies `σ'^* ∘ φ^*` with `h^* ∘ σ^*` only
up to a natural isomorphism, and the vanishing has to cross it. -/
theorem map_eq_zero_of_natIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {A B : C} (u : A ⟶ B)
    (hu : G.map u = 0) : F.map u = 0 := by
  have hn := e.hom.naturality u
  calc F.map u = F.map u ≫ e.hom.app B ≫ e.inv.app B := by
        rw [e.hom_inv_id_app, Category.comp_id]
    _ = (F.map u ≫ e.hom.app B) ≫ e.inv.app B := by rw [Category.assoc]
    _ = (e.hom.app A ≫ G.map u) ≫ e.inv.app B := by rw [hn]
    _ = 0 := by rw [hu, comp_zero, zero_comp]

/-- **`σ^*` KILLS THE INCLUSION `𝒪(−σ) ↪ 𝒪_Z`** (PROVEN) — `σ^*(I_σ) ⟶ σ^*𝒪_Z`
is the zero map.

This is the scheme-theoretic content of "`σ` factors through the closed
subscheme `V(I_σ)`", i.e. `I_σ · 𝒪_T = 0`, in the only form this pin can state
it: there is no closed-subscheme-of-an-ideal-sheaf construction here, only the
kernel that `sectionIdeal` is defined to be.

**The proof is one triangle identity, and it uses NOTHING about `σ`.**  Write
`F = σ^*`, `G = σ_*`, `η = adj.unit.app 𝒪_Z`.  Then `F.map η` is a SPLIT MONO —
its retraction is `adj.counit.app (F.obj 𝒪_Z)`, and `F.map η ≫ counit = 𝟙` is
`Adjunction.left_triangle_components`.  So it is a mono, and
`F.map (kernel.ι η) ≫ F.map η = F.map (kernel.ι η ≫ η) = F.map 0 = 0` cancels
to `F.map (kernel.ι η) = 0`.  `Scheme.Modules.pullback` is `Additive` at this
pin (mathlib, `AlgebraicGeometry/Modules/Sheaf.lean`), which is what makes
`Functor.map_zero` available. -/
theorem pullback_map_sectionIdeal_ι_eq_zero {Z T : Scheme.{u}} (σ : T ⟶ Z) :
    (Scheme.Modules.pullback σ).map
        (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Z)))
      = 0 := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction σ with hadj
  set η := adj.unit.app (modUnit Z) with hηdef
  haveI : IsSplitMono ((Scheme.Modules.pullback σ).map η) :=
    ⟨⟨adj.counit.app ((Scheme.Modules.pullback σ).obj (modUnit Z)),
      adj.left_triangle_components _⟩⟩
  refine zero_of_comp_mono ((Scheme.Modules.pullback σ).map η) ?_
  rw [← Functor.map_comp, kernel.condition, Functor.map_zero]

/-- **`σ'^* φ^*` KILLS THE INCLUSION `𝒪(−σ) ↪ 𝒪_Y`** (PROVEN) — the previous
lemma transported across the square.

`σ' ≫ φ = h ≫ σ` (`hcompat`), so `σ'^* ∘ φ^* ≅ (σ' ≫ φ)^* = (h ≫ σ)^*
≅ h^* ∘ σ^*` by `Scheme.Modules.pullbackComp` twice and
`Scheme.Modules.pullbackCongr` in between; the right-hand functor kills the
inclusion because `σ^*` does and `h^*` is additive.  `map_eq_zero_of_natIso`
carries the vanishing back.

**Only `hcompat` is used.**  In particular the square need not be cartesian for
this; being cartesian is what makes the resulting map an *isomorphism*, not what
makes it exist. -/
theorem pullback_pullback_map_sectionIdeal_ι_eq_zero {Y T Y' T' : Scheme.{u}}
    {φ : Y' ⟶ Y} {h : T' ⟶ T} {σ : T ⟶ Y} {σ' : T' ⟶ Y'} (hcompat : σ' ≫ φ = h ≫ σ) :
    (Scheme.Modules.pullback σ').map ((Scheme.Modules.pullback φ).map
        (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Y))))
      = 0 := by
  set ι := kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Y))
    with hι
  have hG : (Scheme.Modules.pullback σ ⋙ Scheme.Modules.pullback h).map ι = 0 := by
    show (Scheme.Modules.pullback h).map ((Scheme.Modules.pullback σ).map ι) = 0
    rw [hι, pullback_map_sectionIdeal_ι_eq_zero, Functor.map_zero]
  have e : (Scheme.Modules.pullback φ ⋙ Scheme.Modules.pullback σ') ≅
      (Scheme.Modules.pullback σ ⋙ Scheme.Modules.pullback h) :=
    Scheme.Modules.pullbackComp σ' φ ≪≫ Scheme.Modules.pullbackCongr hcompat ≪≫
      (Scheme.Modules.pullbackComp h σ).symm
  exact map_eq_zero_of_natIso e ι hG

/-- **THE CANONICAL COMPARISON MAP `φ^*𝒪(−σ) ⟶ 𝒪(−σ')`** (PROVEN — this is a
construction, and it is total: it needs only `σ' ≫ φ = h ≫ σ`).

`φ^*` applied to `I_σ ↪ 𝒪_Y`, followed by `modPullbackUnitIso φ : φ^*𝒪_Y ≅
𝒪_{Y'}`, is a map `φ^*I_σ ⟶ 𝒪_{Y'}`.  It lands inside `I_{σ'} = ker η_{σ'}`
because its transpose across `σ'^* ⊣ σ'_*` is `σ'^*φ^*(kernel.ι η_σ) = 0`
(the lemma above) — concretely, unit naturality turns `u ≫ η_{σ'}` into
`η_{σ'} ≫ σ'_*(σ'^*u)` and the second factor is zero.  `kernel.lift` then
supplies the map.

**Why this is the right object to name.**  Both `φ^*𝒪(−σ)` and `𝒪(−σ')` are
subsheaves-up-to-`Tor` of `𝒪_{Y'}`, and every proof of the parent theorem — the
`Tor` route, the split-exactness route below, a local-coordinate route — proves
that THIS map is invertible.  A bare `Nonempty (… ≅ …)` hides that and would let
a prover chase an unrelated isomorphism. -/
noncomputable def modPullbackSectionIdealMap {Y T Y' T' : Scheme.{u}}
    {φ : Y' ⟶ Y} {h : T' ⟶ T} {σ : T ⟶ Y} {σ' : T' ⟶ Y'} (hcompat : σ' ≫ φ = h ≫ σ) :
    modPullback φ (sectionIdeal σ) ⟶ sectionIdeal σ' :=
  kernel.lift ((Scheme.Modules.pullbackPushforwardAdjunction σ').unit.app (modUnit Y'))
    ((Scheme.Modules.pullback φ).map
        (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Y)))
      ≫ (modPullbackUnitIso φ).hom)
    (by
      set u := (Scheme.Modules.pullback φ).map
          (kernel.ι ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app (modUnit Y)))
        ≫ (modPullbackUnitIso φ).hom with hu
      have hz : (Scheme.Modules.pullback σ').map u = 0 := by
        rw [hu, Functor.map_comp, pullback_pullback_map_sectionIdeal_ι_eq_zero hcompat, zero_comp]
      have hcomp : (Scheme.Modules.pullback σ' ⋙ Scheme.Modules.pushforward σ').map u = 0 := by
        show (Scheme.Modules.pushforward σ').map ((Scheme.Modules.pullback σ').map u) = 0
        rw [hz, Functor.map_zero]
      have hnat := (Scheme.Modules.pullbackPushforwardAdjunction σ').unit.naturality u
      refine hnat.trans ?_
      rw [hcomp]
      exact comp_zero)

/-- **THE COMPARISON MAP IS AN ISOMORPHISM** (sorry leaf, cut 2026-07-31 out of
`nonempty_modPullback_sectionIdeal_of_isPullback`, which is now PROVEN over it
and is its only consumer) — Stacks 062Y / 0631, EGA IV 21.15: a relative
effective Cartier divisor pulls back to one, and its ideal sheaf pulls back to
the ideal sheaf.

**THE ROUTE, AND A CORRECTION TO THE ONE THIS LEAF INHERITED.**  The audit this
slot used to carry said the content is `Tor`-vanishing, supplied by flatness of
`𝒪_{D_σ}` over `𝒪_T`.  That is true but it is not the cheapest true thing, and
naming flatness hides where `_hσ` is actually spent.  In the affine model —
`Y = Spec B`, `T = Spec A`, `strY^# : A ⟶ B`, `σ^# : B ⟶ A` an `A`-algebra
retraction of it (that IS `_hσ`), `I = ker σ^#`, `T' = Spec A'`,
`B' = B ⊗_A A'` (that IS `_hsq`), `σ'^# = σ^# ⊗ 𝟙` (that IS `_hσ'` + `_hcompat`)
— the defining sequence

    0 ⟶ I ⟶ B ⟶ A ⟶ 0

is a sequence of `A`-modules that is **SPLIT**, the splitting being `strY^#`
itself.  A split short exact sequence is a biproduct decomposition, so EVERY
additive functor preserves it; no flatness theorem and no `Tor` computation is
needed.  Applying `− ⊗_A A'`:

    0 ⟶ I ⊗_A A' ⟶ B' ⟶ A' ⟶ 0

is still split exact, so `I ⊗_A A' = ker σ'^# = I_{σ'}`.  And
`I ⊗_B B' = I ⊗_B (B ⊗_A A') = I ⊗_A A'`, which is `φ^* I_σ`.  The two
identifications are compatible with the inclusions into `B'`, so the composite
is exactly `modPullbackSectionIdealMap`, and it is an isomorphism.

**So the ONE genuinely missing formal input is:** for a cartesian square,
`φ^*` on `Y.Modules`, read through the `strY^{-1}𝒪_T`-module structure, IS the
base change `− ⊗_{𝒪_T} 𝒪_{T'}`.  Everything else in the paragraph above is
formal (split monos and split epis are preserved by additive functors, and
`Scheme.Modules.pullback` is `Additive` at this pin).  That input is flat base
change and it does not exist here; a prover has to build it, or to work locally
with `isIso_of_locally_isIso` above and a local equation for `I_σ` obtained from
`isInvertibleSheaf_sectionIdeal_of_isSection`.

**WHY `_hσ` IS LOAD-BEARING, with the witness that was recorded on this leaf.**
Drop it and the statement is FALSE: take `T = Spec k[s]`, `Y = Spec k[s,t]`,
`D = V(st)`.  Its ideal is invertible (`st` is a nonzerodivisor) but `D` is not
flat over `T` (`s · t = 0` with `t ≠ 0`), and base change along `s = 0` gives
`φ^*I ≅ 𝒪` of rank one against an ideal of the preimage equal to `0`.  In the
split language: without a retraction there is no `A`-splitting of
`0 ⟶ I ⟶ B ⟶ B/I ⟶ 0`, and the sequence does not survive `− ⊗_A A'`.
The older audit credited this flatness to `isInvertibleSheaf_sectionIdeal`; that
is WRONG — invertibility of the ideal says nothing about flatness over `T`, as
the same witness shows.

**FALSITY AUDIT — the tempting weaker hypothesis is REFUTED.**  It is natural to
ask only that the SECTION square be cartesian, i.e. `T' = T ×_Y Y'`, which is
`isPullback_relSection_curveBaseChangeMap` above and looks like the right
statement ("`D'` is the preimage of `D`").  **That version is FALSE**, with an
explicit witness:

    Y = 𝔸¹_k = Spec k[t],  T = Spec k,  strY the structure map,  σ = the origin;
    Y' = Spec k[t]/(t),    T' = Spec k, strY' = 𝟙,  h = 𝟙,  σ' = 𝟙,  φ the closed
    immersion of the origin.

Then `σ' ≫ φ = φ = h ≫ σ`, and `T ×_Y Y' = Spec (k ⊗_{k[t]} k[t]/(t)) = Spec k
= T'`, so the section square IS cartesian; `sectionIdeal σ = (t)` is invertible
and `σ` is a closed immersion, so every other hypothesis holds.  But
`sectionIdeal σ' = ker(𝒪_{Y'} ⟶ 𝟙_*𝒪_{T'}) = 0` while `φ^*(t) ≅ 𝒪_{Y'} ≠ 0`, so
no isomorphism exists.  What kills the witness is exactly `_hsq`:
`Y ×_T T' = 𝔸¹_k`, not `Spec k[t]/(t)`.  So the load-bearing hypothesis is that
`Y'` is the base change of `Y` **over `T`**, not that `D'` is the preimage of
`D`.

**THE OTHER HYPOTHESES, re-audited against the composite statement** (the
previous audit is VOID rather than inherited — this statement is new, and its
binder names have changed: the old `_hbase` is `_hsq`, the old `_hcomm` is
`hcompat`, and the old `_hclosed`/`_hinv` are gone).

* `_hσ'` is NOT derivable and is load-bearing: `_hcompat` together with `_hsq`
  only gives `(σ' ≫ strY') ≫ h = h`, so without `_hσ'` the statement is false
  for any `σ'` that is not the base-changed section.
* `_hproper` and `_hsmooth` are **not used by the affine argument above at
  all** — they are kept because the call site
  (`nonempty_modPullback_sectionIdeal`) holds them for free, because dropping a
  hypothesis is a signature change, and because a globalising argument that
  reduces to the affine case is likely to want `σ` to be a closed immersion,
  which is one line from `_hproper` (see `isClosedImmersion_relSection`, whose
  proof generalises verbatim to any section of a proper morphism).  A prover may
  ignore both.
* `_hinv`, which the 2026-07-30 statement carried, has been dropped: it is
  recoverable from `_hproper`, `_hsmooth` and `_hσ` through
  `isInvertibleSheaf_sectionIdeal_of_isSection` below, so demanding it added
  nothing.

**NOT VACUOUS.**  Instantiated immediately below, and already at `h = 𝟙 T`,
where `φ` is a nontrivial automorphism of the pullback rather than the
identity. -/
theorem isIso_modPullbackSectionIdealMap {Y T Y' T' : Scheme.{u}}
    (strY : Y ⟶ T) (strY' : Y' ⟶ T') (φ : Y' ⟶ Y) (h : T' ⟶ T)
    (_hsq : IsPullback φ strY' strY h)
    (_hproper : IsProper strY) (_hsmooth : SmoothOfRelativeDimension 1 strY)
    {σ : T ⟶ Y} (_hσ : σ ≫ strY = 𝟙 T) {σ' : T' ⟶ Y'} (_hσ' : σ' ≫ strY' = 𝟙 T')
    (hcompat : σ' ≫ φ = h ≫ σ) :
    IsIso (modPullbackSectionIdealMap hcompat) := sorry

/-- **THE IDEAL OF A SECTION COMMUTES WITH BASE CHANGE OF THE AMBIENT SCHEME**
(PROVEN 2026-07-31 over `isIso_modPullbackSectionIdealMap`; a sorry leaf from
2026-07-30 to 2026-07-31) — stated for a bare section of a bare morphism because
nothing in the argument knows about curves.

Set-up: `strY : Y ⟶ T` with a section `σ`, and `Y' = Y ×_T T'` with `φ` and
`strY'` the two projections, so that `σ' : T' ⟶ Y'` is *forced* to be the
base-changed section (`_hσ'` and `_hcompat` pin it uniquely, by the universal
property of the pullback).  The claim is `φ^* 𝒪(−σ) ≅ 𝒪(−σ')`.

The isomorphism is not an anonymous one: it is `modPullbackSectionIdealMap`,
constructed above, and the whole content is that it is invertible.  See its
`IsIso` leaf for the route and for the hypothesis audit. -/
theorem nonempty_modPullback_sectionIdeal_of_isPullback {Y T Y' T' : Scheme.{u}}
    (strY : Y ⟶ T) (strY' : Y' ⟶ T') (φ : Y' ⟶ Y) (h : T' ⟶ T)
    (_hsq : IsPullback φ strY' strY h)
    (_hproper : IsProper strY) (_hsmooth : SmoothOfRelativeDimension 1 strY)
    {σ : T ⟶ Y} (_hσ : σ ≫ strY = 𝟙 T) {σ' : T' ⟶ Y'} (_hσ' : σ' ≫ strY' = 𝟙 T')
    (_hcompat : σ' ≫ φ = h ≫ σ) :
    Nonempty (modPullback φ (sectionIdeal σ) ≅ sectionIdeal σ') :=
  haveI := isIso_modPullbackSectionIdealMap strY strY' φ h _hsq _hproper _hsmooth _hσ _hσ'
    _hcompat
  ⟨asIso (modPullbackSectionIdealMap _hcompat)⟩

/-- **THE SECTIONS MATCH** (PROVEN 2026-07-31) — `σ' ≫ φ = h ≫ σ` in the
notation of `nonempty_modPullback_sectionIdeal` below: transporting a relative
point along `h` and then taking its section is the same as taking its section
and restricting.

Both sides have first component `h ≫ x.1` and second component `h`, so
`pullback.hom_ext` reduces it to `pullback.lift_fst` / `pullback.lift_snd`.
This is the identity the audit on that leaf singled out as the one a prover
must check by hand. -/
theorem relSection_comp_curveBaseChangeMap {X S T T' : Scheme.{u}} {strX : X ⟶ S}
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') (x : RelPoint strX g) :
    relSection (RelPoint.pre h hg x) ≫ curveBaseChangeMap strX h hg = h ≫ relSection x := by
  apply pullback.hom_ext <;>
    simp [relSection, curveBaseChangeMap, RelPoint.pre, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- **A RELATIVE POINT IS A SECTION OF THE BASE-CHANGED CURVE** (PROVEN
2026-07-31) — `relSection x ≫ curveBaseChangeProj strX g = 𝟙 T`.

This is `pullback.lift_snd`, and it is the hypothesis that carries FLATNESS in
the leaf below: the divisor `D_x` is the image of a SECTION, so `D_x ⟶ T` is an
isomorphism, hence flat, which is exactly the condition under which an effective
Cartier divisor commutes with base change. -/
theorem relSection_comp_curveBaseChangeProj {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}
    (x : RelPoint strX g) : relSection x ≫ curveBaseChangeProj strX g = 𝟙 T := by
  simp [relSection, curveBaseChangeProj, pullback.lift_snd]

/-- **THE BASE-CHANGE SQUARE OF THE CURVE IS CARTESIAN** (PROVEN 2026-07-31) —
`X ×_S T' = (X ×_S T) ×_T T'`, in the `IsPullback` form, for the concrete
`curveBaseChangeMap`.

Pullback pasting: the outer rectangle `X ×_S T' ⟶ X`, `⟶ T' ⟶ T ⟶ S` and the
right-hand square `X ×_S T ⟶ X`, `⟶ T ⟶ S` are both cartesian, so
`IsPullback.of_right` gives the left-hand square.  The two side conditions are
`pullback.lift_fst` and `pullback.lift_snd` on `curveBaseChangeMap`.

The audit on `nonempty_modPullback_sectionIdeal` asserted this in prose ("and
`X ×_S T' = (X ×_S T) ×_T T'`"); it is proven here so that the leaf can be
restated over an abstract cartesian square. -/
theorem isPullback_curveBaseChangeMap {X S T T' : Scheme.{u}} (strX : X ⟶ S)
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') :
    IsPullback (curveBaseChangeMap strX h hg) (curveBaseChangeProj strX g')
      (curveBaseChangeProj strX g) h := by
  subst hg
  refine IsPullback.of_right (h₁₂ := pullback.fst strX g) ?_ ?_
    (IsPullback.of_hasPullback strX g)
  · have hfst : curveBaseChangeMap strX h rfl ≫ pullback.fst strX g
        = pullback.fst strX (h ≫ g) := by
      simp only [curveBaseChangeMap, pullback.lift_fst]
    rw [hfst]
    exact IsPullback.of_hasPullback strX (h ≫ g)
  · simp only [curveBaseChangeMap, curveBaseChangeProj, pullback.lift_snd]

/-- **The two sections are compatible across the base change** (PROVEN):
`σ' ≫ φ = h ≫ σ`.

This is the identity the old docstring of `nonempty_modPullback_sectionIdeal`
said "is the only part a prover has to check by hand".  It is checked here, by
`pullback.hom_ext`: the two components are `pullback.lift_fst` (both sides have
first component `h ≫ x.1`, definitionally, since `(RelPoint.pre h hg x).1` IS
`h ≫ x.1`) and `pullback.lift_snd` (both have second component `h`). -/
theorem relSection_pre_comp_curveBaseChangeMap {X S T T' : Scheme.{u}} {strX : X ⟶ S}
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') (x : RelPoint strX g) :
    relSection (RelPoint.pre h hg x) ≫ curveBaseChangeMap strX h hg = h ≫ relSection x := by
  apply pullback.hom_ext
  · simp only [relSection, curveBaseChangeMap, Category.assoc, pullback.lift_fst]
    rfl
  · simp only [relSection, curveBaseChangeMap, Category.assoc, pullback.lift_snd,
      Category.comp_id]
    rw [← Category.assoc, pullback.lift_snd, Category.id_comp]

/-- **A SECTION OF A SMOOTH RELATIVE CURVE IS AN EFFECTIVE CARTIER DIVISOR**
(PROVEN 2026-07-31 over `exists_trivialization_sectionIdeal_at_section` and
`sectionIdeal_restrict_iso_unit_of_notMem_range`; a sorry leaf for a few hours on
2026-07-31, and the audit below is the one written while it was one — every word
still applies, now to the on-image leaf it is proven over) — its ideal sheaf
`𝒪(−σ)` is invertible.

Stacks 0C4S / EGA IV 17.12.1 verbatim, and now stated about the morphism the
citation is about: `strY : Y ⟶ T` proper and smooth of relative dimension `1`,
`σ` a section of it.  Then `σ` is a closed immersion whose ideal is locally
generated by one element that is a nonzerodivisor on every fibre — the local
coordinate of the smooth curve at `σ`.  No base change appears in the statement.

**This is one of the exactly TWO genuinely new geometric obligations of
`exists_abelJacobiPoint`, and it is where the smoothness hypothesis of that leaf
is spent.**  Nothing in the pin says it: there is no divisor theory at `a3364fa`
(no `𝒪(D)`, no Cartier divisors), which is why `sectionIdeal` is defined as a
kernel in the first place.  So it has to be proven from that definition —
`sectionIdeal σ = ker (𝒪_Y ⟶ σ_*𝒪_T)` — by trivializing on a neighbourhood of
each point of the image and using `strY` smooth of relative dimension `1` there;
off the image the kernel is all of `𝒪_Y` and the statement is the (proven)
`isInvertibleSheaf_modUnit` locally.

**FAITHFULNESS AUDIT (fresh — this is a NEW statement, so the previous audit is
VOID rather than inherited, per CLAUDE.md's rule.  It survives essentially
verbatim, and the reason is worth recording: both of its counterexamples were
already stated as curves over a base rather than as base changes, so they were
always really about THIS statement.  Restating has made the audit apply
directly instead of through a transport.)**

*Both hypotheses are load-bearing, neither is decoration.*

* Drop `_hsmooth` and it is FALSE: for the nodal cubic `Y : y² = x³ + x²` over a
  field, a section through the node has ideal sheaf which is not invertible at
  the node — the local ring is not regular there, and `𝔪` needs two generators.
  The relative-dimension-`1` part is equally load-bearing: at relative dimension
  `2` a section is a regular immersion of CODIMENSION `2`, and its ideal sheaf
  has rank `2` at the section, so it is not invertible either (`𝔸²_T` with the
  zero section is the smallest witness).
* Drop `_hproper` and it is FALSE: properness is used only through
  SEPARATEDNESS, but it is used.  A section of a non-separated morphism is an
  immersion that need not be closed, and then `ker (𝒪_Y ⟶ σ_*𝒪_T)` is the ideal
  of functions vanishing on a non-closed subset.  Take `Y` the affine line with
  doubled origin over `T = Spec k`, smooth of relative dimension `1`, and `σ`
  one of the two origins: the kernel is the ideal of a point whose closure meets
  the other origin, and it is not invertible at that second point.
* Drop `_hσ` — that `σ` is a SECTION — and it is FALSE for a trivial reason: an
  arbitrary `σ : T ⟶ Y` need not be an immersion at all, and `ker (𝒪_Y ⟶ σ_*𝒪_T)`
  is then not the ideal of a divisor.  Take `T = Y` and `σ = 𝟙 Y` with `Y` a
  curve of positive genus over `T' = Spec k`: the kernel is `0`, which is not
  invertible.  This hypothesis is NEW here — in the old statement it was implicit
  in `σ = relSection x`, which is a section by construction
  (`relSection_comp_curveBaseChangeProj`), and making it explicit is what lets
  the statement mention no base change.

**NOT VACUOUS.**  `Y = ℙ¹_T` with the zero section satisfies every hypothesis,
and `𝒪(−0)` is invertible.  The conclusion is not vacuously true by an empty
quantifier either — `IsInvertibleSheaf` is a `∀` over the points of `Y`, which
is nonempty as soon as `T` is. -/
theorem isInvertibleSheaf_sectionIdeal_of_isSection {Y T : Scheme.{u}} (strY : Y ⟶ T)
    (_hproper : IsProper strY) (_hsmooth : SmoothOfRelativeDimension 1 strY)
    {σ : T ⟶ Y} (_hσ : σ ≫ strY = 𝟙 T) :
    IsInvertibleSheaf (sectionIdeal σ) := by
  intro z
  by_cases hz : z ∈ Set.range σ.base
  · obtain ⟨t, rfl⟩ := hz
    exact exists_trivialization_sectionIdeal_at_section strY _hproper _hsmooth _hσ t
  · exact sectionIdeal_restrict_iso_unit_of_notMem_range σ
      (isClosedImmersion_of_isSection strY _hproper _hσ) z hz

/-- **A SECTION OF A SMOOTH RELATIVE CURVE IS AN EFFECTIVE CARTIER DIVISOR**
(PROVEN — three lines over `isInvertibleSheaf_sectionIdeal_of_isSection` just
above, which carries the whole argument; formerly a bare sorry leaf, and the
audit below is the one written while it was one — every word of it still applies,
now to the on-image leaf `exists_trivialization_sectionIdeal_at_section` that it
is ultimately proven over) — its ideal sheaf `𝒪(−σ)` is invertible.

Stacks 0C4S / EGA IV 17.12.1: for `f : Y ⟶ T` smooth of relative dimension `1`
and separated, a section `σ` is a closed immersion whose ideal is locally
generated by one element that is a nonzerodivisor on every fibre — the local
coordinate of the smooth curve at `σ`.  Here `Y = X ×_S T`, which is proper and
smooth of relative dimension `1` over `T` because both properties are stable
under base change, and `σ = relSection x`.

**This is one of the exactly TWO genuinely new geometric obligations of
`exists_abelJacobiPoint`, and it is where the smoothness hypothesis of that leaf
is spent.**  Nothing in the pin says it: there is no divisor theory at `a3364fa`
(no `𝒪(D)`, no Cartier divisors), which is why `sectionIdeal` is defined as a
kernel in the first place.  So it has to be proven from that definition —
`sectionIdeal σ = ker (𝒪_Y ⟶ σ_*𝒪_T)` — by trivializing on a neighbourhood of
each point of the image and using `f` smooth of relative dimension `1` there;
off the image the kernel is all of `𝒪_Y` and the statement is the (proven)
`isInvertibleSheaf_modUnit` locally.

**FAITHFULNESS.  Both hypotheses are load-bearing, neither is decoration.**

* Drop `_hsmooth` and it is FALSE: for the nodal cubic `Y : y² = x³ + x²` over a
  field, a section through the node has ideal sheaf which is not invertible at
  the node — the local ring is not regular there, and `𝔪` needs two generators.
  The relative-dimension-`1` part is equally load-bearing: at relative dimension
  `2` a section is a regular immersion of CODIMENSION `2`, and its ideal sheaf
  has rank `2` at the section, so it is not invertible either (`𝔸²_T` with the
  zero section is the smallest witness).
* Drop `_hproper` and it is FALSE: properness is used only through
  SEPARATEDNESS, but it is used.  A section of a non-separated morphism is an
  immersion that need not be closed, and then `ker (𝒪_Y ⟶ σ_*𝒪_T)` is the ideal
  of functions vanishing on a non-closed subset.  Take `Y` the affine line with
  doubled origin over `T = Spec k`, smooth of relative dimension `1`, and `σ`
  one of the two origins: the kernel is the ideal of a point whose closure meets
  the other origin, and it is not invertible at that second point.

**NOT VACUOUS.**  Satisfied whenever `X ⟶ S` is a smooth proper relative curve
with a section, which is the situation the whole module is about; `X = S`,
`strX = 𝟙 S` is excluded because that is relative dimension `0`, and the
statement is not vacuously true by an empty quantifier — `IsInvertibleSheaf` is
a `∀` over the points of `X ×_S T`, which is nonempty as soon as `T` is.

**THE CUT (2026-07-30).**  The `∀ z` splits on whether `z` lies in the image of
the section — a decidable-by-`by_cases` disjunction, not a geometric one — and
the two branches share nothing.  Off the image the answer is
`sectionIdeal σ|_U = 𝒪_U` on the whole complement, proven above from the
definition of `sectionIdeal` as a kernel; on the image it is the local
coordinate, which is the leaf.  Properness is spent ONLY in the off-image
branch, through `isClosedImmersion_relSection`; smoothness ONLY in the
on-image one. -/
theorem isInvertibleSheaf_sectionIdeal {X S T : Scheme.{u}} {strX : X ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    {g : T ⟶ S} (x : RelPoint strX g) :
    IsInvertibleSheaf (sectionIdeal (relSection x)) :=
  isInvertibleSheaf_sectionIdeal_of_isSection (curveBaseChangeProj strX g)
    (isProper_curveBaseChangeProj strX g _hproper)
    (smoothOfRelativeDimension_curveBaseChangeProj strX g _hsmooth)
    (relSection_comp_curveBaseChangeProj x)

/-- **`T' = T ×_{X_T} X_{T'}`** (PROVEN) — the section square is cartesian too,
which is the form in which the classical statement is usually quoted ("`D_{x'}`
is the scheme-theoretic preimage of `D_x`").

It is a CONSEQUENCE of the two lemmas above rather than an extra input: paste
the section square onto the projection square, note that both composites
`σ' ≫ π_{g'}` and `σ ≫ π_g` are identities, so the outer rectangle is the
trivially-cartesian square `𝟙, h, h, 𝟙`, and peel the right square off again.

**It is recorded but deliberately NOT used as the hypothesis of the leaf
below** — see that leaf's falsity audit, where this square alone is refuted. -/
theorem isPullback_relSection_curveBaseChangeMap {X S T T' : Scheme.{u}} {strX : X ⟶ S}
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') (x : RelPoint strX g) :
    IsPullback (relSection (RelPoint.pre h hg x)) h (curveBaseChangeMap strX h hg)
      (relSection x) := by
  refine IsPullback.of_right (h₁₂ := curveBaseChangeProj strX g') ?_
    (relSection_comp_curveBaseChangeMap h hg x) (isPullback_curveBaseChangeMap strX h hg).flip
  rw [relSection_comp_proj, relSection_comp_proj]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **`𝒪(−σ)` COMMUTES WITH BASE CHANGE** (PROVEN 2026-07-31 over
`nonempty_modPullback_sectionIdeal_of_isPullback` and
`isInvertibleSheaf_sectionIdeal`; a sorry leaf from 2026-07-29 to 2026-07-31) —
`φ^* 𝒪(−x) ≅ 𝒪(−x_{T'})` for `φ = curveBaseChangeMap strX h hg`.

The second of the two genuinely new geometric obligations of
`exists_abelJacobiPoint`, and the only one `aj_pre` needs beyond the tensor
calculus.

**What the 2026-07-29 audit said, and what happened to each part.**

*"The square is cartesian and the sections match … the only part a prover has to
check by hand"* — both discharged, as `isPullback_curveBaseChangeMap` and
`relSection_comp_curveBaseChangeMap` above.  The prediction was exactly right
about the proofs: `pullback.hom_ext` plus `lift_fst`/`lift_snd` for the sections,
pullback pasting for the square.

*"`φ^*` is right exact, not left exact, so it does not commute with a kernel for
free … the statement is exactly that `D_x` is FLAT over `T`"* — right about the
mechanism, but it attributed the flatness to `isInvertibleSheaf_sectionIdeal`
("an effective relative Cartier divisor is flat over the base").  That is the
wrong source, and getting it right is what allowed the cut: invertibility of the
ideal is Cartier-ness, which says nothing about flatness over `T` — the witness
`V(st) ⊂ 𝔸²_{k[s]}` recorded on the leaf above is Cartier and not flat.  What
supplies flatness here is that `x` is a *section*: `D_x ≅ T` over `T`.  So the
two inputs are INDEPENDENT — invertibility from `isInvertibleSheaf_sectionIdeal`,
flatness from `relSection_comp_curveBaseChangeProj` — and only the first is a
geometric leaf.

**FAITHFULNESS.**  `_hproper` and `_hsmooth` are spent exactly once, on
`isInvertibleSheaf_sectionIdeal`; drop either and `𝒪(−x)` need not be
invertible, hence need not be locally principal, and the pullback map
`φ^*𝒪(−x) ⟶ 𝒪(−x_{T'})` has a kernel.  Concretely, over the nodal cubic with
`T' ⟶ T` the inclusion of the node's residue field, `φ^*` of the ideal has rank
`2` while `𝒪(−x_{T'})` has rank `1`, so no isomorphism exists.

**NOT VACUOUS, and not a relocation.**  `h = 𝟙 T` gives a nontrivial instance
(`φ` is then an automorphism of the pullback, not the identity, since
`curveBaseChangeMap` is defined by `pullback.lift`), and the general case is
consumed once in `aj_pre` at each of `x` and the base point `o`. -/
theorem nonempty_modPullback_sectionIdeal {X S T T' : Scheme.{u}} {strX : X ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    {g : T ⟶ S} {g' : T' ⟶ S} (h : T' ⟶ T) (hg : h ≫ g = g') (x : RelPoint strX g) :
    Nonempty (modPullback (curveBaseChangeMap strX h hg) (sectionIdeal (relSection x))
      ≅ sectionIdeal (relSection (RelPoint.pre h hg x))) :=
  nonempty_modPullback_sectionIdeal_of_isPullback (curveBaseChangeProj strX g)
    (curveBaseChangeProj strX g') (curveBaseChangeMap strX h hg) h
    (isPullback_curveBaseChangeMap strX h hg)
    (isProper_curveBaseChangeProj strX g _hproper)
    (smoothOfRelativeDimension_curveBaseChangeProj strX g _hsmooth)
    (relSection_comp_curveBaseChangeProj x)
    (relSection_comp_curveBaseChangeProj (RelPoint.pre h hg x))
    (relSection_pre_comp_curveBaseChangeMap h hg x)

/-- **THE ABEL–JACOBI MAP INTO `Pic`** (PROVEN 2026-07-29 over the two geometric
leaves `isInvertibleSheaf_sectionIdeal` and `nonempty_modPullback_sectionIdeal`,
and the tensor calculus above) — the
`𝒪(D)` dictionary for section divisors on a relative curve, which is BLR
9.4/4's first input and the only place `sectionIdeal` is consumed.

Classically: for `x` a `T`-point of the curve, `𝒪(x − o)` is an
invertible sheaf on `X_T`, so `surj` classifies it, and the resulting
point of `Pic` is natural in `T` and sends `o` to the origin.

**ROUTE — carried out, and every step of the pricing below held.**  The
construction at one `(T, g)` is `M := 𝒪(−o_T) ⊗ 𝒪(−x)⁻¹`, then `hP.surj M`, and
`aj` is `choose` over `(T, g, x)`.  What follows is what it cost, with the two
things that were NOT foreseen marked.

*The two genuinely NEW geometric obligations are now the two named leaves
immediately above*, `isInvertibleSheaf_sectionIdeal` (consumed at `Ix := 𝒪(−x)`
and at `Io := 𝒪(−o_T)`) and `nonempty_modPullback_sectionIdeal` (consumed only
by `aj_pre`, at `x` and at `o_T`).  They carry ALL the algebraic geometry of
this leaf; everything else below is tensor calculus.

*The tensor bookkeeping.*  `aj_spec` is as priced: `hP.sheaf (aj x) ∼ Io ⊗ Jx`
(with `Ix ⊗ Jx ≅ 𝒪` from `exists_modTensor_inv`), tensor on the right by `Ix`,
then `(Io ⊗ Jx) ⊗ Ix ≅ Io ⊗ (Jx ⊗ Ix) ≅ Io ⊗ 𝒪 ≅ Io` — associativity, one
braiding, the right unitor.  The two helpers it named are proven above as
`relPicEquiv_of_iso` and `relPicEquiv_tensor_right`.

*`aj_pre`*, and the audit's diagnosis was exactly right: the blocking piece was
neither geometric obligation but **`IsInvertibleSheaf (modPullback h N)`**, now
PROVEN above as `isInvertibleSheaf_modPullback` over the `morphismRestrict`
chain it predicted, and consumed through `relPicEquiv_modPullback`.

**TWO CORRECTIONS to the route, both found by carrying it out.**

1. *`aj_base` does need more than `hP.inj` applied to `𝒪(o − o) ∼ 𝒪`.*  The
   audit said it "needs none of it".  In fact both `aj_base` and `aj_pre` are
   proven the SAME way — `IsRelPicOf.eq_of_relPicEquiv_tensor` above — and that
   lemma rests on `relPicEquiv_cancel_left`, hence on
   `nonempty_iso_of_modTensorPic_left`, hence on `exists_modTensor_inv` and the
   braiding.  The reason is that the two `Classical.choose`s being compared are
   made at different `(T, g)`, so they can only be identified through the SPEC,
   never directly; `hP.inj` alone gets you as far as `𝒪(x−o) ⊗ 𝒪(−x)`, and the
   `𝒪(−x)` has to be cancelled.
2. *No comparison of chosen inverses is needed.*  A first plan proved `aj_pre`
   by showing `φ^* Jx ≅ J_{x'}` — uniqueness of tensor inverses.  That is true
   but unnecessary: pushing the SPEC through `φ^*` and appealing to uniqueness
   of the solution avoids the chosen inverses entirely, and is why `Jinv` never
   appears outside `hspec`.

One identity that looks like nothing and is not `rfl`:
`RelPoint.pre h hg (relBasePoint o g) = relBasePoint o g'`.  Both sides
are `⟨h ≫ (g ≫ o.1), _⟩` and `⟨(h ≫ g) ≫ o.1, _⟩`; it is `Subtype.ext`
plus `Category.assoc`, and `aj_pre` cannot start without it.  It is proven
above as `relBasePoint_pre`, with its `𝟙 S` companion `relBasePoint_id`, and
the audit was right that `aj_pre` cannot start without it.

**Pinned.**  The `∃` looks under-pinned — an adversary might try to
replace `aj` by any other family of points — but `hP.inj` makes the point
satisfying the first clause UNIQUE, so the clause determines `aj`
pointwise and the other two clauses are then theorems about it rather
than extra freedom.  This is the same argument that makes
`IsRelPicOf.addPoint` well defined, and it is now a theorem rather than a
remark: `IsRelPicOf.eq_of_relPicEquiv_tensor`.

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
        aj S (𝟙 S) o = hP.zeroPoint (𝟙 S) := by
  -- `𝒪(−σ)` is invertible for every section, at every base
  have hI : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      IsInvertibleSheaf (sectionIdeal (relSection x)) :=
    fun T g x => isInvertibleSheaf_sectionIdeal _hproper _hsmooth x
  -- a tensor inverse `Jx` of each `Ix := 𝒪(−x)`
  choose Jinv hJinv hJ using fun (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g) =>
    exists_modTensor_inv (hI T g x)
  -- the Abel–Jacobi point: the class of `𝒪(−o_T) ⊗ 𝒪(−x)⁻¹`, classified by `surj`
  choose aj haj using fun (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g) =>
    hP.surj (T := T) (g := g)
      (modTensor (sectionIdeal (relSection (relBasePoint o g))) (Jinv T g x))
      (isInvertibleSheaf_modTensorPic (hI T g (relBasePoint o g)) (hJinv T g x))
  -- `aj_spec`: `(Io ⊗ Jx) ⊗ Ix ≅ Io ⊗ (Jx ⊗ Ix) ≅ Io ⊗ 𝒪 ≅ Io`
  have hspec : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))) := by
    intro T g x
    refine relPicEquiv_trans strX g
      (relPicEquiv_tensor_right strX g _ (haj T g x)) (relPicEquiv_of_iso strX g ?_)
    refine (nonempty_modTensor_assoc _ (Jinv T g x) (sectionIdeal (relSection x))).some ≪≫ ?_
    refine modTensorMapIso (Iso.refl _) ?_ ≪≫ modTensorUnitRightIso _
    exact modTensorSymmIso (Jinv T g x) (sectionIdeal (relSection x)) ≪≫ (hJ T g x).some
  refine ⟨aj, hspec, ?_, ?_⟩
  · -- `aj_pre`: the pulled-back point solves the spec at `(T', g')`, and the
    -- solution is unique
    intro T' T h g g' hg x
    refine hP.eq_of_relPicEquiv_tensor (hI T' g' (RelPoint.pre h hg x))
      (hspec T' g' (RelPoint.pre h hg x)) ?_
    obtain ⟨bcx⟩ := nonempty_modPullback_sectionIdeal _hproper _hsmooth h hg x
    obtain ⟨bco⟩ := nonempty_modPullback_sectionIdeal _hproper _hsmooth h hg (relBasePoint o g)
    rw [relBasePoint_pre o h hg] at bco
    refine relPicEquiv_trans strX g'
      (relPicEquiv_tensor_right strX g' _ (hP.sheaf_pre h hg (aj T g x))) ?_
    refine relPicEquiv_trans strX g'
      (relPicEquiv_of_iso strX g'
        (modTensorMapIso (Iso.refl _) bcx.symm ≪≫
          (nonempty_modPullback_modTensorPic (curveBaseChangeMap strX h hg)
            (hP.sheaf (aj T g x)) (sectionIdeal (relSection x))).some.symm)) ?_
    exact relPicEquiv_trans strX g'
      (relPicEquiv_modPullback strX h hg (hspec T g x)) (relPicEquiv_of_iso strX g' bco)
  · -- `aj_base`: the origin solves the spec at `(S, 𝟙 S)` for `x = o`
    have hz : RelPicEquiv strX (𝟙 S)
        (modTensor (hP.sheaf (hP.zeroPoint (𝟙 S))) (sectionIdeal (relSection o)))
        (sectionIdeal (relSection (relBasePoint o (𝟙 S)))) := by
      rw [relBasePoint_id o]
      exact relPicEquiv_trans strX (𝟙 S)
        (relPicEquiv_tensor_right strX (𝟙 S) _ (hP.sheaf_zeroPoint (𝟙 S)))
        (relPicEquiv_of_iso strX (𝟙 S) (modTensorUnitLeftIso _))
    exact hP.eq_of_relPicEquiv_tensor (hI S (𝟙 S) o) (hspec S (𝟙 S) o) hz

/-! ### The Abel–Jacobi laws, for an `aj` that arrives as a HYPOTHESIS

`exists_abelJacobiPoint` proves three things about the family it builds — the
spec, naturality (`aj_pre`) and `aj o = 0` (`aj_base`) — and then hides the last
two inside an existential.  A consumer that receives `aj` and its SPEC as
hypotheses, which is how every leaf below the split of `exists_relPicZeroSubgroup`
receives it, therefore holds only the spec and cannot get at the other two.

That is an accident of packaging, not of mathematics: the spec DETERMINES `aj`
pointwise (`IsRelPicOf.eq_of_relPicEquiv_tensor`, the "Pinned." paragraph above),
so any family satisfying it is THE family, and both laws transport to it.  The
three lemmas below say exactly that, and cost nothing beyond one appeal to
uniqueness — no part of the hard proof above is repeated.

This matters because naturality is what makes the Abel–Jacobi image a *family*
rather than a set of unrelated points: an identity-component argument sees the
universal point `aj_{X,strX}(id_X)` and gets every other `aj T g x` from it by
`pre`, and cannot start without `aj_pre`.  Likewise `aj_base` is what places the
image THROUGH THE ORIGIN, which is the hypothesis "the connected family meets the
identity" in SGA3 VI_B 3.10.  Both are consumed by
`exists_relPicZeroSubfunctor`'s assembly below, which is what puts them into the
hands of `exists_relPicIdentityComponent`'s owner. -/

/-- **THE ABEL–JACOBI FAMILY IS DETERMINED BY ITS SPEC** (PROVEN 2026-07-31) —
two families of points of `Pic` that both solve `[p] + [x] = [o_T]` at every
base agree pointwise.

One application of `IsRelPicOf.eq_of_relPicEquiv_tensor`; it is the "Pinned."
paragraph of `exists_abelJacobiPoint` stated about an arbitrary pair of families
rather than about the one that theorem constructs. -/
theorem aj_eq_of_spec {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (o : RelPoint strX (𝟙 S)) (hP : IsRelPicOf strX pstr)
    (aj aj' : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))))
    (haj' : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj' T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))))
    (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g) :
    aj T g x = aj' T g x :=
  hP.eq_of_relPicEquiv_tensor (isInvertibleSheaf_sectionIdeal hproper hsmooth x)
    (haj T g x) (haj' T g x)

/-- **THE ABEL–JACOBI FAMILY IS NATURAL, FROM ITS SPEC ALONE** (PROVEN
2026-07-31) — `aj_pre` for a family that arrives as a hypothesis.

Compare with `exists_abelJacobiPoint`'s own `aj_pre`, whose proof this does NOT
repeat: the family here is identified with that one by `aj_eq_of_spec`, and the
law is then read off. -/
theorem aj_pre_of_spec {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (o : RelPoint strX (𝟙 S)) (hP : IsRelPicOf strX pstr)
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g)))) :
    ∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
      (x : RelPoint strX g),
      aj T' g' (RelPoint.pre h hg x) = RelPoint.pre h hg (aj T g x) := by
  obtain ⟨aj₀, h0spec, h0pre, -⟩ := exists_abelJacobiPoint hproper hsmooth o hP
  have heq : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g), aj T g x = aj₀ T g x :=
    aj_eq_of_spec hproper hsmooth o hP aj aj₀ haj h0spec
  intro T' T h g g' hg x
  simp only [heq]
  exact h0pre T' T h g g' hg x

/-- **THE ABEL–JACOBI FAMILY SENDS THE BASE POINT TO THE ORIGIN, FROM ITS SPEC
ALONE** (PROVEN 2026-07-31) — `aj_base` for a family that arrives as a
hypothesis.

This is what says the Abel–Jacobi image MEETS THE IDENTITY of `Pic`, and it is
the hypothesis an identity-component argument needs in order to conclude that
the whole (connected) image lies in `Pic⁰`. -/
theorem aj_base_of_spec {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (o : RelPoint strX (𝟙 S)) (hP : IsRelPicOf strX pstr)
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g)))) :
    aj S (𝟙 S) o = hP.zeroPoint (𝟙 S) := by
  obtain ⟨aj₀, h0spec, -, h0base⟩ := exists_abelJacobiPoint hproper hsmooth o hP
  rw [aj_eq_of_spec hproper hsmooth o hP aj aj₀ haj h0spec]
  exact h0base

/-- **`Pic` IS SMOOTH OVER `S`** (**PROVEN 2026-07-31**; the smoothness half of
`smooth_isSeparated_of_isRelPicOf`, split off from it 2026-07-30) — BLR 8.4/2.

**HOW IT WENT THROUGH, and the one change to the signature.**  The statement
quantifies over an ARBITRARY `pstr` with `IsRelPicOf strX pstr`, which is a
shape the literature never proves: BLR does not show "every scheme
representing `Pic_{X/S}` is smooth", it CONSTRUCTS one and reads smoothness
off the construction.  `IsRelPicOf.isoOver` (proven above, pure Yoneda on
`RelPoint`) closes that gap — two representing objects are isomorphic over
`S` — so the leaf reduces to `exists_relPicFull`, whose conclusion was
strengthened the same day to carry `Smooth ∧ IsSeparated`.  The obligation
therefore did not vanish; it moved to `exists_relPicOf_isAffineOpen`, where a
scheme is actually built and where BLR 8.4/2 lives.  Net effect on the
frontier: 4 open leaves in this file became 2.

The signature GAINED a section `_o : RelPoint strX (𝟙 S)`, because
`exists_relPicFull` needs one (BLR 8.1/4 uses the section to collapse the
fppf sheaf onto the naive quotient, and the section is also what makes the
curve relatively projective).  This WEAKENS the leaf and is safe: the sole
consumer, `exists_relPicZeroOf_of_relPicGroupLaw`, already has `o` in scope
and passes it.  The statement is in fact still true without a section — a
representable functor is an fppf sheaf, so a representable naive quotient
already IS `Pic_{X/S}` — but that argument needs descent theory this
development does not have, and manufacturing a harder statement for no
consumer would be the wrong trade.

The classical content, kept because it is what the new owner of
`exists_relPicOf_isAffineOpen` has to supply: the relative Picard functor of a
flat proper morphism is smooth over `S` as
soon as `H²(X_s, 𝒪_{X_s})` vanishes on every fibre, because that group receives
the obstructions to lifting a line bundle along a square-zero thickening.  On a
relative CURVE it vanishes for dimension reasons, so this is the one place in
BLR 9.4/4 where "the fibres are curves" is used as a *cohomological* input
rather than as a geometric one.

**HYPOTHESIS USAGE, now that there is a proof to read it off.**  The proof
spends `_hproper`, `_hsmooth`, `_hconn` and `_o` (all four go into
`exists_relPicFull`) and `_hP` (which is the whole content).  `_hpush` is
GENUINELY IDLE and is deliberately kept, for the same reason `_hequiv` is kept
on `exists_relPicOf_of_hasUniversallyTrivialPushforward`: it is derivable from
the other three by
`hasUniversallyTrivialPushforward_of_isProper_of_smooth`, so it constrains
nothing and cannot make the statement false, while deleting an input from a
released signature churns consumers for no mathematical gain.  A reader must
not treat it as a live obligation — it is not one.

**FAITHFULNESS.**  `_hP` is the whole content: any non-smooth `pstr` refutes
the statement without it, e.g. `Spec k[t]/(t²) ⟶ Spec k`.  Dropping `_hsmooth`
refutes it at relative dimension `2`, where `H²(X_s, 𝒪)` need not vanish and
`Pic` is genuinely obstructed — a K3 over a non-reduced base is the standard
witness.  NOT VACUOUS: `IsRelPicOf strX pstr` is satisfiable, by
`exists_relPicFull`. -/
theorem smooth_of_isRelPicOf {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX) :
    Smooth pstr := by
  obtain ⟨_Q, _qstr, ⟨hQ⟩, hQsmooth, -⟩ :=
    exists_relPicFull strX _hproper _hsmooth _hconn _o
  exact smooth_of_isRelPicOf_of_smooth _hP hQ hQsmooth

/-- **`Pic` IS SEPARATED OVER `S`** (**PROVEN 2026-07-31**; the separatedness
half of `smooth_isSeparated_of_isRelPicOf`, split off from it 2026-07-30) —
BLR 8.2/1, `Pic_{X/S}` is a separated `S`-scheme locally of finite type.

The route is the sibling's verbatim: `IsRelPicOf.isoOver` reduces the "every
representing object" shape to the "some representing object" shape, and
`exists_relPicFull` now supplies the latter.  See `smooth_of_isRelPicOf` above
for the full account, including why the signature gained the section `_o` and
why `_hpush` is kept although the proof does not use it.

The classical content, which is what the owner of
`exists_relPicOf_isAffineOpen` now has to supply: with `f_*𝒪 = 𝒪` universally
the sequence `0 ⟶ Pic T ⟶ Pic X_T ⟶ P(T)` is exact, so two points of `P`
agreeing on a dense open of a valuation base agree, and the valuative
criterion applies (`AlgebraicGeometry.IsSeparated.of_valuativeCriterion` is the
pin's entry point, and it also wants `QuasiSeparated`, which the construction
supplies).  Without `f_*𝒪 = 𝒪` the functor is only a *presheaf* quotient and
the criterion fails — already for `X = S ⊔ S`, the same witness the
Zariski-gluing audit uses.

**One correction to the parent's prose, which this split made checkable and
which the proof has now settled.**  The paragraph below says separatedness "is
where the section `o` and `_hpush` are spent".  When this was a leaf the
signature had no section at all, and the displayed classical argument uses only
`f_*𝒪 = 𝒪`.  The section is now present — but for a different reason than that
paragraph gives: it is consumed by `exists_relPicFull`, i.e. by
REPRESENTABILITY, not by the valuative criterion.  So the sentence is still
wrong about *which* step spends `o`, and it is left visible for the same
reason the module docstring keeps its stale paragraphs. -/
theorem isSeparated_of_isRelPicOf {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (_o : RelPoint strX (𝟙 S))
    (_hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX) :
    IsSeparated pstr := by
  obtain ⟨_Q, _qstr, ⟨hQ⟩, -, hQsep⟩ :=
    exists_relPicFull strX _hproper _hsmooth _hconn _o
  exact isSeparated_of_isRelPicOf_of_isSeparated _hP hQ hQsep

/-- **`Pic` IS SMOOTH AND SEPARATED OVER `S`** (PROVEN 2026-07-30 as the
assembly of the two halves just above; formerly a bare sorry leaf, cut
2026-07-29 out of `exists_relPicZeroSubgroup`, and the audit below is the
docstring written while it was one) — the FIRST of BLR 9.4/4's three classical
steps, and the only one of the three that is a statement about `Pic` alone.

*Smoothness* is BLR 8.4/2: the relative Picard functor of a flat proper
morphism is smooth over `S` as soon as `H²(X_s, 𝒪_{X_s})` vanishes on every
fibre, because that group receives the obstructions to lifting a line bundle
along a square-zero thickening.  On a relative CURVE it vanishes for dimension
reasons, so no hypothesis beyond `_hsmooth` is needed — this is the one place in
BLR 9.4/4 where "the fibres are curves" is used as a *cohomological* input
rather than as a geometric one.

*Separatedness* is BLR 8.2/1 (`Pic_{X/S}` is a separated `S`-scheme locally of
finite type), which is where the section `o` and `_hpush` are spent: with
`f_*𝒪 = 𝒪` universally, the sequence `0 ⟶ Pic T ⟶ Pic X_T ⟶ P(T)` is exact, so
two points of `P` agreeing on a dense open of a valuation base agree, and the
valuative criterion applies.  Without `_hpush` the functor is only a *presheaf*
quotient and the criterion fails.

**WHY THIS IS A CUT AND NOT A RELOCATION.**  It removes an obligation from
`exists_relPicZeroSubgroup` that is *independent* of the two remaining ones: the
identity component and the valuative criterion for `Pic⁰` both CONSUME
smoothness and separatedness of `Pic` and neither contributes to proving them.
The two are also both statements about `Pic` only, with no reference to `J`,
`incl` or `aj` — which is exactly why they can be stated before the object that
does not yet exist.

**FAITHFULNESS.**  `_hP` is load-bearing and is the whole content of the
statement: `pstr` is an arbitrary morphism until `IsRelPicOf` pins it, and `inj`
+ `surj` pin it up to unique `S`-isomorphism by Yoneda, so smoothness and
separatedness transport.  Drop `_hP` and the statement is FALSE for the obvious
reason — any non-smooth `pstr` is a counterexample, e.g. `Spec k[t]/(t²) ⟶ Spec k`.
Drop `_hsmooth` and smoothness fails: for `X ⟶ S` of relative dimension `2`,
`H²(X_s, 𝒪)` need not vanish and `Pic` is genuinely obstructed (a K3 over a
non-reduced base is the standard witness).  Drop `_hpush` and separatedness
fails as described above, already for `X = S ⊔ S`, the same witness the
Zariski-gluing audit uses.

**NOT VACUOUS.**  `IsRelPicOf strX pstr` is satisfiable — that is
`exists_relPicFull`, PROVEN above — so this is not a statement about an empty
class of `pstr`.

**CUT IN TWO, 2026-07-30, and this declaration is now the assembly.**  The two
conjuncts are BLR 8.4/2 and BLR 8.2/1: different chapters, different arguments
(deformation theory against `H²` on the fibres, versus the valuative criterion),
and — as the paragraphs above already say in prose — different hypotheses.  They
were welded together only because they were cut out of
`exists_relPicZeroSubgroup` in one motion, and one owner had to carry both.  See
`smooth_of_isRelPicOf` and `isSeparated_of_isRelPicOf` below.  Nothing
downstream changed: `exists_relPicZeroOf_of_relPicGroupLaw` still destructures
this conjunction. -/
theorem smooth_isSeparated_of_isRelPicOf {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX)
    (hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX) :
    Smooth pstr ∧ IsSeparated pstr :=
  ⟨smooth_of_isRelPicOf hproper hsmooth hconn o hP hpush,
    isSeparated_of_isRelPicOf hproper hsmooth hconn o hP hpush⟩

/-! ### The 2026-07-29 audit of `exists_relPicZeroSubgroup`

**`Pic⁰` IS AN ABELIAN SCHEME INSIDE `Pic`** (sorry leaf, cut
2026-07-29) — BLR 9.4/4's geometric half, and the whole of what that
theorem is usually cited for.

This was the docstring of `exists_relPicZeroSubgroup` while that
declaration was a leaf.  It is demoted to a section comment on 2026-07-31,
unchanged, because the leaf was cut again on that day and the survey it
records is what a reader of EITHER half needs; the two declarations below
carry their own docstrings.

Given `Pic` and the Abel–Jacobi map into it, cut out the identity
component and show it is an abelian scheme over `S`.  Concretely the
three classical steps:

* `Pic ⟶ S` is **smooth and separated** — this is where `_hpush`
  (`f_*𝒪 = 𝒪` universally) and the vanishing of `H²` on a relative curve
  are spent.  **CUT OUT** as `smooth_isSeparated_of_isRelPicOf` above
  (stated 2026-07-29, wired up 2026-07-30, and split later that day into
  `smooth_of_isRelPicOf` + `isSeparated_of_isRelPicOf` — the conjunction
  itself is now PROVEN as their assembly), and received here as the two
  hypotheses `_hPsmooth` and `_hPsep`; the parent
  `exists_relPicZeroOf_of_relPicGroupLaw` discharges them by that leaf, so
  nothing downstream changed;
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
`Pic(X_T)/Pic(T)` is a quotient set.

**CUT AGAIN, 2026-07-31, and this declaration is now the assembly.**  What is
below is `exists_relPicZeroSubfunctor` plus the transport of the group law
along `incl`; the audit above is left intact because it is still what a reader
needs, and every one of its junk-witness arguments applies verbatim to the new
leaf (which carries the same properness, Abel–Jacobi and injectivity clauses).
See the section heading immediately below for what moved and why. -/

/-! ### BLR 9.4/4's geometric half: the subfunctor, and the group law on it

**CUT 2026-07-31.**  `exists_relPicZeroSubgroup` used to be asked for an
`AbelianSchemeStruct` on `Pic⁰` — twelve fields, of which nine are group
axioms and two are naturality.  None of those nine has anything to do with the
identity component: they are the group axioms of `Pic` itself, restricted to a
subgroup, and a prover of the geometry had to reprove them from scratch.

So the leaf below asks instead for the subfunctor: a scheme `J`, proper, smooth
and with geometrically connected fibres, injecting naturally into the points of
`Pic`, whose image is CLOSED UNDER the group law of `Pic` (contains
`zeroPoint`, closed under `addPoint` and under `negPoint`) and contains the
Abel–Jacobi image.  The group structure is then transported by
`exists_relPicZeroSubgroup` below, over the group axioms for `IsRelPicOf`
proven earlier in this file.

**Why this is a cut and not a relocation.**  The three closure clauses are the
ONLY group-theoretic content left in the leaf, and each is a single existential
with no equations to verify — an owner discharges them by exhibiting a point of
`Pic⁰`, which is what an identity-component construction produces anyway.  What
leaves the leaf is: `add`, `zero`, `neg` as operations; `add_assoc`,
`add_comm`, `zero_add`, `neg_add`; `pre_add`, `pre_zero`; and the three
conclusion clauses of the parent that name `ab.zero` and `ab.add`.  All nine of
those are now discharged by `hinj` applied to a rewrite chain, in the assembly
below, and none of them was ever geometry.

**What the cut does NOT do**, and this is the reason it is small rather than
decisive: the two genuinely missing pieces are unchanged and both still sit in
the leaf — the identity component of a group scheme (absent from the pin in any
form) and properness of `Pic⁰` by the valuative criterion (BLR 9.4).  Whoever
takes the leaf takes both.  A further cut along THAT line is possible — state
`J` open in `P` with connected fibres, then properness separately — but it
needs an `IsOpenImmersion`-flavoured statement, and the parent's own audit
records why the conclusion is on points rather than on subschemes ("stating it
as an open immersion would force the caller to convert").  I left that boundary
where the parent put it.

**Faithfulness of the closure clauses.**  `negPoint` is a `Classical.choose`,
so "closed under `negPoint`" reads, on its face, as a condition on an arbitrary
choice.  It is not: `hP.inj` makes the point classifying the inverse sheaf
unique, so `negPoint p` is THE inverse and the clause is the honest statement
that the subfunctor is closed under inversion.  The same remark applies to
`zeroPoint` and `addPoint`, and is why the group axioms above could be proven
about them at all. -/

/-! ### CUT AGAIN, 2026-07-31 (second cut of the day): SGA3 from BLR 9.4

The leaf that stood here asked for BOTH classical chapters its own docstring
named as missing — the identity component of a group scheme (SGA3 VI_B 3.10)
and properness of `Pic⁰` (BLR 9.4) — and said so explicitly: "Whoever takes the
leaf takes both."  They are different arguments with no shared machinery: one is
about connected components of a smooth separated group functor and never
mentions a curve; the other is the valuative criterion for line bundles on a
relative curve and never mentions a component.  So they are split here, along
exactly the line the previous cut declined to take, and
`exists_relPicZeroSubfunctor` is now the (two-line) assembly:

* `exists_relPicIdentityComponent` — everything EXCEPT `IsProper jstr`;
* `isProper_relPicIdentityComponent` — `IsProper jstr`, taking the whole
  conclusion of the first as its hypotheses.

**How the boundary the previous cut worried about is resolved.**  That cut
recorded "a further cut along THAT line is possible — state `J` open in `P` with
connected fibres, then properness separately — but it needs an
`IsOpenImmersion`-flavoured statement, and the parent's own audit records why
the conclusion is on points rather than on subschemes."  The resolution is that
NO open-immersion statement is needed: the properness half does not take "`J` is
open in `P`" as its hypothesis, it takes the FIRST HALF'S CONCLUSION verbatim —
`incl` natural and injective, image closed under the group law, image containing
the Abel–Jacobi image, `J` smooth with geometrically connected fibres.  That is
already a complete characterisation of `Pic⁰` (the derivation is written out on
the properness leaf), it is stated entirely on points, and nothing crosses the
boundary that was not already in the parent's language.  So the cut costs no new
vocabulary at all.

**The load-bearing check, and where it is written.**  Splitting `A ∧ B` into
"`A`" and "`A → B`" is faithfulness-neutral only if `B` holds for EVERY witness
of `A`, not merely for the intended one.  Weakening the leaf by deleting
`IsProper` admits junk witnesses that the deleted conjunct used to exclude, and
if any of them failed properness the second half would be FALSE.  That check is
carried out in full in the FAITHFULNESS section of
`isProper_relPicIdentityComponent`; it is the only nontrivial thing about this
cut, and it turns on the connectedness clause, which is what now does the work
`IsProper` used to do in excluding `J = P`.

**What ALSO improved, and it is not bookkeeping.**  `aj` now arrives with all
three of its laws rather than one.  `aj_pre_of_spec` and `aj_base_of_spec` above
derive naturality and `aj o = 0` from the spec alone, so the assembly can hand
them to both halves for free.  Before the cut, an owner of the geometry held
only the spec and could not even say that the Abel–Jacobi image passes through
the origin — which is the hypothesis of the SGA3 statement being invoked. -/

/-- **THE IDENTITY COMPONENT `Pic⁰ ⊆ Pic`** (sorry leaf, cut 2026-07-31 out of
`exists_relPicZeroSubfunctor`) — SGA3 VI_B 3.10 / EGA IV 15.6.5, the first of
the two classical chapters that leaf carried.

A scheme `J`, smooth over `S` with geometrically connected fibres, whose points
inject naturally into the points of `Pic`, whose image is closed under the group
law of `Pic` (contains `zeroPoint`, closed under `addPoint` and `negPoint`), and
contains the Abel–Jacobi image.

**Properness is deliberately NOT asked for here.**  It is
`isProper_relPicIdentityComponent` below — BLR 9.4, a different chapter with a
different argument — and `exists_relPicZeroSubfunctor` is the two assembled.  See
the section heading above for why the boundary can be drawn here without any
`IsOpenImmersion` vocabulary.

**What the hypotheses give you that they did not before the cut.**  `aj` arrives
with all THREE of its laws: the spec `_haj`, naturality `_hajpre`, and
`aj o = 0` (`_hajbase`).  The last two used to be locked inside
`exists_abelJacobiPoint`'s existential; they are supplied by `aj_pre_of_spec` /
`aj_base_of_spec`, which derive them from the spec alone.  They are precisely
what the SGA3 argument needs.  `_hajbase` says the Abel–Jacobi image MEETS THE
IDENTITY of `Pic`.  `_hajpre` says the image is one FAMILY rather than an
unstructured set of points: the universal point `aj X strX ⟨𝟙 X, _⟩` is a
`X`-point of `Pic`, `X` is proper smooth with geometrically connected fibres
(`_hproper`, `_hsmooth`, `_hconn`), it meets the origin at `o` by `_hajbase`,
and every other `aj T g x` is obtained from it by `RelPoint.pre` — so "a
connected family through the identity lies in the identity component" applies to
ONE point and then propagates.  That is the whole reason the Abel–Jacobi clause
of the conclusion is reachable at all.

**FAITHFULNESS.**  This is the conclusion of `exists_relPicZeroSubfunctor` with
one conjunct deleted, under strictly MORE hypotheses, so it is implied by that
statement and cannot be false unless that one was.  A weakening cannot introduce
falsity; what it CAN do is admit junk witnesses, and here it does — `J = P`,
`incl = id` now satisfies every clause except `GeometricallyConnected jstr`.
That is harmless for THIS leaf and is exactly what must be checked for its
sibling, where it is (see `isProper_relPicIdentityComponent`).

The parent's other junk-witness arguments apply verbatim, and neither remaining
clause may be dropped:

* drop the **Abel–Jacobi clause** and `J = S`, `jstr = 𝟙 S` survives —
  `RelPoint (𝟙 S) g` is a singleton, so injectivity, naturality and all three
  closure clauses are free, and `𝟙 S` is smooth with connected point fibres.
  The clause kills it: at `T = X`, `g = strX` the classes of `𝒪(Δ − o_X)` and
  `𝒪` are distinct for `g ≥ 1`, so `aj` takes two values there and cannot
  factor through a singleton;
* drop **injectivity** of `incl` and `J` may be any smooth connected scheme
  mapping onto `Pic⁰`, e.g. `Pic⁰ × E` for an elliptic curve `E` — and then the
  transport in `exists_relPicZeroSubgroup` is not merely unprovable but FALSE,
  since `ab.add` would have to be a `choose` among several preimages.

**TRUE at genus 0**, where `Pic⁰ = S` is the junk witness above and the
Abel–Jacobi clause is satisfiable by it, every `𝒪(x − o)` being trivial.

**NOT VACUOUS**: `IsRelPicOf strX pstr` is satisfiable (`exists_relPicFull`,
PROVEN above), so this is not a statement about an empty class of `pstr`. -/
theorem exists_relPicIdentityComponent {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))))
    (_hajpre : ∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
      (x : RelPoint strX g), aj T' g' (RelPoint.pre h hg x) = RelPoint.pre h hg (aj T g x))
    (_hajbase : aj S (𝟙 S) o = hP.zeroPoint (𝟙 S)) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S)
      (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g),
      Smooth jstr ∧ GeometricallyConnected jstr ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          incl T g p = incl T g q → p = q) ∧
        (∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
          (p : RelPoint jstr g),
          incl T' g' (RelPoint.pre h hg p) = RelPoint.pre h hg (incl T g p)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S),
          ∃ z : RelPoint jstr g, incl T g z = hP.zeroPoint g) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          ∃ r : RelPoint jstr g, incl T g r = hP.addPoint (incl T g p) (incl T g q)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p : RelPoint jstr g),
          ∃ r : RelPoint jstr g, incl T g r = hP.negPoint (incl T g p)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
          ∃ p : RelPoint jstr g, incl T g p = aj T g x) := sorry

/-- **`Pic⁰ ⟶ S` IS PROPER** (sorry leaf, cut 2026-07-31 out of
`exists_relPicZeroSubfunctor`) — BLR 9.4, the second of the two classical
chapters that leaf carried, and the one the valuative criterion for line bundles
on a relative curve is for.

The hypotheses are the conclusion of `exists_relPicIdentityComponent` verbatim,
plus the curve and `Pic` hypotheses that leaf already had.  Nothing about open
immersions is asked for or offered: the clauses below already pin `J` as `Pic⁰`,
and the derivation is written out under FAITHFULNESS.

**The intended argument** (BLR 9.4/4, and 8.4 for the finiteness inputs).
`Pic_{X/S}` is smooth (`_hPsmooth`) and separated (`_hPsep`) over `S`, and
`f_*𝒪 = 𝒪` universally (`_hpush`) is what makes its `T`-points the naive
quotient `Pic(X_T)/Pic(T)` rather than an fppf sheafification, which is the form
`hP` states.  Properness of the degree-zero part is then the valuative
criterion: for a valuation ring `R` with fraction field `K` and a degree-zero
class on `X_K`, the closure of the corresponding divisor in `X_R` is a divisor
whose degree on the special fibre can be corrected to `0` by a multiple of the
special fibre itself — `X_R ⟶ Spec R` being proper, smooth and with
geometrically connected fibres, so its fibres are irreducible and the degree map
is defined.  Uniqueness of the extension is separatedness.  Finite-type-ness,
the other half of properness, is BLR 8.4/3 (`Pic` is locally of finite type,
and `Pic⁰` is quasi-compact because it is a CONNECTED group scheme locally of
finite type over a field on each fibre — SGA3 VI_A 2.4).

**FAITHFULNESS — and this is the load-bearing check of the 2026-07-31 cut, not
a formality.**  Splitting a conjunction `A ∧ B` into `A` and `A → B` is only
faithfulness-neutral if `B` holds for EVERY witness of `A`.  Here `A` was
weakened by deleting `IsProper`, so witnesses that the deleted conjunct used to
exclude are now admitted, and the question is whether any of them fails
properness.  None does, and here is why: the hypotheses force `J = Pic⁰`.

1. `_hinclpre` and `_hinj` make `incl` a monomorphism of functors on `Over S`.
   By Yoneda (evaluate at `T = J`, `g = jstr`, on the tautological point) it is
   `(· ≫ ι)` for a unique `ι : J ⟶ P` over `S`, and `ι` is a monomorphism of
   schemes.
2. `_hzero`, `_hadd`, `_hneg` make the image a SUBGROUP functor of `Pic` — the
   three clauses are exactly closure under the three operations, and each is an
   honest closure statement because `hP.inj` makes the point classifying a given
   sheaf unique (see the section heading before `exists_relPicIdentityComponent`).
3. `_hJconn` says every geometric fibre `J_s̄` is a CONNECTED topological space,
   which in `Mathlib`'s `ConnectedSpace` includes NONEMPTY.  Together with 2 it
   places `J_s̄` inside the identity component of `Pic_s̄`, i.e. `J_s̄ ⊆ Pic⁰_s̄`.
   This is where the clause that replaced `IsProper` does its work: without it
   `J = P`, `incl = id` satisfies 1 and 2 and the Abel–Jacobi clause, and `Pic`
   is NOT proper — so `GeometricallyConnected jstr` is the hypothesis that makes
   this leaf true, and it may not be dropped.
4. `_himg` puts the class of `𝒪(x − o)` in `J_s̄` for every point `x` of the
   fibre `X_s̄`.  Those classes GENERATE `Pic⁰_s̄` as a group (Riemann–Roch: every
   degree-zero class on a smooth projective connected curve of genus `g` is
   `𝒪(D − g·o)` for an effective `D` of degree `g`, hence a sum of `g` such
   differences), so with 2 we get `J_s̄ ⊇ Pic⁰_s̄` on points.
5. A monomorphism of group schemes of finite type over a field is a closed
   immersion (SGA3 VI_B 1.4.2), and `J_s̄` is of finite type by the SGA3 VI_A 2.4
   remark above, so 3 + 4 give `J_s̄ = Pic⁰_s̄` as schemes, fibrewise, and `ι` is
   an isomorphism onto `Pic⁰`.  `Pic⁰ ⟶ S` is proper by BLR 9.4/4.

So the leaf is TRUE for every witness of `exists_relPicIdentityComponent`, which
is what the cut needed.

**Which clauses are load-bearing, tested by deleting them one at a time.**

* Drop `_hJconn` and it is FALSE, by `J = P`, `incl = id` as in 3 above: every
  other clause survives (`_himg` holds with `p := aj T g x`), and `Pic_{X/S}` is
  not proper over `S` — it is a disjoint union of the `Pic^d`, of which there
  are infinitely many.  This is the sharpest witness in the audit and the reason
  the connectedness clause is stated on the LEAF rather than derived.
* Drop `_hinj` and it is FALSE: `J := Pic⁰ ⊔ 𝔸¹_S` with `incl` sending both
  copies into `Pic⁰`… fails `_hJconn`; the honest witness is
  `J := Pic⁰ ×_S 𝔸¹_S` with `incl` the first projection on points, which is
  smooth, has geometrically connected fibres, has image closed under the group
  law and containing the Abel–Jacobi image, and is not proper.  So injectivity
  is load-bearing too.
* `_himg` is NOT load-bearing for this leaf, and the audit says so rather than
  claiming a witness it does not have: by 2 and 3 alone `J_s̄` is a connected
  subgroup functor of `Pic⁰_s̄`, `Pic⁰_s̄` is an abelian variety (the curve is
  smooth and proper), and a monomorphism from a smooth connected group scheme
  into an abelian variety is a closed immersion onto an abelian subvariety,
  hence proper.  The clause is nevertheless KEPT, for two reasons: it is
  supplied free by the sibling leaf, and it upgrades "`J` is *some* abelian
  subvariety of `Pic⁰`" to "`J` IS `Pic⁰`", which is what the name claims and
  what `exists_relPicZeroSubgroup`'s consumers read the result as.  Dropping a
  hypothesis strengthens a leaf, and this development has a standing record of
  restatements that composed into a false statement
  (`exists_artinDivisorNormIndex_le_ray_class`); a prover who finds it genuinely
  idle should delete it THEN, with a proof in hand.
* The curve hypotheses `_hproper`, `_hsmooth`, `_hconn`, `o` and `_hpush` are
  all spent: smoothness and properness of the curve are what make `Pic⁰` an
  abelian scheme at all, geometric connectedness of the fibres is what makes the
  degree map well defined in the valuative criterion, the section `o` is what
  makes the naive quotient `Pic(X_T)/Pic(T)` the right functor (BLR 8.1/4), and
  `_hpush` is what `hP` needs in order to be about that quotient. -/
theorem isProper_relPicIdentityComponent {X P J S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    {jstr : J ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))))
    (_hajpre : ∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
      (x : RelPoint strX g), aj T' g' (RelPoint.pre h hg x) = RelPoint.pre h hg (aj T g x))
    (_hajbase : aj S (𝟙 S) o = hP.zeroPoint (𝟙 S))
    (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g)
    (_hJsmooth : Smooth jstr) (_hJconn : GeometricallyConnected jstr)
    (_hinj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
      incl T g p = incl T g q → p = q)
    (_hinclpre : ∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
      (p : RelPoint jstr g),
      incl T' g' (RelPoint.pre h hg p) = RelPoint.pre h hg (incl T g p))
    (_hzero : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      ∃ z : RelPoint jstr g, incl T g z = hP.zeroPoint g)
    (_hadd : ∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
      ∃ r : RelPoint jstr g, incl T g r = hP.addPoint (incl T g p) (incl T g q))
    (_hneg : ∀ (T : Scheme.{u}) (g : T ⟶ S) (p : RelPoint jstr g),
      ∃ r : RelPoint jstr g, incl T g r = hP.negPoint (incl T g p))
    (_himg : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      ∃ p : RelPoint jstr g, incl T g p = aj T g x) :
    IsProper jstr := sorry

/-- **A smooth `S`-group scheme with geometrically connected fibres, WITHOUT the
properness that would make it abelian** — every field of `AbelianSchemeStruct`
except `proper`.

This is what the identity-component construction can produce before the
valuative criterion has been run, and `toAbelianSchemeStruct` below is the one
line that closes the gap. -/
structure RelGroupSchemeStruct {A S : Scheme.{u}} (f : A ⟶ S) where
  /-- addition of relative points -/
  add : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint f g → RelPoint f g
  /-- the zero section, read as a relative point -/
  zero : ∀ {T : Scheme.{u}} (g : T ⟶ S), RelPoint f g
  /-- inversion of relative points -/
  neg : ∀ {T : Scheme.{u}} {g : T ⟶ S}, RelPoint f g → RelPoint f g
  /-- associativity of the group law -/
  add_assoc : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x y z : RelPoint f g),
    add (add x y) z = add x (add y z)
  /-- commutativity of the group law -/
  add_comm : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x y : RelPoint f g), add x y = add y x
  /-- the unit law -/
  zero_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g), add (zero g) x = x
  /-- the inverse law -/
  neg_add : ∀ {T : Scheme.{u}} {g : T ⟶ S} (x : RelPoint f g), add (neg x) x = zero g
  /-- naturality of addition -/
  pre_add : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g') (x y : RelPoint f g),
    RelPoint.pre h hg (add x y) = add (RelPoint.pre h hg x) (RelPoint.pre h hg y)
  /-- naturality of the zero section -/
  pre_zero : ∀ {T' T : Scheme.{u}} (h : T' ⟶ T) {g : T ⟶ S} {g' : T' ⟶ S}
    (hg : h ≫ g = g'), RelPoint.pre h hg (zero g) = zero g'
  /-- smooth over the base -/
  smooth : Smooth f
  /-- geometrically connected fibres -/
  connected : GeometricallyConnected f

/-- **Properness is the only thing between the two structures** (PROVEN). -/
def RelGroupSchemeStruct.toAbelianSchemeStruct {A S : Scheme.{u}} {f : A ⟶ S}
    (G : RelGroupSchemeStruct f) (hproper : IsProper f) : AbelianSchemeStruct f where
  add := G.add
  zero := G.zero
  neg := G.neg
  add_assoc := G.add_assoc
  add_comm := G.add_comm
  zero_add := G.zero_add
  neg_add := G.neg_add
  pre_add := G.pre_add
  pre_zero := G.pre_zero
  proper := hproper
  smooth := G.smooth
  connected := G.connected

/-- **The five point-level clauses that pin `Pic⁰` inside `Pic`**, abbreviated so
that the two leaves below and the assembly all read exactly the same list rather
than three copies that can drift apart.

It is the conclusion of `exists_relPicZeroSubgroup` verbatim, with
`ab : AbelianSchemeStruct jstr` replaced by `G : RelGroupSchemeStruct jstr` —
the clauses mention only `G.zero` and `G.add`, so nothing is lost. -/
def IsRelPicZeroIncl {X P S J : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S} {jstr : J ⟶ S}
    (hP : IsRelPicOf strX pstr) (G : RelGroupSchemeStruct jstr)
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g) : Prop :=
  (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g), incl T g p = incl T g q → p = q) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ S), incl T g (G.zero g) = hP.zeroPoint g) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          incl T g (G.add p q) = hP.addPoint (incl T g p) (incl T g q)) ∧
        (∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
            (p : RelPoint jstr g),
            incl T' g' (RelPoint.pre h hg p) = RelPoint.pre h hg (incl T g p)) ∧
          (∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
              ∃ p : RelPoint jstr g, incl T g p = aj T g x)

/-- **THE IDENTITY COMPONENT OF `Pic` AS AN OPEN SUBGROUP SCHEME** (sorry leaf,
cut 2026-07-30 out of `exists_relPicZeroSubgroup`) — BLR 9.4/4 step two, and the
step that is genuinely absent from the pin.

`Pic ⟶ S` is smooth (`_hPsmooth`) and separated (`_hPsep`), so its fibres are
smooth group schemes over fields and each has an open-and-closed identity
component; SGA 3 VI_B 3.10 assembles these into an open subgroup scheme
`Pic⁰ ⊆ Pic`, smooth over `S` because `Pic` is and open immersions are smooth,
with geometrically connected fibres by construction.  The Abel–Jacobi clause
holds because `aj T g x` is the class of `𝒪(x − o)`, which has degree `0` on
every geometric fibre, and the degree-`0` part of `Pic` of a geometrically
connected smooth proper curve IS the identity component.

**FAITHFULNESS.**  The three clauses that pin `Pic⁰` are analysed in the parent's
audit and every word of it applies here unchanged, with ONE difference that
matters: this leaf does *not* claim properness, so the junk witness the parent
rules out by properness — `J = P`, `incl = id` — is **not** ruled out here.  That
is deliberate and is the entire content of the cut: `J = P` satisfies every
clause of `IsRelPicZeroIncl` and is killed only by
`isProper_of_relPicZeroGroupScheme` below, which is therefore not a formality.
Two of the parent's three clauses do still bite here:

* drop the **Abel–Jacobi clause** and `J = S`, `jstr = 𝟙 S` survives, exactly as
  the parent records — `RelPoint (𝟙 S) g` is a singleton, so injectivity,
  the homomorphism clause and naturality are free, and `𝟙 S` is smooth with
  connected fibres;
* drop **injectivity** of `incl` and any smooth connected group scheme mapping
  onto `Pic⁰` will do, e.g. `Pic⁰ × 𝔾ₐ`.

`_hpush` and `_hequiv` are carried because the parent carries them and because
the degree function used to identify the Abel–Jacobi image with `Pic⁰` is only
well defined on the quotient `Pic(X_T)/Pic(T)`.

**NOT VACUOUS.**  `IsRelPicOf strX pstr` is satisfiable (`exists_relPicFull`),
and the conclusion is an existential over a nonempty class — `J = P` is a
witness of everything except what the next leaf adds. -/
theorem exists_relPicZeroGroupScheme {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g)))) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S) (G : RelGroupSchemeStruct jstr)
      (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g),
      IsRelPicZeroIncl hP G aj incl :=
  sorry

/-- **THE IDENTITY COMPONENT IS PROPER** (sorry leaf, cut 2026-07-30 out of
`exists_relPicZeroSubgroup`) — BLR 9.4/4 step three, the valuative criterion for
line bundles on a relative curve, and the clause that turns the group scheme of
the previous leaf into an ABELIAN scheme.

`Pic⁰ ⟶ S` is of finite type and separated (inherited from `Pic`), so
properness is the existence half of the valuative criterion: given a discrete
valuation ring `R` with fraction field `K` over `S` and a degree-`0` line bundle
on `X_K`, extend it to `X_R`.  On a REGULAR total space this is the classical
"take the closure of the divisor" argument — `X_R` is regular because `X ⟶ S` is
smooth and `R` is regular — and the extension is unique up to a twist from `R`,
i.e. unique in the relative Picard group, which is the uniqueness half.  This is
where the smooth-relative-CURVE hypothesis is spent a second time, and it is the
only place in this file where a valuation base appears.

**FAITHFULNESS — this leaf is NOT vacuous and NOT free.**  Its hypotheses
include the entire output of `exists_relPicZeroGroupScheme`, so a reader may
suspect it is implied by them.  It is not: the junk witness `J = P`,
`incl = id`, `G` the group data of `Pic` itself satisfies `IsRelPicZeroIncl` in
full, and `Pic ⟶ S` is **not** proper — it has infinitely many components,
one per degree, already for `X` an elliptic curve over `S = Spec k`.  So the
conclusion is false for that witness and this leaf is exactly the statement
that the witness handed over was the identity component rather than all of
`Pic`.  In particular it may NOT be proven from `_hincl` alone; a prover must
use how `J` was constructed, which is why the two leaves are stated with the
same hypothesis list.

**Where the hypotheses are spent.**  `_hproper`/`_hsmooth`/`_hconn` give the
regularity of `X_R` and the degree theory on the geometric fibres; `o` and
`_hpush` are what make the relative Picard group a quotient SET in which
"unique up to a twist" is literally uniqueness; `_hPsep` supplies separatedness,
without which the valuative criterion gives at most universal closedness. -/
theorem isProper_of_relPicZeroGroupScheme {X P S J : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g))))
    {jstr : J ⟶ S} (_G : RelGroupSchemeStruct jstr)
    (_incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g)
    (_hincl : IsRelPicZeroIncl hP _G aj _incl) :
    IsProper jstr :=
  sorry

/-! **`Pic⁰` IS AN ABELIAN SCHEME INSIDE `Pic`** (PROVEN 2026-07-30 over
`exists_relPicZeroGroupScheme` and `isProper_of_relPicZeroGroupScheme`; the
audit above this subsection is the one written while it was one node, and still
says what a reader needs).

The assembly is the one line the cut was made for: take the group scheme the
first leaf produces, feed its data to the second to get properness, and
`RelGroupSchemeStruct.toAbelianSchemeStruct` closes the gap.  The five clauses
are `IsRelPicZeroIncl` unfolded, and they are literally the same propositions —
`toAbelianSchemeStruct` leaves `add` and `zero` untouched, which is why no
rewrite is needed anywhere below.

(RELEASE 26: the two paragraphs below and above were TWO docstrings with the
declaration between them deleted at an earlier release, so the second one was
parsed as Lean. They are joined here into one section comment, which needs no
declaration; no prose is lost. The declaration they described is now
`exists_relPicZeroSubfunctor` below.)

`Pic(X_T)/Pic(T)` is a quotient set.

**CUT AGAIN, 2026-07-31, and this declaration is now the assembly.**  What is
below is `exists_relPicZeroSubfunctor` plus the transport of the group law
along `incl`; the audit above is left intact because it is still what a reader
needs, and every one of its junk-witness arguments applies verbatim to the new
leaf (which carries the same properness, Abel–Jacobi and injectivity clauses).
See the section heading immediately below for what moved and why. -/

/-! ### BLR 9.4/4's geometric half: the subfunctor, and the group law on it

**CUT 2026-07-31.**  `exists_relPicZeroSubgroup` used to be asked for an
`AbelianSchemeStruct` on `Pic⁰` — twelve fields, of which nine are group
axioms and two are naturality.  None of those nine has anything to do with the
identity component: they are the group axioms of `Pic` itself, restricted to a
subgroup, and a prover of the geometry had to reprove them from scratch.

So the leaf below asks instead for the subfunctor: a scheme `J`, proper, smooth
and with geometrically connected fibres, injecting naturally into the points of
`Pic`, whose image is CLOSED UNDER the group law of `Pic` (contains
`zeroPoint`, closed under `addPoint` and under `negPoint`) and contains the
Abel–Jacobi image.  The group structure is then transported by
`exists_relPicZeroSubgroup` below, over the group axioms for `IsRelPicOf`
proven earlier in this file.

**Why this is a cut and not a relocation.**  The three closure clauses are the
ONLY group-theoretic content left in the leaf, and each is a single existential
with no equations to verify — an owner discharges them by exhibiting a point of
`Pic⁰`, which is what an identity-component construction produces anyway.  What
leaves the leaf is: `add`, `zero`, `neg` as operations; `add_assoc`,
`add_comm`, `zero_add`, `neg_add`; `pre_add`, `pre_zero`; and the three
conclusion clauses of the parent that name `ab.zero` and `ab.add`.  All nine of
those are now discharged by `hinj` applied to a rewrite chain, in the assembly
below, and none of them was ever geometry.

**What the cut does NOT do**, and this is the reason it is small rather than
decisive: the two genuinely missing pieces are unchanged and both still sit in
the leaf — the identity component of a group scheme (absent from the pin in any
form) and properness of `Pic⁰` by the valuative criterion (BLR 9.4).  Whoever
takes the leaf takes both.  A further cut along THAT line is possible — state
`J` open in `P` with connected fibres, then properness separately — but it
needs an `IsOpenImmersion`-flavoured statement, and the parent's own audit
records why the conclusion is on points rather than on subschemes ("stating it
as an open immersion would force the caller to convert").  I left that boundary
where the parent put it.

**Faithfulness of the closure clauses.**  `negPoint` is a `Classical.choose`,
so "closed under `negPoint`" reads, on its face, as a condition on an arbitrary
choice.  It is not: `hP.inj` makes the point classifying the inverse sheaf
unique, so `negPoint p` is THE inverse and the clause is the honest statement
that the subfunctor is closed under inversion.  The same remark applies to
`zeroPoint` and `addPoint`, and is why the group axioms above could be proven
about them at all. -/

/-- **`Pic⁰` IS A PROPER SMOOTH SUBFUNCTOR OF `Pic` WITH CONNECTED FIBRES**
(PROVEN 2026-07-31 over `exists_relPicIdentityComponent` and
`isProper_relPicIdentityComponent`; a sorry leaf for a few hours the same day,
cut out of `exists_relPicZeroSubgroup`) — BLR 9.4/4's geometric half with the
group axioms removed.

The two classical steps it used to carry are now one leaf each, and this
declaration is their assembly: `exists_relPicIdentityComponent` produces the
subfunctor, `isProper_relPicIdentityComponent` takes that entire conclusion and
returns `IsProper jstr`, and nothing is left over.  The only step that is not
re-packaging is the discharge of the two Abel–Jacobi laws that both halves ask
for and the caller does not supply: `aj_pre_of_spec` and `aj_base_of_spec`
derive them from `_haj` alone.  See the section heading above for why the cut is
legitimate and where its load-bearing check is written.

Everything the ORIGINAL parent asked for — the `AbelianSchemeStruct` — is
supplied by transport from `IsRelPicOf.addPoint_assoc` and its siblings in
`exists_relPicZeroSubgroup` below; the audit written while all of this was one
node is the section comment further above and is still what a reader wants. -/
theorem exists_relPicZeroSubfunctor {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
    (_hequiv : ∀ {T : Scheme.{u}} (g : T ⟶ S), Equivalence (RelPicEquiv strX g))
    (aj : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint strX g → RelPoint pstr g)
    (_haj : ∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
      RelPicEquiv strX g (modTensor (hP.sheaf (aj T g x)) (sectionIdeal (relSection x)))
        (sectionIdeal (relSection (relBasePoint o g)))) :
    ∃ (J : Scheme.{u}) (jstr : J ⟶ S)
      (incl : ∀ (T : Scheme.{u}) (g : T ⟶ S), RelPoint jstr g → RelPoint pstr g),
      IsProper jstr ∧ Smooth jstr ∧ GeometricallyConnected jstr ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          incl T g p = incl T g q → p = q) ∧
        (∀ (T' T : Scheme.{u}) (h : T' ⟶ T) (g : T ⟶ S) (g' : T' ⟶ S) (hg : h ≫ g = g')
          (p : RelPoint jstr g),
          incl T' g' (RelPoint.pre h hg p) = RelPoint.pre h hg (incl T g p)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S),
          ∃ z : RelPoint jstr g, incl T g z = hP.zeroPoint g) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p q : RelPoint jstr g),
          ∃ r : RelPoint jstr g, incl T g r = hP.addPoint (incl T g p) (incl T g q)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (p : RelPoint jstr g),
          ∃ r : RelPoint jstr g, incl T g r = hP.negPoint (incl T g p)) ∧
        (∀ (T : Scheme.{u}) (g : T ⟶ S) (x : RelPoint strX g),
          ∃ p : RelPoint jstr g, incl T g p = aj T g x) := by
  -- the two laws of `aj` that both halves need and the caller does not supply
  have hajpre := aj_pre_of_spec _hproper _hsmooth o hP aj _haj
  have hajbase := aj_base_of_spec _hproper _hsmooth o hP aj _haj
  obtain ⟨J, jstr, incl, hsm, hcn, hinj, hpre, hzero, hadd, hneg, himg⟩ :=
    exists_relPicIdentityComponent _hproper _hsmooth _hconn o hP _hpush _hPsmooth _hPsep
      _hequiv aj _haj hajpre hajbase
  exact ⟨J, jstr, incl,
    isProper_relPicIdentityComponent _hproper _hsmooth _hconn o hP _hpush _hPsmooth _hPsep
      _hequiv aj _haj hajpre hajbase incl hsm hcn hinj hpre hzero hadd hneg himg,
    hsm, hcn, hinj, hpre, hzero, hadd, hneg, himg⟩

/-- **`Pic⁰` IS AN ABELIAN SCHEME INSIDE `Pic`** (PROVEN 2026-07-31 over
`exists_relPicZeroSubfunctor` and the group axioms for `IsRelPicOf.addPoint`; a
sorry leaf from 2026-07-29 to 2026-07-31) — BLR 9.4/4's geometric half.

The whole proof is the transport of a group structure along an injection whose
image is a subgroup: `ab.add p q` is the unique preimage of
`hP.addPoint (incl p) (incl q)`, existing by the closure clause and unique by
`hinj`, and each of the nine remaining fields is `hinj` applied to a rewrite
chain that ends in the corresponding law on `Pic`.  Not one of them touches the
geometry, which is the point of the cut. -/
theorem exists_relPicZeroSubgroup {X P S : Scheme.{u}} {strX : X ⟶ S} {pstr : P ⟶ S}
    (_hproper : IsProper strX) (_hsmooth : SmoothOfRelativeDimension 1 strX)
    (_hconn : GeometricallyConnected strX) (o : RelPoint strX (𝟙 S))
    (hP : IsRelPicOf strX pstr)
    (_hpush : AlgebraicGeometry.HasUniversallyTrivialPushforward strX)
    (_hPsmooth : Smooth pstr) (_hPsep : IsSeparated pstr)
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
            ∃ p : RelPoint jstr g, incl T g p = aj T g x) := by
  obtain ⟨J, jstr, G, incl, hincl⟩ := exists_relPicZeroGroupScheme _hproper _hsmooth _hconn o hP
    _hpush _hPsmooth _hPsep _hequiv aj _haj
  exact ⟨J, jstr, G.toAbelianSchemeStruct (isProper_of_relPicZeroGroupScheme _hproper _hsmooth
    _hconn o hP _hpush _hPsmooth _hPsep _hequiv aj _haj G incl hincl), incl, hincl.1,
    hincl.2.1, hincl.2.2.1, hincl.2.2.2.1, hincl.2.2.2.2⟩

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
  obtain ⟨hPsmooth, hPsep⟩ :=
    smooth_isSeparated_of_isRelPicOf _hproper _hsmooth _hconn o hP _hpush
  obtain ⟨J, jstr, ab, incl, hinj, hzero, hadd, hpre, himg⟩ :=
    exists_relPicZeroSubgroup _hproper _hsmooth _hconn o hP _hpush hPsmooth hPsep
      _hequiv aj hajSpec
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
  obtain ⟨_P, _pstr, ⟨hP⟩, -, -⟩ := exists_relPicFull strX hproper hsmooth hconn o
  exact exists_relPicZero_of_isRelPicOf hproper hsmooth hconn o hP

/-! ## `𝒦_X`, AND `sectionIdeal` AS AN INVERTIBLE SUBSHEAF OF IT

**Why this section exists.**  `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal`
(`ModularCurve/X0.lean`) received a ROUTE CORRECTION on 2026-07-31 which took
Riemann–Roch, `h⁰` and base-point-free pencils OFF its critical path and
replaced them by three obligations.  Obligation (1) is this section, quoted
verbatim from that docstring:

> `sectionIdeal` is defined in `ModularCurve/RelativePicard.lean` as the KERNEL
> of an adjunction unit, not as an ideal inside `𝒦_X`, so "`𝒪(−x)` is
> invertible, sits inside the constant sheaf, and `modTensor` of two of them is
> the product ideal" has to be built before `f` can be extracted.  That is the
> real first step, and it belongs in `RelativePicard.lean`, not in a divisor
> theory.

**What it buys.**  On an INTEGRAL scheme a morphism between two invertible
subsheaves of `𝒦_X` is multiplication by a single element of `𝒦_X`, and an
ISOMORPHISM is multiplication by some `f ∈ 𝒦_Xˣ`.  So the `_hiso` hypothesis of
the `g¹₂` leaf HANDS THE RATIONAL FUNCTION BACK DIRECTLY, with
`div f = (x₁ + x₂) − (y₁ + y₂)`.  That is `D ∼ E ⟺ D − E = div f` in the
direction that consumes no cohomology; the `h⁰(D) ≥ 2` phrasing produces the
SAME `f` (as the pencil `⟨1, f⟩`) through strictly more machinery.
`exists_units_functionField_of_iso_sectionIdeal` at the end of this section is
that hand-back, and it is PROVEN over the three leaves below.

**THE CHECK THAT WOULD HAVE REFUTED THE WHOLE ROUTE — RUN, AND IT COMES BACK
NEGATIVE.**  The route correction named one: "an isomorphism of `sectionIdeal`s
that is NOT multiplication by a rational function — i.e. `sectionIdeal` failing
to be an invertible subsheaf of `𝒦_X`."  It does not fail, and the reason
makes obligation (1) cheaper than the correction supposed, because the SUBSHEAF
half is FREE and needs neither smoothness nor properness:

* `sectionIdeal σ` is by DEFINITION `ker (𝒪_Z ⟶ σ_*𝒪_T)`, so `kernel.ι` is a
  mono `sectionIdeal σ ⟶ 𝒪_Z` — it is an IDEAL sheaf, a subsheaf of `𝒪_Z`,
  unconditionally.  Kernels are monic in any category; nothing is assumed.
* `𝒪_X ⟶ 𝒦_X` is a mono as soon as `X` is INTEGRAL, because on a nonempty open
  it is `Scheme.germToFunctionField`, which mathlib proves injective
  (`Scheme.germToFunctionField_injective`).  That is `mono_toConstSheaf` below.
* Composing, `sectionIdeal σ ⟶ 𝒦_X` is a mono (`mono_sectionIdealToConst`,
  PROVEN here).  INVERTIBILITY is the separate, already-existing leaf
  `isInvertibleSheaf_sectionIdeal` above, which is where `_hproper` and
  `_hsmooth` are spent and which this section does not duplicate.

So obligation (1) splits into a free part and a part that was already a named
leaf, plus the genuinely new dictionary below.  **A prover should NOT treat
"is a subsheaf of `𝒦_X`" as new geometry; it is `kernel.ι` and integrality.**

**HOW `𝒦_X` IS BUILT, and why it is not a new theory.**  The constant sheaf is
the PUSHFORWARD OF `𝒪` ALONG THE GENERIC POINT,
`𝒦_X = g_* 𝒪_{Spec K}` with `g : Spec X.functionField ⟶ X` the canonical
`Scheme.fromSpecStalk` at `genericPoint X`.  Its sections over a nonempty `U`
are `Γ(𝒪_{Spec K}, g ⁻¹ᵁ U) = K` — `g ⁻¹ᵁ U` is all of the one-point space
`Spec K` — and `0` over `∅`, which is exactly the constant sheaf on an
irreducible space.  This costs no new construction: it is the SAME shape as
`sectionIdeal`'s own definition (pushforward along a point, unit of the
`pullback ⊣ pushforward` adjunction), so the module needs no divisor theory,
no `𝒪(D)` and no Cartier divisors — none of which exist at this pin.

Multiplication by `a ∈ K` is likewise pushed forward from `Spec K`
(`constSmul`), through the endomorphism of `𝒪_{Spec K}` that
`SheafOfModules.unitHomEquiv` attaches to a global section (`modUnitMul`).

**WHAT IS GENUINELY OPEN HERE — three leaves, and none of them is
Riemann–Roch.**  `mono_toConstSheaf` (`𝒪_X ↪ 𝒦_X` on an integral scheme),
`mono_modTensorToUnit` (the product-ideal map `I ⊗ J ⟶ 𝒪_X` is injective for
invertible ideal sheaves on an integral scheme) and `exists_constSmul_of_iso`
(THE dictionary: a morphism of invertible subsheaves of `𝒦_X` is multiplication
by an element of `𝒦_X`).  The first two are local statements about integral
schemes; the third is the generic-stalk argument written out in its own
docstring.  Everything else in this section is a definition or is proven.

**RESIDUAL OBLIGATION FOR THE CONSUMER, and it is NOT discharged here.**
`exists_units_functionField_of_iso_sectionIdeal` needs
`IsIntegral (curveBaseChange strX g)` — the base-changed curve must be
integral, which is what makes `𝒦` a field and every statement in this section
meaningful.  At `S = T = Spec ℚ` that follows from smooth (hence regular, hence
normal) plus geometrically connected plus nonempty, but it is a real step and
it belongs next to its consumer, not here. -/

/-- **THE GENERIC POINT, AS A MORPHISM OF SCHEMES** — `Spec K ⟶ X` for
`K = X.functionField`, i.e. mathlib's `Scheme.fromSpecStalk` at the generic
point.  This is the map along which `𝒦_X` is pushed forward. -/
noncomputable def genericPointHom (X : Scheme.{u}) [IrreducibleSpace X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- **THE CONSTANT SHEAF `𝒦_X`** — the pushforward of `𝒪_{Spec K}` along the
generic point, `K = X.functionField`.

`Γ(𝒦_X, U) = Γ(𝒪_{Spec K}, g ⁻¹ᵁ U)`, which is `K` for every nonempty `U`
(the preimage of a nonempty open under `g` is the whole one-point space) and
`0` for `U = ∅`.  On an irreducible space that presheaf is already a sheaf,
and it is the constant sheaf of rational functions. -/
noncomputable def constSheaf (X : Scheme.{u}) [IrreducibleSpace X] : X.Modules :=
  (Scheme.Modules.pushforward (genericPointHom X)).obj (modUnit _)

/-- **THE CANONICAL `𝒪_X ⟶ 𝒦_X`** — the unit of `g^* ⊣ g_*` at `𝒪_X`,
followed by `g_*` of `modPullbackUnitIso` (`g^*𝒪_X ≅ 𝒪_{Spec K}`).

Exactly the shape of `sectionIdeal`'s own defining map, with the section
`σ : T ⟶ Z` replaced by the generic point. -/
noncomputable def toConstSheaf (X : Scheme.{u}) [IrreducibleSpace X] :
    modUnit X ⟶ constSheaf X :=
  (Scheme.Modules.pullbackPushforwardAdjunction (genericPointHom X)).unit.app (modUnit X) ≫
    (Scheme.Modules.pushforward (genericPointHom X)).map (modPullbackUnitIso _).hom

/-- **A GLOBAL SECTION OF `𝒪_Z`, READ AS A COMPATIBLE FAMILY** — restrict `a`
from `⊤` to every open.  Compatibility is functoriality of the presheaf plus
the fact that `Opens Z` has at most one arrow between any two objects. -/
noncomputable def modUnitSections {Z : Scheme.{u}} (a : Γ(Z, ⊤)) : (modUnit Z).sections :=
  PresheafOfModules.sectionsMk (fun _ => Z.presheaf.map (homOfLE le_top).op a)
    (by
      intro U V f
      show Z.presheaf.map f (Z.presheaf.map (homOfLE le_top).op a) = _
      rw [← CategoryTheory.comp_apply, ← Z.presheaf.map_comp]
      congr 1)

/-- **MULTIPLICATION BY A GLOBAL SECTION**, as an endomorphism of `𝒪_Z`.

`SheafOfModules.unitHomEquiv` is the bijection `(𝒪 ⟶ M) ≃ M.sections`; taken
at `M = 𝒪` it turns a global section into the endomorphism "multiply by it". -/
noncomputable def modUnitMul {Z : Scheme.{u}} (a : Γ(Z, ⊤)) : modUnit Z ⟶ modUnit Z :=
  (modUnit Z).unitHomEquiv.symm (modUnitSections a)

/-- **`modTensor` IS FUNCTORIAL ON ARBITRARY MORPHISMS** — `modTensorMapIso`
without the inverse.

**HOISTED 2026-07-31 from `Modularity/AmpleSheaf.lean`**, where it was declared
(byte-identically) for `modPullbackTensorComparison`.  `AmpleSheaf.lean` imports
this module, so the two declarations would have collided — the same collision
`isInvertibleSheaf_modUnit` caused when it was duplicated.  Its companion
`modTensorMap_tensorSection` stays downstream, where its consumer is. -/
noncomputable def modTensorMap {Z : Scheme.{u}} {L L' M M' : Z.Modules}
    (e : L ⟶ L') (e' : M ⟶ M') : modTensor L M ⟶ modTensor L' M' :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
    (MonoidalCategory.tensorHom
      ((SheafOfModules.forget _).map e) ((SheafOfModules.forget _).map e'))

/-- **MULTIPLICATION BY `a ∈ K` ON `𝒦_X`** — push `modUnitMul` forward from
`Spec K`, where the global sections of the structure sheaf are `K` itself
(`Scheme.ΓSpecIso`).

This is the "multiplication by a rational function" of the route correction:
the payoff `exists_constSmul_of_iso` says an isomorphism of invertible
subsheaves of `𝒦_X` IS one of these. -/
noncomputable def constSmul {X : Scheme.{u}} [IrreducibleSpace X] (a : X.functionField) :
    constSheaf X ⟶ constSheaf X :=
  (Scheme.Modules.pushforward (genericPointHom X)).map
    (modUnitMul ((Scheme.ΓSpecIso X.functionField).inv a))

/-- **THE PRODUCT OF TWO IDEAL SHEAVES**, as a map `I ⊗ J ⟶ 𝒪_X`.

Tensor the two inclusions and use the left unitor `𝒪 ⊗ 𝒪 ≅ 𝒪`.  Its image is
the product ideal `IJ`; the pin has no ideal-sheaf image API, so what is
recorded about it here is the part that is used — that it is INJECTIVE
(`mono_modTensorToUnit`), which is what realises `I ⊗ J` as a subsheaf of
`𝒪_X ⊆ 𝒦_X`. -/
noncomputable def modTensorToUnit {X : Scheme.{u}} {L M : X.Modules}
    (ιL : L ⟶ modUnit X) (ιM : M ⟶ modUnit X) : modTensor L M ⟶ modUnit X :=
  modTensorMap ιL ιM ≫ (modTensorUnitLeftIso (modUnit X)).hom

/-- **`ι` REALISES `L` AS AN INVERTIBLE SUBSHEAF OF `𝒦_X`.**

Two clauses, deliberately not one: invertibility is about `L` and is proven
elsewhere (`isInvertibleSheaf_sectionIdeal`, `isInvertibleSheaf_modTensorPic`),
while monicity is about `ι` and is what "subsheaf" means.  The dictionary
`exists_constSmul_of_iso` needs BOTH — monicity to make `L_η ↪ K`, and
invertibility to make `L_η ≠ 0`, since a `K`-submodule of `K` is `0` or `K`
and only the second case gives a well-defined ratio. -/
def IsInvertibleSubsheaf {X : Scheme.{u}} [IrreducibleSpace X] {L : X.Modules}
    (ι : L ⟶ constSheaf X) : Prop :=
  IsInvertibleSheaf L ∧ Mono ι

/-! ### `𝒪_X ↪ 𝒦_X` on an integral scheme

**`mono_toConstSheaf` below is PROVEN**; this note is the audit written when it
was introduced as a leaf, kept because it records why integrality is the
hypothesis and what the two-line refutation is.  The four helpers between here
and it are its proof.

**`𝒪_X ↪ 𝒦_X`** is the one place integrality enters the subsheaf half of the
dictionary.

**Route, and it is short.**  A faithful functor reflects monomorphisms, and
`SheafOfModules.forget` is faithful, so it suffices to be monic in presheaves of
modules, where monicity is objectwise injectivity.  Over a nonempty `U` the map
`Γ(X, U) ⟶ Γ(𝒦_X, U) = Γ(𝒪_{Spec K}, g ⁻¹ᵁ U) = K` is
`Scheme.germToFunctionField U`, whose injectivity is
`Scheme.germToFunctionField_injective` (mathlib, for `[IsIntegral X]`); over
`∅` both sides are `0`.  The work is the IDENTIFICATION of the adjunction unit
with the germ map, not the injectivity.

**FAITHFULNESS.  `[IsIntegral X]` is load-bearing and cannot be weakened to
`[IrreducibleSpace X]`.**  On `X = Spec k[ε]/(ε²)` — irreducible, one point, so
`𝒦_X` is the stalk `k[ε]/(ε²)` and the map `𝒪_X ⟶ 𝒦_X` is the identity, which
IS monic, so that is not a counterexample.  Take instead
`X = Spec k[x,y]/(y², xy)`, whose reduction is a line: it is irreducible with
generic point the generic point of the line, `K = k(x)`, and the germ map kills
the embedded-primary component `y`, so `y ≠ 0` maps to `0` and `𝒪_X ⟶ 𝒦_X` is
NOT monic.  Reducedness is exactly what `IsIntegral` adds and exactly what
`germ_injective_of_isIntegral` uses.

**NOT VACUOUS.**  Every smooth proper geometrically connected curve over a
field is integral, which is the situation every consumer of this section is in.

**PROVEN 2026-07-31**, exactly along the route above and over the four helpers
immediately below.  Cost: about forty lines, no new mathematics, and the
identification that made it short is `toConstSheaf_eq` — the composite
`unit ≫ g_*(g^*𝒪 ≅ 𝒪)` defining `toConstSheaf` IS mathlib's
`SheafOfModules.unitToPushforwardObjUnit`, whose sections map is `g^♯` by
`rfl`.  So no adjunction had to be unwound by hand. -/

/-- **THE PREIMAGE OF A NONEMPTY OPEN UNDER THE GENERIC POINT IS EVERYTHING**
(PROVEN) — `Spec K` is a one-point space for `K` a field, and that point goes
to the generic point (`Scheme.fromSpecStalk_closedPoint`), which lies in every
nonempty open. -/
theorem preimage_genericPointHom_eq_top (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    [Nonempty U] : (genericPointHom X) ⁻¹ᵁ U = ⊤ := by
  haveI : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  rw [eq_top_iff]
  intro p _
  show (genericPointHom X).base p ∈ U
  have hp : p = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  subst hp
  rw [show (genericPointHom X).base (IsLocalRing.closedPoint X.functionField) = genericPoint X from
    Scheme.fromSpecStalk_closedPoint]
  exact hη

/-- **RESTRICTION TO AN OPEN THAT IS KNOWN TO BE `⊤` IS INJECTIVE** (PROVEN) —
after substituting the equation the map is `𝟙`.  Stated with the equation as a
hypothesis rather than by rewriting at the use site, because rewriting `V = ⊤`
inside `presheaf.map (homOfLE le_top : V ⟶ ⊤).op` changes the TYPE of the
morphism and drags `eqToHom` through the whole proof. -/
theorem injective_res_of_eq_top {Z : Scheme.{u}} (V : Z.Opens) (hV : V = ⊤) :
    Function.Injective (Z.presheaf.map (homOfLE le_top : V ⟶ ⊤).op) := by
  subst hV
  rw [Subsingleton.elim (homOfLE le_top : (⊤ : Z.Opens) ⟶ ⊤) (𝟙 _)]
  intro a b h
  simpa using h

/-- **`g^♯` IS INJECTIVE ON A NONEMPTY OPEN** (PROVEN) — this is where
integrality is spent, through mathlib's `germ_injective_of_isIntegral`.

`Scheme.fromSpecStalk_app` factors `g.app U` as
`germ ≫ (ΓSpecIso K).inv ≫ restriction`, and all three factors are injective:
the germ by integrality, the middle by being an isomorphism, and the
restriction by `injective_res_of_eq_top` at
`preimage_genericPointHom_eq_top`. -/
theorem injective_genericPointHom_app (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    [Nonempty U] : Function.Injective ((genericPointHom X).app U) := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have happ : (genericPointHom X).app U =
      X.presheaf.germ U (genericPoint X) hη ≫
        (Scheme.ΓSpecIso X.functionField).inv ≫
          (Spec X.functionField).presheaf.map (homOfLE le_top).op :=
    Scheme.fromSpecStalk_app hη
  rw [happ]
  intro a b hab
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hab
  refine germ_injective_of_isIntegral X (genericPoint X) hη ?_
  refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).inv).1 ?_
  exact injective_res_of_eq_top _ (preimage_genericPointHom_eq_top X U) hab

/-- **`toConstSheaf` IS mathlib's `unitToPushforwardObjUnit`** (PROVEN) — the
identification that makes `mono_toConstSheaf` short.

`toConstSheaf` is written as `η ≫ g_*(g^*𝒪_X ≅ 𝒪_{Spec K})`, which is the
adjunction transpose of `pullbackObjUnitToUnit`; mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` says that
transpose is `unitToPushforwardObjUnit`, whose value on sections is `g^♯`
BY `rfl` (`unitToPushforwardObjUnit_val_app_apply`).  So the sections
description costs no unwinding of the adjunction at all. -/
theorem toConstSheaf_eq (X : Scheme.{u}) [IrreducibleSpace X] :
    toConstSheaf X =
      SheafOfModules.unitToPushforwardObjUnit (genericPointHom X).toRingCatSheafHom := by
  rw [← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    Adjunction.homEquiv_unit]
  rfl

/-- **`𝒪_X ↪ 𝒦_X` ON AN INTEGRAL SCHEME** (PROVEN 2026-07-31) — the audit,
including the two witnesses showing `[IsIntegral X]` cannot be weakened to
`[IrreducibleSpace X]`, is the section note above. -/
theorem mono_toConstSheaf (X : Scheme.{u}) [IsIntegral X] : Mono (toConstSheaf X) := by
  refine (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map ?_
  refine PresheafOfModules.mono_of_injective ?_
  intro V a b hab
  by_cases hne : Nonempty V.unop
  · haveI := hne
    rw [toConstSheaf_eq] at hab
    exact injective_genericPointHom_app X V.unop hab
  · have hbot : V.unop = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨⟨x, hx⟩⟩
    have hs : Subsingleton Γ(X, V.unop) := hbot ▸ inferInstance
    exact hs.elim a b

/-- **`𝒪(−σ) ⊆ 𝒦_X`** — the ideal sheaf of a section, read inside the constant
sheaf. -/
noncomputable def sectionIdealToConst {Z T : Scheme.{u}} [IrreducibleSpace Z] (σ : T ⟶ Z) :
    sectionIdeal σ ⟶ constSheaf Z :=
  kernel.ι _ ≫ toConstSheaf Z

/-- **`𝒪(−σ)` IS A SUBSHEAF OF `𝒦_Z`** (PROVEN) — and this is the half of
obligation (1) that is FREE.

`sectionIdeal σ` is a KERNEL, so `kernel.ι` is monic with no hypotheses at all;
compose with `mono_toConstSheaf`.  Neither `IsProper` nor
`SmoothOfRelativeDimension 1` appears: those are spent on INVERTIBILITY
(`isInvertibleSheaf_sectionIdeal`), which is a different statement.

`mono_comp` is applied by hand rather than by instance search because the
`HasKernel` instance inside `sectionIdeal`'s definition and the one instance
search reconstructs are defeq but not syntactically equal, so the search for
`Mono (kernel.ι …)` fails while `equalizer.ι_mono` at the goal's own
instantiation succeeds. -/
theorem mono_sectionIdealToConst {Z T : Scheme.{u}} [IsIntegral Z] (σ : T ⟶ Z) :
    Mono (sectionIdealToConst σ) := by
  refine @mono_comp _ _ _ _ _ _ ?_ _ (mono_toConstSheaf Z)
  exact equalizer.ι_mono

/-- **`𝒪(−σ − τ) ⊆ 𝒦_Z`** — the product of two section ideals, read inside the
constant sheaf.  This is the sheaf the `g¹₂` leaf's `_hiso` compares. -/
noncomputable def sectionIdealPairToConst {Z T : Scheme.{u}} [IrreducibleSpace Z]
    (σ τ : T ⟶ Z) : modTensor (sectionIdeal σ) (sectionIdeal τ) ⟶ constSheaf Z :=
  modTensorToUnit (kernel.ι _) (kernel.ι _) ≫ toConstSheaf Z

/-- **THE PRODUCT-IDEAL MAP IS INJECTIVE** (sorry leaf, 2026-07-31) — for two
INVERTIBLE ideal sheaves on an INTEGRAL scheme, `I ⊗ J ⟶ 𝒪_X` is monic, so
`I ⊗ J` is again a subsheaf of `𝒪_X` (namely the product ideal `IJ`).

**Route.**  Monicity is local, and both sheaves are locally trivial: near any
point choose `U` on which `I|_U ≅ 𝒪_U` and `J|_U ≅ 𝒪_U`, with the inclusions
becoming multiplication by sections `a, b ∈ Γ(X, U)`.  Then `(I ⊗ J)|_U ≅ 𝒪_U`
and the map is multiplication by `ab`.  On an INTEGRAL scheme `Γ(X, U)` is a
domain and `a, b ≠ 0` (they are nonzero because `I`, `J` are nonzero subsheaves
of `𝒪`), so `ab ≠ 0` and multiplication by it is injective.

**FAITHFULNESS.  Every hypothesis is load-bearing.**

* Drop integrality: over `X = Spec k[x,y]/(xy)` take `I = (x)`, `J = (y)`.  Both
  are invertible on the two components separately, `I ⊗ J` is nonzero, and the
  product map is zero, so it is not monic.  A nonzerodivisor hypothesis is
  exactly what a domain supplies.
* Drop invertibility of `J`: for `X` a smooth affine surface and `J = 𝔪` the
  maximal ideal at a point, `I = 𝒪`, the map `𝒪 ⊗ 𝔪 ⟶ 𝒪` is monic — so this
  particular drop is not refuted by that witness; invertibility is used to make
  the LOCAL model available at all, and without it `I ⊗ J` has torsion at the
  points where the ideals are not principal and the map kills it.  The standard
  witness is `X = Spec k[x,y]`, `I = J = (x, y)`: `I ⊗ J` has a torsion element
  `x ⊗ y − y ⊗ x ≠ 0` that maps to `xy − yx = 0`.

**NOT VACUOUS.**  Satisfied by `I = J = 𝒪`, and by the pair of section ideals
of any two sections of a smooth proper relative curve — which is the only place
it is consumed. -/
theorem mono_modTensorToUnit {X : Scheme.{u}} [IsIntegral X] {L M : X.Modules}
    {ιL : L ⟶ modUnit X} {ιM : M ⟶ modUnit X} (_hL : IsInvertibleSheaf L)
    (_hM : IsInvertibleSheaf M) (_hιL : Mono ιL) (_hιM : Mono ιM) :
    Mono (modTensorToUnit ιL ιM) := sorry

/-- **THE DICTIONARY: AN ISOMORPHISM OF INVERTIBLE SUBSHEAVES OF `𝒦_X` IS
MULTIPLICATION BY AN ELEMENT OF `𝒦_Xˣ`** (sorry leaf, 2026-07-31) — obligation
(1) of the `g¹₂` route correction, and the statement that removes Riemann–Roch
from `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal`.

**Route — the generic stalk, and nothing else.**  Write `η` for the generic
point and `K = X.functionField = 𝒪_{X,η}`.  Taking stalks at `η` is exact, so

* `ιL` monic gives an injection of `K`-modules `L_η ↪ (𝒦_X)_η = K`, whose image
  is a `K`-submodule of `K`, hence `0` or `K`;
* `L` invertible gives `L_η ≅ 𝒪_{X,η} = K ≠ 0`, so the image is `K` and
  `(ιL)_η` is an ISOMORPHISM onto `K`; likewise for `M`;
* put `f := (ιM)_η (e_η ((ιL)_η⁻¹ 1)) ∈ K`.  Then `(ιM)_η ∘ e_η = f · (ιL)_η`
  by `K`-linearity, and `f ∈ Kˣ` because the same construction applied to
  `e.symm` gives `g` with `fg = 1`.
* Finally the identity of MORPHISMS follows from the identity on the generic
  stalk, because `Γ(𝒦_X, U) ⟶ (𝒦_X)_η` is injective for every `U` — it is the
  identity of `K` for `U` nonempty and `0 ⟶ K` for `U = ∅`.  This is the one
  step that uses what `𝒦_X` IS rather than that it is a sheaf.

**FAITHFULNESS.  This was the check named as able to refute the whole route
correction, and it comes back NEGATIVE — with both hypotheses load-bearing.**

* Drop `Mono ιL` and it is FALSE: take `ιL = 0` with `L = 𝒪_X` and `M = 𝒪_X`,
  `ιM = ` the canonical inclusion, `e = Iso.refl`.  Then `e ≫ ιM ≠ 0 = ιL ≫ c`
  for every `c`, since `ιM` is monic and nonzero.  Without monicity there is no
  ratio to speak of.
* Drop `IsInvertibleSheaf L` and it is FALSE: the generic stalk can vanish.  On
  `X = Spec ℤ` let `L` be the kernel of `𝒪 ⟶ 𝒪/(p)`… which is invertible, so
  instead take `L` the SKYSCRAPER `(p)/(p²)` at `(p)`, `ιL = 0` — already
  covered — or, keeping `ιL` monic, note that no monic `ι` out of a torsion
  sheaf exists into `𝒦_X` at all, so the honest statement of what invertibility
  buys is `L_η ≠ 0`: the hypothesis could be weakened to that, and is left as
  invertibility because that is what both call sites have in hand
  (`isInvertibleSheaf_sectionIdeal`, `isInvertibleSheaf_modTensorPic`).
* Drop `[IsIntegral X]` and `X.functionField` is not a field, `L_η ↪ K` has no
  submodule dichotomy, and the ratio need not exist: on
  `X = Spec k[x,y]/(xy)` (not irreducible, so not even statable) or on a
  non-reduced irreducible `X` the germ map is not injective and `𝒦_X` is not a
  constant sheaf of fields.

**NOT VACUOUS, and not `Iso`-trivial.**  `L = M = 𝒪_X` with `ιL = ιM` the
canonical inclusion and `e = Iso.refl` gives `f = 1`; and the content is real
because for `L = 𝒪(−x)`, `M = 𝒪(−y)` on a curve with `x ∼ y` the `f` produced
is a nonconstant rational function with `div f = x − y`, which is exactly what
the consumer extracts. -/
theorem exists_constSmul_of_iso {X : Scheme.{u}} [IsIntegral X] {L M : X.Modules}
    {ιL : L ⟶ constSheaf X} {ιM : M ⟶ constSheaf X}
    (_hL : IsInvertibleSubsheaf ιL) (_hM : IsInvertibleSubsheaf ιM) (e : L ≅ M) :
    ∃ f : X.functionFieldˣ, e.hom ≫ ιM = ιL ≫ constSmul (f : X.functionField) :=
  sorry

/-- **THE HAND-BACK: AN ISOMORPHISM `𝒪(−x₁−x₂) ≅ 𝒪(−y₁−y₂)` IS MULTIPLICATION
BY A RATIONAL FUNCTION** (PROVEN 2026-07-31 over the three leaves above) — the
export obligation (1) of the `g¹₂` route correction asks for, in the form its
consumer `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal` can use.

Given the isomorphism that leaf receives as `_hiso`, this produces
`f ∈ K(X_T)ˣ` with `f · 𝒪(−x₁−x₂) = 𝒪(−y₁−y₂)` inside `𝒦`, i.e. classically
`div f = (x₁ + x₂) − (y₁ + y₂)`.  **No cohomology, no `h⁰`, no linear system
and no pencil is involved**, which is the whole point of the correction: the
`h⁰(D) ≥ 2` phrasing produces the same `f` through strictly more machinery.

**WHAT REMAINS FOR THE CONSUMER after this**, and neither is here: obligation
(2), that `f` restricted to `X ∖ {y₁, y₂}` is a finite morphism to `𝔸¹`
(proper + quasi-finite + separated, by the valuative criterion already in
`Mathlib/AlgebraicGeometry/…/CurveExtension.lean`), and obligation (3), the
degree theorem `deg (div g) = 0` for a nonconstant `g` on a smooth proper
curve, which is shared with
`card_relPoint_not_liesIn_le_of_finite_toAffineLine`.

**THE FOUR DISJOINTNESS INEQUALITIES ARE NOT NEEDED HERE** and are deliberately
absent from the statement: they are what makes `div f ≠ 0` and pins the polar
divisor to `(y₁) + (y₂)` with no cancellation, which is obligation (2)'s
business.  Passing them in would make this lemma look like it used them.

**`[IsIntegral (curveBaseChange strX g)]` is an instance argument, not a
derived fact.**  It is the residual obligation named in this section's header:
the consumer must supply it, and at `S = T = Spec ℚ` it follows from smooth
(hence regular, hence normal) + geometrically connected + nonempty.  It is not
discharged here because the derivation belongs next to the curve hypotheses,
in `X0.lean`, not in a module about `Pic`. -/
theorem exists_units_functionField_of_iso_sectionIdeal {X S T : Scheme.{u}} {strX : X ⟶ S}
    (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX) {g : T ⟶ S}
    [IsIntegral (curveBaseChange strX g)] (x₁ x₂ y₁ y₂ : RelPoint strX g)
    (e : modTensor (sectionIdeal (relSection x₁)) (sectionIdeal (relSection x₂)) ≅
      modTensor (sectionIdeal (relSection y₁)) (sectionIdeal (relSection y₂))) :
    ∃ f : (curveBaseChange strX g).functionFieldˣ,
      e.hom ≫ sectionIdealPairToConst (relSection y₁) (relSection y₂) =
        sectionIdealPairToConst (relSection x₁) (relSection x₂) ≫ constSmul (f : _) := by
  have key : ∀ z₁ z₂ : RelPoint strX g,
      IsInvertibleSubsheaf (sectionIdealPairToConst (relSection z₁) (relSection z₂)) := by
    intro z₁ z₂
    refine ⟨isInvertibleSheaf_modTensorPic (isInvertibleSheaf_sectionIdeal hproper hsmooth z₁)
      (isInvertibleSheaf_sectionIdeal hproper hsmooth z₂), ?_⟩
    refine @mono_comp _ _ _ _ _ _ ?_ _ (mono_toConstSheaf _)
    exact mono_modTensorToUnit (isInvertibleSheaf_sectionIdeal hproper hsmooth z₁)
      (isInvertibleSheaf_sectionIdeal hproper hsmooth z₂) equalizer.ι_mono equalizer.ι_mono
  exact exists_constSmul_of_iso (key x₁ x₂) (key y₁ y₂) e

end Fermat
