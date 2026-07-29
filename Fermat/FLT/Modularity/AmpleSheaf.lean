/-
Modularity/AmpleSheaf.lean — own work for the Fermat project (not vendored
from the FLT project).

# Tensor powers, non-vanishing loci and AMPLE sheaves of modules

This module exists for exactly one consumer: the leaf
`isQuasiAffine_ker_mulByNat_of_isAlgClosed` in
`Modularity/AbelianSchemeIsogeny.lean` — "`ker[p]` is a quasi-affine scheme
over an algebraically closed field of characteristic `p`", the residue of
"`[p]` is an isogeny", classically proved by Mumford *Abelian Varieties* §6,
Application 2 of the THEOREM OF THE CUBE.

## Why this module exists now, and did not before

That leaf's docstring carried, until 2026-07-27, a recorded verdict that the
cut below was **not available**:

> the operative fact is stronger and it is what decides feasibility: **there
> is no monoidal structure on sheaves of modules over a scheme, so `L^{⊗n}`
> cannot even be WRITTEN.** … stating the interface faithfully means defining
> tensor powers of invertible sheaves — a mathlib-scale build (monoidal
> `SheafOfModules`, then invertibility, then ampleness), not a task-scale one.

The first clause of that verdict is now **FALSE**, and the refuting check is
one grep: `Fermat.modTensor` in `ModularCurve/RelativePicard.lean` supplies the
object part of the tensor product of two `𝒪_Z`-modules, by SHEAFIFYING the
presheaf tensor product (`PresheafOfModules.Monoidal.tensorObj` — the pin does
have a monoidal structure on *presheaves* of modules).  Together with
`Fermat.modPullback` (a wrapper on `Scheme.Modules.pullback`) and
`Fermat.IsInvertibleSheaf`, that is enough to WRITE `L^{⊗n}`, `[n]^* L`, and
hence the cube's output `[n]^* L ≅ L^{⊗ n²}`.  The remaining
statement-level gap was **ampleness**, and this module closes it: see
`IsAmpleSheaf` below, whose plumbing was verified to elaborate on 2026-07-27.

The verdict's *conclusion* — that this is a theory build and not a task — is
unchanged and is not disputed here.  What changed is that the theory is now a
list of NAMED LEAVES with honest statements, instead of a wall.

## What is proven here and what is left open

**Update 2026-07-27 (second pass).  All six of the original sheaf-theoretic
leaves are now PROVEN**, on top of four smaller named ones.  The route that
closed them is worth recording, because it refutes a second recorded verdict:

> `modTensor` is deliberately object-only … the ASSOCIATOR is the genuinely
> missing piece, and it is the statement that sheafification is monoidal.

Only the last clause survives.  `PresheafOfModules (R ⋙ forget₂ CommRingCat
RingCat)` is a **full symmetric monoidal category at this pin**
(`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` — `tensorHom`,
associator, both unitors, braiding), and `PresheafOfModules.sheafification` is
a **left adjoint whose counit is an iso** (`sheafificationAdjunction`, plus the
`IsIso` instance in `Presheaf/Sheafification.lean`).  Consequently:

* FUNCTORIALITY of `modTensor` is free — `modTensorMapIso` below;
* both UNITORS are free — `a(𝟙 ⊗ M) ≅ a(M) ≅ M`; only the left one is kept
  (`modTensorUnitLeftIso`), since nothing here consumes the right one and this
  project does not allow free-floating declarations;
* the ASSOCIATOR is *not*, and is the only one of the three that is a real
  theorem.

**Update 2026-07-28.  `nonempty_modTensor_assoc` is now PROVEN**, by the route
its own docstring named and called untried: `PresheafOfModules.sheafification`
is a LOCALIZATION functor (`ModuleCat/Sheaf/Localization.lean`), so
`CategoryTheory.LocalizedMonoidal` transports the presheaf-level monoidal
structure to `Z.Modules` as soon as the inverted class `modLocW Z` is
compatible with `⊗`.  That compatibility is `MorphismProperty.IsMonoidal`, its
right-whiskering half follows from its left-whiskering half by the braiding,
and what was left was ONE leaf, `modLocW_whiskerLeft` — TENSORING PRESERVES
LOCAL ISOMORPHISMS.

**Update 2026-07-28 (fourth pass).  `modLocW_whiskerLeft` is now PROVEN**, so
`MorphismProperty.IsMonoidal (modLocW Z)` and with it the whole localized
monoidal structure are unconditional.  The proof is elementary and lives in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/MonoidalW.lean`, stated
for an arbitrary site: neither of the two theories the old docstring named as
prerequisites (`MonoidalClosed (PresheafOfModules R)`; a monoidal stalk functor)
is needed.  What is needed is the EQUATIONAL CRITERION FOR VANISHING without
mathlib's "the `mᵢ` generate `M`" hypothesis, which that file supplies as
`Fermat.SheafificationMonoidal.exists_relations`.

Similarly, `nonempty_modPullback_modUnit` turned out to be **free from the
pin**, contradicting the recorded note that finality of `Opens.map f` "is not
automatic".  It *is* automatic: `StructuredArrow U (Opens.map g)` has `⊤` as a
TERMINAL object (`U ≤ f ⁻¹ᵁ ⊤` always), hence is connected, hence
`(Opens.map g).Final`, hence `SheafOfModules.pullbackObjUnitToUnit` is an
isomorphism by mathlib's own instance.  See `opensMapFinal` below.

PROVEN (free from the pin): `modPullbackCompIso`, `modPullbackCongrIso`,
`modPullbackMapIso` — pseudo-functoriality of `modPullback`, straight off
`Scheme.Modules.pullbackComp` / `pullbackCongr` / `Functor.mapIso`.

PROVEN here, in the tensor/ampleness API: `modTensorMapIso`,
`modTensorUnitLeftIso`, `modTensorPowMapIso`,
`modTensorPowUnitIso`, `modPullbackUnitIso`, `trivializedSection_of_iso`,
`nonvanishingAt_of_iso`, `nonvanishingLocus_of_iso`, `unitEndoApply_eq`,
`trivializedSection_restrictUnitIso`, `trivializedSection_trans`,
`nonvanishingLocus_modUnit` (the transition-function computation, which was the
only remaining obligation of `isQuasiAffine_of_isAmpleSheaf_modUnit`), and —
derived from the four leaves below — all six original statements
(`isAmpleSheaf_of_iso`, `isAmpleSheaf_modTensorPow`, `isAmpleSheaf_modPullback`,
`isQuasiAffine_of_isAmpleSheaf_modUnit`, `nonempty_modPullback_modTensorPow`,
`nonempty_modPullback_modUnit`).

**Update 2026-07-28 (third pass).**  Two of those four are now PROVEN, over a
TRIVIALIZATION CALCULUS (`§ Restriction of a trivialization` and
`§ Well-definedness` below) and four smaller named leaves.  The headline is a
FAITHFULNESS VERDICT that had been recorded as an open risk:

> **`nonvanishingLocus_modPullback_of_isAmpleSheaf` and `exists_tensorPowSection`
> are BOTH FAITHFUL AS STATED.  The numerical-semigroup worry is real, and it
> does not make either statement false; it is bridged by the classical theorem
> that an INVERTIBLE sheaf of modules is LOCALLY FREE OF RANK ONE (Stacks 01CV,
> Hartshorne II.6.12), isolated here as the single leaf
> `exists_trivialization_of_modTensorPow`.**

The reasoning is written out at `isInvertibleSheaf_of_isAmpleSheaf`.  Two
consequences of the verdict are worth pulling forward, because they change what
a prover should do:

* `exists_tensorPowSection`'s `V` and `hloc` turn out to be **inert** — the
  statement `nonvanishingLocus (A^{⊗k}) (s^{⊗k}) = nonvanishingLocus A s` is
  true with no hypothesis on `A` at all (`nonvanishingLocus_tensorPowSection`),
  and `exists_tensorPowSection` is a one-line corollary.  The FAITHFULNESS note
  that used to stand on it — "a version stated without `V` and `hloc` should be
  treated as unproven-and-suspect" — was right that `hloc` is not what saves the
  `⊆` direction, and wrong that anything is lost by dropping it: Stacks 01CV is
  what saves it, and it needs no `V`.
* `nonvanishingLocus_modPullback_of_isAmpleSheaf` needs **neither**
  `[IsClosedImmersion f]` **nor** `hn` **nor** `hV`.  Basic opens pull back along
  ANY morphism of schemes (`Scheme.preimage_basicOpen`), so the residue-field
  argument the closed immersion was there to supply is not needed.  The three
  hypotheses are kept (they cost the consumer nothing and removing them would
  churn the call site) but the unused ones are underscore-prefixed.

OPEN.  `modLocW_whiskerLeft` — SHEAFIFICATION IS MONOIDAL — used to head this
list; it is PROVEN as of 2026-07-28, and with it every associativity statement
in the module (`nonempty_modTensor_assoc`, `nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, `isAmpleSheaf_modTensorPow`).  What remains is
listed below, with the entries that have since been PROVEN kept in place for
the notes they carry — read the `PROVEN` marks, not a count.  One is an
original leaf:

* `exists_modPullback_modTensor` — monoidality of `f^*` on objects.  With
  `modPullbackUnitIso` proven, this is all that
  `nonempty_modPullback_modTensorPow` needs, and — through
  `nonempty_restrict_modTensor`, which is derived from it in three lines — it is
  also the only input the whole trivialization calculus has left.

  **RESTATED 2026-07-28**: it was `nonempty_modPullback_modTensor`, a bare
  `Nonempty`, which pins no isomorphism at all — post-composing a witness with
  multiplication by a unit of `Γ(X, ⊤)` satisfies every clause while scaling
  every trivialized section.  It now carries the section identity
  `f^*(a ⊗ b) = f^*a ⊗ f^*b`, which is what the trivialization calculus needs
  and what the old form could not supply.  `nonempty_modPullback_modTensor`
  survives as a PROVEN corollary, so no consumer changed.  Its docstring also
  carries a rewritten ROUTE AUDIT naming the four pin declarations that build
  the canonical comparison map.

The rest came out of the trivialization calculus, each strictly smaller than the
leaf it came out of:

* `exists_trivialization_of_modTensorPow` — **the mathematical one**: Stacks
  01CV, the semigroup bridge.  It is the only entry in this list that is not
  bookkeeping.
* `exists_trivialization_tensorPow` — `s^{⊗k}` read through the `k`-th power of
  a trivialization is the `k`-th power of the trivialized section.  **PROVEN
  2026-07-28**, by induction, over ONE new leaf `exists_trivialization_modTensor`
  ("a trivialization of a tensor product multiplies sections").  That cut is a
  CORRECTION: the route recorded here relied on reading `trivializedSection`
  through the anonymous iso supplied by `nonempty_restrict_modTensor`, which pins
  nothing — see that leaf's docstring for the unit-scaling counterexample.
* `exists_trivialization_modTensor` — the new leaf just described.
* `exists_trivialization_modPullback` — the same for `f^*`.  **PROVEN 2026-07-28**
  over a five-lemma calculus for the pullback of a global section through the
  canonical comparison isomorphisms, and a `trivializationOfPullback` that is now
  real code rather than an `∃`.  See `trivializedSection_trivializationOfPullback`.
* `trivializedSection_trivializationOfLE` — **PROVEN 2026-07-28.**  It was never
  mathematics; it was blocked by `modRestrictLEIso` being routed through
  `modPullback`.  Rerouting that through mathlib's `restrictFunctorCongr` +
  `restrictFunctorComp` (both `app`s are `rfl`) closed it.  Two owners found
  exactly this reroute independently and wrote the SAME definition; the proof
  kept here is the one that was already on `main`.

**Update 2026-07-28 (Picard block).**  The compiler's warning set for this
module is SEVEN, not six: the Picard-group block at the end of the file added
one.  It is `exists_modDual` — the dual sheaf `L^∨` together with its
evaluation pairing `L ⊗ L^∨ ⟶ 𝒪_Z`, asked for only up to LOCAL isomorphy of
that one global map.  `exists_modTensor_inverse`, which is what the relative
Picard calculus and `ModularCurve/X0.lean` actually consume, is PROVEN from it
in three lines through `isIso_of_locally_isIso` (isomorphy of a morphism of
`𝒪_Z`-modules is local on the base — proven here from stalks).  Read
`exists_modDual`'s docstring before attacking it: it records that mathlib has
no internal `Hom` on (pre)sheaves of modules at this pin, that the "just glue
the inverse cocycle" route is NOT cheap (mathlib's `Sites/Descent/IsStack.lean`
has no instances, so `Scheme.Modules` is not known to be a stack), and which
construction does avoid both obstructions.

## A note on the definition of ampleness

`NonvanishingAt L s z` is stated through the LOCAL TRIVIALIZATIONS of `L`
rather than through stalks, because `Scheme.Modules` has no `Module` structure
on stalks at this pin (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` has
`stalkFunctor` only through the underlying `Ab`-presheaf).  The `∃`
formulation is FAITHFUL without any well-definedness lemma: if `s` generates
`L` at `z` then every trivialization near `z` witnesses it, and conversely a
trivialization sending `s` to a unit at `z` exhibits `s` as a generator.  The
well-definedness IS needed to *prove* things about the locus, which is why it
is named above as an obligation of
`isQuasiAffine_of_isAmpleSheaf_modUnit` rather than smuggled into the
definition.
-/
module

public import Fermat.FLT.ModularCurve.RelativePicard
public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalW
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open TopologicalSpace MonoidalCategory Opposite

namespace Fermat

/-! ### Tensor powers -/

/-- **Tensor powers of an `𝒪_Z`-module**, `L^{⊗n}`, right-nested onto the
unit: `L^{⊗0} = 𝒪_Z` and `L^{⊗(n+1)} = L ⊗ L^{⊗n}`.

This is the object that the verdict quoted in the module docstring said could
not be written.  It can, because `modTensor` exists. -/
noncomputable def modTensorPow {Z : Scheme.{u}} (L : Z.Modules) : ℕ → Z.Modules
  | 0 => modUnit Z
  | (n + 1) => modTensor L (modTensorPow L n)

/-! ### Non-vanishing loci -/

/-- **A global section of `L`, read through a trivialization of `L` over `U`,
as an element of `Γ(U, 𝒪)`.**

The three steps are: restrict `s` from `⊤` to `U.ι ''ᵁ ⊤`, transport across
`Scheme.Modules.restrictAppIso` into the sections of `L|_U`, and apply the
trivialization.  The last identification — sections of `modUnit U` ARE
sections of `𝒪_U` — is definitional at this pin, which is why no coercion
appears. -/
noncomputable def trivializedSection {Z : Scheme.{u}} {L : Z.Modules} {U : Z.Opens}
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(L, ⊤)) : Γ((U : Scheme.{u}), ⊤) :=
  φ.hom.val.app (.op ⊤)
    ((Scheme.Modules.restrictAppIso (f := U.ι) L ⊤).inv
      (L.presheaf.map (homOfLE le_top).op s))

/-- **`s` does not vanish at `z`**: some neighbourhood of `z` trivializes `L`
in such a way that `s` becomes a unit at `z`.

See the module docstring for why this `∃` form is faithful with no
well-definedness lemma, and why stalks are not used. -/
def NonvanishingAt {Z : Scheme.{u}} (L : Z.Modules) (s : Γ(L, ⊤)) (z : Z) : Prop :=
  ∃ (U : Z.Opens) (hz : z ∈ U) (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})),
    (⟨z, hz⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s)

/-- **The non-vanishing locus `Z_s` of a global section**, as a bare set.

It is open — a union of images of basic opens — but the openness proof is not
needed anywhere below, because `IsAmpleSheaf` names the affine open
separately and only asks that the locus EQUAL it. -/
def nonvanishingLocus {Z : Scheme.{u}} (L : Z.Modules) (s : Γ(L, ⊤)) : Set Z :=
  {z | NonvanishingAt L s z}

/-! ### Ampleness -/

/-- **`L` is AMPLE**: every point lies in the non-vanishing locus of a global
section of some positive tensor power of `L`, and that locus is affine.

This is the classical definition (EGA II 4.5.3 / Hartshorne II.7.4 for a
quasi-compact separated scheme), and it is the hypothesis under which
EGA II 5.1.2 says that a scheme with ample structure sheaf is quasi-affine.

**Not vacuous.**  `IsAmpleSheaf` is satisfiable: on an affine `Z` the unit
section of `modTensorPow (modUnit Z) 1` has non-vanishing locus `⊤`.  It is
also not trivially satisfiable — for `Z` proper over a field and of positive
dimension, `IsAmpleSheaf (modUnit Z)` is FALSE, which is precisely why the
consumer's leaf carries content. -/
def IsAmpleSheaf {Z : Scheme.{u}} (L : Z.Modules) : Prop :=
  ∀ z : Z, ∃ (n : ℕ) (_ : 0 < n) (s : Γ(modTensorPow L n, ⊤)) (V : Z.Opens),
    z ∈ V ∧ IsAffineOpen V ∧ nonvanishingLocus (modTensorPow L n) s = (V : Set Z)

/-! ### HOISTED to `ModularCurve/RelativePicard.lean` (2026-07-28)

The pseudo-functoriality of `modPullback`, the presheaf monoidal structure,
`modSheafifyValIso`, `modTensorMapIso`, `modTensorUnitLeftIso`, `opensMapFinal`,
`modPullbackUnitIso`, `modRestrictPullbackIso`, `modRestrictLEIso`,
`trivializationOfLE` and `isInvertibleSheaf_modUnit`
were declared HERE and are now declared in `RelativePicard.lean`, unchanged, and
inherited by import.  They had to move because `RelativePicard.lean`'s two
representability leaves consume them and it is UPSTREAM of this module; the
collision that revealed it was `Fermat.isInvertibleSheaf_modUnit` being declared
twice.  Nothing about them changed, so every use below still resolves. -/

/-- **Tensor powers transport along an isomorphism**: `L ≅ M` gives
`L^{⊗n} ≅ M^{⊗n}`. -/
noncomputable def modTensorPowMapIso {Z : Scheme.{u}} {L M : Z.Modules} (e : L ≅ M) :
    ∀ n : ℕ, modTensorPow L n ≅ modTensorPow M n
  | 0 => Iso.refl _
  | (n + 1) => modTensorMapIso e (modTensorPowMapIso e n)

/-- **`𝒪_Z^{⊗n} ≅ 𝒪_Z`** — iterated left unitor.  This is the "UNITOR"
obligation recorded against `isQuasiAffine_of_isAmpleSheaf_modUnit`. -/
noncomputable def modTensorPowUnitIso {Z : Scheme.{u}} :
    ∀ n : ℕ, modTensorPow (modUnit Z) n ≅ modUnit Z
  | 0 => Iso.refl _
  | (n + 1) => modTensorUnitLeftIso _ ≪≫ modTensorPowUnitIso n

/-! ### Tensor products of global sections

HOISTED 2026-07-28 from `§ Tensor powers of a global section`, which is a
thousand lines below.  The reason is `exists_modPullback_modTensor`: that leaf
states its PINNING clause in terms of `tensorSection`, so both definitions have
to precede it.  `tensorPowSection` stays where it was — it needs `unitOne`,
which needs the non-vanishing-locus material. -/

/-- The unit of the sheafification adjunction at the presheaf tensor product:
this is what turns a tensor of sections into a section of `modTensor`. -/
noncomputable def modTensorMk {Z : Scheme.{u}} (L M : Z.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val ⟶ (modTensor L M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app _

/-- **`a ⊗ b` as a global section of `L ⊗ M`.**  The presheaf tensor product is
OBJECTWISE (`PresheafOfModules.Monoidal.tensorObj` sends `X` to
`M₁.obj X ⊗ M₂.obj X`), so `a ⊗ₜ b` is literally an element of it; the only step
is pushing it through the sheafification unit. -/
noncomputable def tensorSection {Z : Scheme.{u}} {L M : Z.Modules} (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    Γ(modTensor L M, ⊤) :=
  (modTensorMk L M).app (op ⊤) (a ⊗ₜ b)

/-! ### Pullback of a global section, and `f^* 𝒪_Y ≅ 𝒪_X` -/

/-- **The pullback of a global section**, `f^* s ∈ Γ(f^*A, ⊤)`.

Obtained from the unit `A ⟶ f_* f^* A` of the pullback/pushforward adjunction
evaluated on global sections; `Γ(f_*N, ⊤) = Γ(N, f ⁻¹ᵁ ⊤) = Γ(N, ⊤)` is
definitional. -/
noncomputable def modPullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    (s : Γ(A, ⊤)) : Γ(modPullback f A, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op ⊤) s

/-! ### Transport of the non-vanishing locus along an isomorphism

The second obligation recorded against `isAmpleSheaf_of_iso`.  It is a
computation with `trivializedSection`: `Scheme.Modules.restrictAppIso` is
`Iso.refl` and `restrictFunctor` is a pushforward, so only the naturality of
`α` survives. -/

/-- Transporting a trivialization of `A` to one of `B` along `α : A ≅ B` leaves
the trivialized section unchanged. -/
lemma trivializedSection_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection ((Scheme.Modules.restrictFunctor U.ι).mapIso α.symm ≪≫ φ)
      (α.hom.val.app (op ⊤) s) = trivializedSection φ s := by
  unfold trivializedSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have hcomp : ∀ (x : Γ(B.restrict U.ι, ⊤)),
      ((Scheme.Modules.restrictFunctor U.ι).map α.inv ≫ φ.hom).val.app (op ⊤) x
        = φ.hom.val.app (op ⊤) (α.inv.val.app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) x) :=
    fun _ => rfl
  rw [hcomp]
  refine congrArg _ ?_
  have hnat := PresheafOfModules.naturality_apply α.hom.val
    (X := op (⊤ : Z.Opens)) (Y := op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (homOfLE le_top).op s
  have hinv : ∀ (V : Z.Opensᵒᵖ) (y : A.val.obj V), α.inv.val.app V (α.hom.val.app V y) = y := by
    intro V y
    have : (α.hom ≫ α.inv).val.app V = 𝟙 _ := by rw [α.hom_inv_id]; rfl
    exact ConcreteCategory.congr_hom this y
  exact (congrArg _ hnat.symm).trans (hinv _ _)

/-- Non-vanishing transports along an isomorphism of sheaves. -/
lemma nonvanishingAt_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) (s : Γ(A, ⊤)) (z : Z)
    (h : NonvanishingAt A s z) : NonvanishingAt B (α.hom.val.app (op ⊤) s) z := by
  obtain ⟨U, hz, φ, hmem⟩ := h
  exact ⟨U, hz, (Scheme.Modules.restrictFunctor U.ι).mapIso α.symm ≪≫ φ,
    by rw [trivializedSection_of_iso]; exact hmem⟩

/-- **The non-vanishing locus is an invariant of the pair `(sheaf, section)` up
to isomorphism.** -/
lemma nonvanishingLocus_of_iso {Z : Scheme.{u}} {A B : Z.Modules} (α : A ≅ B) (s : Γ(A, ⊤)) :
    nonvanishingLocus B (α.hom.val.app (op ⊤) s) = nonvanishingLocus A s := by
  ext z
  constructor
  · intro h
    have h2 := nonvanishingAt_of_iso α.symm _ z h
    have e0 : (α.symm.hom.val.app (op ⊤)) ((α.hom.val.app (op ⊤)) s) = s := by
      have hh : (α.hom ≫ α.inv).val.app (op ⊤) = 𝟙 _ := by rw [α.hom_inv_id]; rfl
      exact ConcreteCategory.congr_hom hh s
    rw [e0] at h2
    exact h2
  · exact fun h => nonvanishingAt_of_iso α s z h

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

/-! ### The two CATEGORICAL leaves

The first of the two (the ASSOCIATOR) is PROVEN; only
`nonempty_modPullback_modTensor` remains.  Each is strictly smaller than one of
the six statements it replaced, and each
names in its docstring what it needs.  Between them they are the residue of the
ampleness theory that `Mathlib/AlgebraicGeometry/` does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY at this pin — re-run it
before believing this sentence).

The other three open leaves are further down, in the trivialization calculus
that begins after `nonvanishingLocus_modUnit`; only one of them
(`exists_trivialization_of_modTensorPow`) is mathematics.
(`trivializedSection_trivializationOfLE`, the fourth, was PROVEN 2026-07-28 by
rerouting `modRestrictLEIso` through `Scheme.Modules.restrictFunctorCongr`.) -/

/-- **THE ASSOCIATOR** — PROVEN (2026-07-28): `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` for
`𝒪_Z`-modules.

The route recorded in the previous version of this docstring — pair
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean` — is the one that
works; see the section above.  The whole associativity question reduces to
`modLocW_whiskerLeft` ("tensoring preserves local isomorphisms") — itself PROVEN
since 2026-07-28 — from which the localized monoidal structure, and with it this
associator, both unitors and the braiding, are formal.

Everything else about tensor powers in this file (`nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, and hence `isAmpleSheaf_modTensorPow`) is DERIVED
from this statement, so the module now carries NO open associativity
obligation. -/
theorem nonempty_modTensor_assoc {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor L (modTensor M N)) := by
  have e : toModLM (modTensor (modTensor L M) N) ≅ toModLM (modTensor L (modTensor M N)) :=
    modTensorLocIso (modTensor L M) N ≪≫
      MonoidalCategory.tensorIso (modTensorLocIso L M) (Iso.refl (toModLM N)) ≪≫
      α_ (toModLM L) (toModLM M) (toModLM N) ≪≫
      MonoidalCategory.tensorIso (Iso.refl (toModLM L)) (modTensorLocIso M N).symm ≪≫
      (modTensorLocIso L (modTensor M N)).symm
  exact ⟨{ hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }⟩

/-- **Monoidality of `f^*` on objects** (sorry leaf):
`f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`, **with the isomorphism PINNED by its effect on
global sections**: it carries `f^*(a ⊗ b)` to `f^*a ⊗ f^*b`.

**RESTATED 2026-07-28 — the previous `Nonempty` form was UNDER-PINNED, and that
is a defect and not a matter of taste.**  The old statement was

    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M))

and an adversary may post-compose any witness with multiplication by a unit `u`
of `Γ(X, ⊤)` — `modTensorMapIso` of the two identity isos, twisted by `u`, is
again an isomorphism between exactly those two objects — so *every* clause of
the old statement survives while every trivialized section is scaled by `u`.
Consequently `a ⊗ b ↦ a · b`, which is the ONLY thing the trivialization
calculus below wants from this leaf, is not a consequence of it.  That is what
forced `exists_trivialization_tensorPow` to be cut as a separate leaf, and it is
why it must be re-derived here rather than assumed: **the `Nonempty` packaging
was not weaker mathematics, it was a statement about a different (larger) set of
isomorphisms.**

The pinning clause below is the standard one and it is TRUE of the canonical
comparison map, by the adjunction triangle: the canonical `θ` is the transpose
of `L ⊗ M ⟶ f_*(f^*L ⊗ f^*M)`, which on `V`-sections is `s ⊗ t ↦ η(s) ⊗ η(t)`,
and `θ ∘ η_{L ⊗ M}` is that very map; `modPullbackSection` is `η` read at `⊤`.
It is stated at `⊤` only, which is all any consumer needs — `trivializedSection`
restricts a GLOBAL section — and it is enough to defeat the unit twist above,
since scaling by `u` changes the left-hand side and not the right.

With `modPullbackUnitIso` PROVEN, this is the only obligation of
`nonempty_modPullback_modTensorPow` — and the only input of the trivialization
calculus below as well (`nonempty_restrict_modTensor` is three lines over it,
via `Scheme.Modules.restrictFunctorIsoPullback`).  So this is still the ONLY
leaf in the module that anything except `exists_trivialization_of_modTensorPow`
waits on.

ROUTE AUDIT (rewritten 2026-07-28 against the pin; every declaration named below
was located by `grep` in `.lake/packages/mathlib`, and the check that would
refute each claim is the same `grep`).

The previous audit said "the ring-CHANGING pushforward is only lax, and the left
adjoint of a lax monoidal functor is oplax, which is what supplies the canonical
comparison" — correct, but it left the reader to build both halves.  Both are in
the pin, and the chain is now completely explicit:

1. `ModuleCat.restrictScalars f` is **already `LaxMonoidal`** —
   `Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`, obtained as
   `(extendRestrictScalarsAdj f).rightAdjointLaxMonoidal`, and its comparison is
   computed there: `restrictScalars_μ_tmul : μ (restrictScalars f) M₁ M₂
   (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂`.  (The previous audit did not know this.)
2. `PresheafOfModules.pushforward φ` is **definitionally**
   `pushforward₀ F R ⋙ restrictScalars φ` (`Presheaf/Pushforward.lean`), and
   `pushforward₀OfCommRingCat` is strong `Monoidal`
   (`Presheaf/PushforwardZeroMonoidal.lean`).  So the ONE instance missing at
   this pin is `(PresheafOfModules.restrictScalars α).LaxMonoidal`, which is
   objectwise (1): the presheaf tensor is objectwise, so `μ` is `μ` of
   `ModuleCat.restrictScalars` at each `X`, and only naturality is to check.
3. `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`
   (`Mathlib/CategoryTheory/Monoidal/Functor.lean`) then makes
   `PresheafOfModules.pullback φ` **oplax monoidal**, with `δ` the canonical
   comparison — this is the map to write, not to guess.
   `CategoryTheory.Functor.Monoidal.ofOplaxMonoidal` (same file) upgrades it to
   strong given `IsIso (η F)` and `IsIso (δ F X Y)`.
4. Transport to SHEAVES is free: `SheafOfModules.sheafificationCompPullback`
   (`Sheaf/PullbackContinuous.lean`) is `a_Y ⋙ f^* ≅ p^* ⋙ a_X`, and
   `SheafOfModules.pullbackIso` is `f^* ≅ forget ⋙ p^* ⋙ a_X`.

So after (1)–(4) the residue of this leaf is a statement of exactly the same
shape as `modLocW_whiskerLeft`, and it should be cut as such:

    modLocW X (δ (PresheafOfModules.pullback φ) P Q)

"the oplax comparison map of the PRESHEAF pullback is a LOCAL isomorphism".
Both are instances of "sheafification is monoidal", and a prover who closes
`modLocW_whiskerLeft` by the stalk route (route 3 there) will find the same
filtered-colimit input closes this one, because `p^*` on presheaves over a space
is the filtered colimit `colim_{V ⊇ f(U)}` — the site functor `Opens.map f.base`
is final (`opensMapFinal`, proven above).

* A prover who wants a smaller first target: the OPEN IMMERSION case is strictly
  easier and is what everything below actually consumes, and it is easier for a
  reason the previous audit did not name.  For an open immersion, restriction is
  itself a LEFT adjoint (`Scheme.Modules.restrictAdjunction`, which is what
  `restrictFunctorIsoPullback` compares to `pullbackPushforwardAdjunction`), and
  at presheaf level it is a `pushforward₀` — `restrictAppIso` is `Iso.refl` —
  which by (2) is **strong** monoidal with `μIso = Iso.refl`.  So in the open
  case there is NO `δ`-is-an-iso question at presheaf level at all; the only
  step left is that sheafification commutes with restriction to an open subsite,
  which is the mate of `restrictFunctorIsoPullback`.  It is not cut as a
  separate leaf only because it is a three-line corollary of this one.
PIN CHECK 2026-07-28.  The claim that
`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean` is
present at this pin — which is what makes (2) above usable — was re-run and
STANDS.

* The free/colimit route recorded previously is still available and still
  correct: `SheafOfModules.pullbackObjFreeIso (I : Type u) : (pullback φ).obj
  (free I) ≅ free I` and `pullbackObjUnitToUnit` (`Sheaf/PullbackFree.lean`,
  already imported here), with `Sheaf/Generators.lean`'s `LocalGeneratorsData`
  presenting every sheaf of modules locally as a quotient of frees.  It is
  listed second now because it needs the comparison map (3) anyway before
  "is an iso" can even be stated.

HOW A CONSUMER TURNS THIS INTO THE OPEN-IMMERSION FORM IT WANTS.  The
trivialization calculus below does not consume `modPullbackSection`; it consumes
the restriction of a global section that is spelled out inside
`trivializedSection`.  The bridge is three steps, and **all three were
compiler-checked on 2026-07-28** (in a scratch module; they are not declared here
because a declaration with no consumer is free-floating, and their consumer —
`exists_trivialization_tensorPow` / `exists_trivialization_modTensor` — belongs
to another owner).  Each is stated with the check that reproduces it:

    -- (i) `rfl`.  The restriction inside `trivializedSection` IS the unit of
    --     `Scheme.Modules.restrictAdjunction`, read at `⊤`.
    (Scheme.Modules.restrictAppIso (f := U.ι) L ⊤).inv
        (L.presheaf.map (homOfLE le_top).op s)
      = ((Scheme.Modules.restrictAdjunction U.ι).unit.app L).val.app (op ⊤) s

    -- (ii) `Adjunction.unit_leftAdjointUniq_hom_app _ _ A`, since
    --     `modRestrictPullbackIso` is `restrictFunctorIsoPullback`, which is
    --     `(restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)`.
    (Scheme.Modules.restrictAdjunction f).unit.app A ≫
        (Scheme.Modules.pushforward f).map (modRestrictPullbackIso f A).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A

    -- (iii) naturality of the sheafification unit, one line:
    --     `congr($((sheafificationAdjunction _).unit.naturality
    --        (tensorIso (forget.mapIso e) (forget.mapIso e')).hom).app (op ⊤) (a ⊗ₜ b)).symm`
    --     after `unfold tensorSection modTensorMk modTensorMapIso`.
    (modTensorMapIso e e').hom.val.app (op ⊤) (tensorSection a b)
      = tensorSection (e.hom.val.app (op ⊤) a) (e'.hom.val.app (op ⊤) b)

With (i) and (ii), the pinning clause below transfers verbatim from
`modPullbackSection` to the restriction of a global section along `U.ι`; (iii)
then pushes it through `modTensorMapIso φ ψ`, and `modTensorUnitLeftIso` on
`tensorSection a b` with both factors in `Γ(𝒪_U, ⊤)` is the multiplication
`a * b` that `exists_trivialization_tensorPow` is after.  So the WHOLE gap
between this leaf and that one is (i)–(iii) plus the induction; none of it is
mathematics, and none of it was reachable from the old `Nonempty` form. -/
theorem exists_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    ∃ e : modPullback f (modTensor L M) ≅ modTensor (modPullback f L) (modPullback f M),
      ∀ (a : Γ(L, ⊤)) (b : Γ(M, ⊤)),
        e.hom.val.app (op ⊤) (modPullbackSection f (modTensor L M) (tensorSection a b)) =
          tensorSection (modPullbackSection f L a) (modPullbackSection f M b) := sorry

/-- **Monoidality of `f^*` on objects, forgetting the pinning** (PROVEN
2026-07-28 over `exists_modPullback_modTensor`).

Kept because several consumers — `nonempty_modPullback_modTensorPow`,
`nonempty_restrict_modTensor`, and through them `isAmpleSheaf_modPullback` and
`isInvertibleSheaf_modTensor` — genuinely need nothing more than the existence
of the isomorphism.  Consumers that need the section identity must go through
`exists_modPullback_modTensor` instead; see its docstring for why `Nonempty` is
not enough for them. -/
theorem nonempty_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M)) :=
  ⟨(exists_modPullback_modTensor f L M).choose⟩

/-! ### The non-vanishing locus of a section of the structure sheaf

The "well-definedness of `nonvanishingLocus`" obligation recorded against
`isQuasiAffine_of_isAmpleSheaf_modUnit`.  It is a transition-function
computation, and it needs *less* than the docstring predicted: only that an
endomorphism of `𝒪_U` as an `𝒪_U`-module is multiplication by `β(1)` —
INVERTIBILITY of that factor is never used, because `basicOpen (a * c) ≤
basicOpen a` already suffices in the direction where it is needed.

Note `Γ(modUnit W, ⊤)` and `Γ(W, ⊤)` are DEFEQ at this pin; `unitOne` and
`unitEndoApply` exist only to give the elaborator a place to see that, since
type-class search for `1` and `*` does not unfold `modUnit` on its own. -/

/-- `1 : Γ(W, ⊤)`, read as a section of the unit module. -/
def unitOne (W : Scheme.{u}) : Γ(modUnit W, ⊤) := (1 : Γ(W, ⊤))

/-- An endomorphism of `𝒪_W` (as a module over itself), applied to a global
section, with both sides typed in `Γ(W, ⊤)`. -/
noncomputable def unitEndoApply {W : Scheme.{u}} (β : modUnit W ≅ modUnit W) (a : Γ(W, ⊤)) :
    Γ(W, ⊤) := β.hom.val.app (op ⊤) a

/-- **An endomorphism of the structure sheaf is multiplication by `β(1)`** —
`𝒪_W`-linearity applied to `a = a • 1`. -/
lemma unitEndoApply_eq {W : Scheme.{u}} (β : modUnit W ≅ modUnit W) (a : Γ(W, ⊤)) :
    unitEndoApply β a = a * unitEndoApply β 1 := by
  have h2 : unitEndoApply β (a * 1) = a * unitEndoApply β 1 :=
    (β.hom.val.app (op ⊤)).hom.map_smul a (unitOne W)
  simpa using h2

/-- The CANONICAL trivialization of `𝒪_Z` over `U` computes the ordinary
restriction map `Γ(Z, ⊤) ⟶ Γ(U, ⊤)`.  Uses `Scheme.Opens.ι_appIso`, which says
the comparison isomorphism of an open immersion of the form `U.ι` is
`Iso.refl`. -/
lemma trivializedSection_restrictUnitIso {Z : Scheme.{u}} (U : Z.Opens) (r : Γ(Z, ⊤)) :
    trivializedSection (Scheme.Modules.restrictUnitIso U.ι) r = U.ι.appTop r := by
  unfold trivializedSection
  rw [Scheme.Opens.ι_appTop]
  simp [Scheme.Modules.restrictUnitIso, Scheme.Opens.ι_appIso]
  rfl

/-- Post-composing a trivialization with an endomorphism of `𝒪_U` post-composes
the trivialized section. -/
lemma trivializedSection_trans {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (α : A.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (β : modUnit (U : Scheme.{u}) ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (α ≪≫ β) s = unitEndoApply β (trivializedSection α s) := rfl

/-- **The non-vanishing locus of a section of the structure sheaf is its basic
open** (PROVEN 2026-07-27).

`⊇` take `U = ⊤` and the canonical trivialization.  `⊆` any trivialization `φ`
factors as `restrictUnitIso ≪≫ β` with `β` an endomorphism of `𝒪_U`, so
`trivializedSection φ r = (r|_U) * β(1)` and
`basicOpen ((r|_U) * β(1)) ≤ basicOpen (r|_U) = U.ι ⁻¹ᵁ Z.basicOpen r`.

This was the ONLY remaining input of `isQuasiAffine_of_isAmpleSheaf_modUnit`,
which is therefore now sorry-free. -/
theorem nonvanishingLocus_modUnit (Z : Scheme.{u}) (r : Γ(Z, ⊤)) :
    nonvanishingLocus (modUnit Z) r = (Z.basicOpen r : Set Z) := by
  have key : ∀ (U : Z.Opens) (φ : (modUnit Z).restrict U.ι ≅ modUnit (U : Scheme.{u})),
      (U : Scheme.{u}).basicOpen (trivializedSection φ r)
        ≤ (U : Scheme.{u}).basicOpen (U.ι.appTop r) := by
    intro U φ
    obtain ⟨β, hφ⟩ : ∃ β : modUnit (U : Scheme.{u}) ≅ modUnit (U : Scheme.{u}),
        φ = Scheme.Modules.restrictUnitIso U.ι ≪≫ β :=
      ⟨(Scheme.Modules.restrictUnitIso U.ι).symm ≪≫ φ,
        Eq.symm (Iso.self_symm_id_assoc _ _)⟩
    have e1 : trivializedSection φ r = (U.ι.appTop r) * unitEndoApply β 1 := by
      rw [hφ]
      exact (trivializedSection_trans _ _ _).trans
        ((congrArg (unitEndoApply β) (trivializedSection_restrictUnitIso U r)).trans
          (unitEndoApply_eq β _))
    rw [e1, Scheme.basicOpen_mul]
    exact inf_le_left
  ext z
  constructor
  · rintro ⟨U, hz, φ, hmem⟩
    have h1 := key U φ hmem
    have h2 : (⟨z, hz⟩ : (U : Scheme.{u})) ∈ U.ι ⁻¹ᵁ Z.basicOpen r :=
      (Scheme.preimage_basicOpen_top U.ι r).symm ▸ h1
    exact h2
  · intro hzr
    refine ⟨⊤, trivial, Scheme.Modules.restrictUnitIso (⊤ : Z.Opens).ι, ?_⟩
    have h3 : (⟨z, trivial⟩ : ((⊤ : Z.Opens) : Scheme.{u}))
        ∈ (⊤ : Z.Opens).ι ⁻¹ᵁ Z.basicOpen r := hzr
    have h4 := (Scheme.preimage_basicOpen_top (⊤ : Z.Opens).ι r) ▸ h3
    exact (congrArg ((⊤ : Z.Opens) : Scheme.{u}).basicOpen
      (trivializedSection_restrictUnitIso (⊤ : Z.Opens) r)).ge h4

/-! ### Restriction of a trivialization to a smaller open

A trivialization is a datum over an OPEN, and every comparison of two
trivializations has to happen over their intersection.  This section builds that
move.

**Route changed 2026-07-28.**  It used to go through `modPullback`, to dodge the
`[IsOpenImmersion f]` instance argument that `restrictFunctor` carries — but that
made `modRestrictLEIso` a composite of `Adjunction.leftAdjointUniq` components,
which compute on sections not at all, and `trivializedSection_trivializationOfLE`
was left open because of it.  The instance juggling was never the problem:
`Scheme.Modules.restrictFunctorCongr` **is** the congruence, it is already in the
pin, and both it and `restrictFunctorComp` have `_app_app` lemmas that are `rfl`
and read `A.presheaf.map (eqToHom _).op`.  So the calculus is now written off
those two, everything on sections is an honest presheaf map, and the leaf is
proven. -/

/-- **Restriction commutes with `modTensor`** (PROVEN 2026-07-28 over
`nonempty_modPullback_modTensor`, in three lines).

This — not the general pullback statement — is what the ampleness theory below
actually consumes, and it is strictly weaker; see the ROUTE AUDIT on
`nonempty_modPullback_modTensor`. -/
theorem nonempty_restrict_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (L M : Y.Modules) :
    Nonempty ((modTensor L M).restrict f ≅ modTensor (L.restrict f) (M.restrict f)) := by
  obtain ⟨e⟩ := nonempty_modPullback_modTensor f L M
  exact ⟨modRestrictPullbackIso f _ ≪≫ e ≪≫
    modTensorMapIso (modRestrictPullbackIso f L).symm (modRestrictPullbackIso f M).symm⟩

/-- **Restricting a trivialization restricts the trivialized section** (sorry
leaf).  Pure plumbing — no mathematics — and the only reason it is not proven
here is that `modRestrictLEIso` is routed through `modPullback`, whose component
isomorphisms come from `Adjunction.leftAdjointUniq` and are therefore not
definitional.

The skeleton, since the same shape recurs everywhere in this file:

* one `have hcomp : ∀ x, … = … := fun _ => rfl` naming each factor's
  `.val.app (op ⊤)` explicitly.  `simp` will NOT split a composite
  `.val.app` — `Iso.trans_hom` and `Functor.mapIso_hom` fire, but
  `SheafOfModules.comp_val`, `PresheafOfModules.comp_app` and
  `ConcreteCategory.comp_apply` are all reported UNUSED and the composite stays
  one opaque application;
* `toApp`, converting `.val.app (op V)` to `Scheme.Modules.Hom.app _ V`, which is
  the form mathlib's `_app_app` simp lemmas are stated in;
* `hpush`, `restrictFunctor` being a pushforward, so its `map` shifts the open;
* `hnat`, `PresheafOfModules.naturality_apply` for `φ.hom.val`;
* `step5`, `restrictUnitIso ∘ restriction = appTop`, via `Scheme.Hom.appIso_hom`
  and `Scheme.homOfLE_app` / `homOfLE_appTop`.

Two notes that cost time. `rw [← step5, ← hnat]` on the RIGHT-hand side, then
`congr 1`, is what lets the argument goal be produced by the tactic instead of
written out by hand. And `rw [← Functor.map_comp]` does NOT fire on
`Z.presheaf.map _ ≫ Z.presheaf.map _` — `erw` does; the elaborated functor is not
syntactically the `Z.presheaf` one writes.  The final step in both branches is
that `Opens Z` is a POSET, so any two parallel morphisms are `Subsingleton.elim`
equal and `Quiver.Hom.unop_inj` lifts that to the opposite category. -/
theorem trivializedSection_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfLE h φ) s
      = (Z.homOfLE h).appTop (trivializedSection φ s) := by
  have hcomp : ∀ x : Γ(A.restrict W.ι, ⊤),
      (trivializationOfLE h φ).hom.val.app (op ⊤) x
        = (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom.val.app (op ⊤)
            (((Scheme.Modules.restrictFunctor (Z.homOfLE h)).map φ.hom).val.app (op ⊤)
              (((Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι).hom.app A).val.app (op ⊤)
                (((Scheme.Modules.restrictFunctorCongr
                    (Z.homOfLE_ι h).symm).hom.app A).val.app (op ⊤) x))) :=
    fun _ => rfl
  have toApp : ∀ {S : Scheme.{u}} {M N : S.Modules} (ψ : M ⟶ N) (V : S.Opens) (y : Γ(M, V)),
      ψ.val.app (op V) y = Scheme.Modules.Hom.app ψ V y := fun _ _ _ => rfl
  unfold trivializedSection
  rw [hcomp]
  simp only [toApp, Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  have hpush : ∀ (y : Γ((A.restrict U.ι).restrict (Z.homOfLE h), ⊤)),
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor (Z.homOfLE h)).map φ.hom) ⊤ y
        = Scheme.Modules.Hom.app φ.hom ((Z.homOfLE h).opensFunctor.obj ⊤) y := fun _ => rfl
  rw [hpush]
  set t : Γ(A.restrict U.ι, ⊤) :=
    (Scheme.Modules.restrictAppIso U.ι A ⊤).inv (A.presheaf.map (homOfLE le_top).op s) with ht
  have hnat : Scheme.Modules.Hom.app φ.hom ((Z.homOfLE h).opensFunctor.obj ⊤)
        ((A.restrict U.ι).val.map (homOfLE (le_top)).op t)
      = (modUnit (U : Scheme.{u})).val.map (homOfLE (le_top)).op
          (Scheme.Modules.Hom.app φ.hom ⊤ t) :=
    PresheafOfModules.naturality_apply φ.hom.val (homOfLE le_top).op t
  have step5 : ∀ (u : Γ((U : Scheme.{u}), ⊤)),
      Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom ⊤
          ((modUnit (U : Scheme.{u})).val.map (homOfLE (le_top)).op u)
        = (Z.homOfLE h).appTop u := by
    intro u
    have hru : ∀ (a : Γ((U : Scheme.{u}), (Z.homOfLE h).opensFunctor.obj ⊤)),
        Scheme.Modules.Hom.app (Scheme.Modules.restrictUnitIso (Z.homOfLE h)).hom ⊤ a
          = ((Z.homOfLE h).appIso ⊤).hom a := fun _ => rfl
    rw [hru, Scheme.Hom.appIso_hom, Scheme.homOfLE_app, Scheme.homOfLE_appTop]
    simp only [Scheme.Opens.toScheme_presheaf_map]
    have hmu : ∀ (y : Γ((U : Scheme.{u}), ⊤)),
        (modUnit (U : Scheme.{u})).val.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y
          = (U : Scheme.{u}).presheaf.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y :=
      fun _ => rfl
    rw [hmu]
    simp only [Scheme.Opens.toScheme_presheaf_map, ← ConcreteCategory.comp_apply]
    congr 1
    erw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun m => ConcreteCategory.hom (Z.presheaf.map m))
      (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  rw [← step5, ← hnat]
  congr 1
  have hIW : ∀ (x : Γ(A, W.ι ''ᵁ (⊤ : (W : Scheme.{u}).Opens))),
      (Scheme.Modules.restrictAppIso W.ι A ⊤).inv x = x := fun _ => rfl
  have hrm : ∀ (y : Γ(A.restrict U.ι, ⊤)),
      (A.restrict U.ι).val.map
          (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op y
        = A.presheaf.map (U.ι.opensFunctor.map
            (homOfLE (le_top : (Z.homOfLE h) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤))).op y :=
    fun _ => rfl
  have hIU : ∀ (x : Γ(A, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))),
      (Scheme.Modules.restrictAppIso U.ι A ⊤).inv x = x := fun _ => rfl
  rw [ht, hIU, hrm, hIW]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => (ConcreteCategory.hom (A.presheaf.map m)) s)
    (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/-- The membership form of `trivializedSection_trivializationOfLE`, which is how
every consumer below uses it. -/
lemma mem_basicOpen_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) {z : Z}
    (hzW : z ∈ W) :
    ((⟨z, hzW⟩ : (W : Scheme.{u})) ∈
        (W : Scheme.{u}).basicOpen (trivializedSection (trivializationOfLE h φ) s)) ↔
      ((⟨z, h hzW⟩ : (U : Scheme.{u})) ∈
        (U : Scheme.{u}).basicOpen (trivializedSection φ s)) := by
  rw [trivializedSection_trivializationOfLE, ← Scheme.preimage_basicOpen_top]
  show (Z.homOfLE h).base ⟨z, hzW⟩ ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) ↔
    (⟨z, h hzW⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s)
  rw [show (Z.homOfLE h).base ⟨z, hzW⟩ = (⟨z, h hzW⟩ : (U : Scheme.{u})) from
    Scheme.homOfLE_apply' h z hzW]
  exact Iff.rfl

/-! ### Well-definedness of the non-vanishing locus

`NonvanishingAt A s z` is an `∃` over trivializations near `z`.  This is the
lemma that says the `∃` is a `∀` once ONE trivialization is in hand — the
general form of the `key` computation inside `nonvanishingLocus_modUnit`, and it
needs exactly as little as that one did: two trivializations over a common open
differ by an endomorphism of `𝒪`, which is multiplication by `β(1)`, and
`basicOpen (a * c) ≤ basicOpen a` does the rest.  INVERTIBILITY of `β(1)` is
never used. -/

/-- **The non-vanishing locus, read through any one trivialization** (PROVEN
2026-07-28). -/
theorem nonvanishingAt_iff_trivializedSection {Z : Scheme.{u}} {A : Z.Modules} (s : Γ(A, ⊤))
    {U : Z.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) {z : Z} (hz : z ∈ U) :
    NonvanishingAt A s z ↔
      (⟨z, hz⟩ : (U : Scheme.{u})) ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) := by
  constructor
  · rintro ⟨V, hzV, ψ, hmem⟩
    have hzW : z ∈ U ⊓ V := ⟨hz, hzV⟩
    set φW := trivializationOfLE (inf_le_left : U ⊓ V ≤ U) φ with hφW
    set ψW := trivializationOfLE (inf_le_right : U ⊓ V ≤ V) ψ with hψW
    have hmemW : (⟨z, hzW⟩ : ((U ⊓ V : Z.Opens) : Scheme.{u})) ∈
        ((U ⊓ V : Z.Opens) : Scheme.{u}).basicOpen (trivializedSection ψW s) :=
      (mem_basicOpen_trivializationOfLE inf_le_right ψ s hzW).2 hmem
    have hsplit : ψW = φW ≪≫ (φW.symm ≪≫ ψW) := Eq.symm (Iso.self_symm_id_assoc _ _)
    have hval : trivializedSection ψW s
        = trivializedSection φW s * unitEndoApply (φW.symm ≪≫ ψW) 1 := by
      conv_lhs => rw [hsplit]
      exact (trivializedSection_trans _ _ _).trans (unitEndoApply_eq _ _)
    rw [hval, Scheme.basicOpen_mul] at hmemW
    exact (mem_basicOpen_trivializationOfLE inf_le_left φ s hzW).1 hmemW.1
  · exact fun hmem => ⟨U, hz, φ, hmem⟩

/-! ### Invertibility, and the NUMERICAL-SEMIGROUP bridge

This section is the FAITHFULNESS AUDIT that
`nonvanishingLocus_modPullback_of_isAmpleSheaf` was flagged as needing.  See
`isInvertibleSheaf_of_isAmpleSheaf` for the verdict and its proof sketch. -/

/-- **A tensor product of invertible sheaves is invertible** (PROVEN over
`nonempty_restrict_modTensor`): trivialize both over `U ⊓ V`.

Deliberately NOT hoisted to `RelativePicard.lean` with the rest of the free
calculus (2026-07-28), and the reason is worth recording: this declaration is
the ONLY consumer of `nonempty_restrict_modTensor`, which in turn is the only
consumer of `nonempty_modPullback_modTensor`.  Moving it up would have left
both of those free-floating and silently orphaned that leaf's owner's work.
`RelativePicard.lean` therefore carries its own
`isInvertibleSheaf_modTensorPic`, over its own twin of the pullback leaf; the
two collapse into one when `nonempty_modPullback_modTensor` is settled and the
hoist described there is carried out. -/
theorem isInvertibleSheaf_modTensor {Z : Scheme.{u}} {L M : Z.Modules}
    (hL : IsInvertibleSheaf L) (hM : IsInvertibleSheaf M) : IsInvertibleSheaf (modTensor L M) := by
  intro z
  obtain ⟨U, hzU, ⟨φ⟩⟩ := hL z
  obtain ⟨V, hzV, ⟨ψ⟩⟩ := hM z
  obtain ⟨e⟩ := nonempty_restrict_modTensor (U ⊓ V : Z.Opens).ι L M
  exact ⟨U ⊓ V, ⟨hzU, hzV⟩, ⟨e ≪≫ modTensorMapIso (trivializationOfLE inf_le_left φ)
    (trivializationOfLE inf_le_right ψ) ≪≫ modTensorUnitLeftIso _⟩⟩

/-- **Every tensor power of an invertible sheaf is invertible** (PROVEN). -/
theorem isInvertibleSheaf_modTensorPow {Z : Scheme.{u}} {L : Z.Modules}
    (hL : IsInvertibleSheaf L) : ∀ n : ℕ, IsInvertibleSheaf (modTensorPow L n)
  | 0 => isInvertibleSheaf_modUnit Z
  | (n + 1) => isInvertibleSheaf_modTensor hL (isInvertibleSheaf_modTensorPow hL n)

/-- **AN INVERTIBLE SHEAF OF MODULES IS LOCALLY FREE OF RANK ONE** (sorry leaf) —
Stacks 01CV, Hartshorne II.6.12.  Stated in the form the audit needs: if SOME
positive tensor power of `A` is trivial on `U`, then `A` itself is trivial on a
smaller neighbourhood of each point of `U`.

**This is the single mathematical leaf of the module** (`nonempty_modTensor_assoc`
and `nonempty_modPullback_modTensor` aside), and it is the whole content of the
numerical-semigroup worry recorded against
`nonvanishingLocus_modPullback_of_isAmpleSheaf`.

WHY IT IS TRUE, and why it is not formal.  Stalks first: sheafification preserves
stalks and `(P ⊗ Q)_y = P_y ⊗_{𝒪_y} Q_y` (filtered colimits commute with `⊗`), so
`(A^{⊗k})|_U ≅ 𝒪_U` gives `A_y^{⊗k} ≅ 𝒪_y` for every `y ∈ U`, hence `A_y` is an
invertible module over the LOCAL ring `𝒪_y`, hence free of rank one.  Stalkwise
freeness is NOT enough — that is the step that fails for a general sheaf of
modules, which is why `Z.Modules` being non-quasi-coherent makes this a theorem
rather than an observation.  What supplies the missing finiteness is the tensor
inverse itself: `A|_U ⊗ (A^{⊗(k-1)})|_U ≅ 𝒪_U` means that near each point
`1 = Σ_{i≤m} s_i ⊗ t_i` for FINITELY many sections, and the standard
`m = Σ_i ⟨t_i, m⟩ s_i` computation then shows `A` is generated by `s_1, …, s_m`
there.  Finite type plus a free stalk gives local triviality.

Do NOT weaken this to a hypothesis on the consumers instead: `IsAmpleSheaf` is
what the consumer `exists_isAmpleSheaf_cube_of_isAlgClosed` produces, and it
produces `IsInvertibleSheaf` beside it — so the ALTERNATIVE repair (thread
`IsInvertibleSheaf L` through `nonvanishingLocus_modPullback_of_isAmpleSheaf` and
`isAmpleSheaf_modPullback`, and stop discarding it at the call site in
`AbelianSchemeIsogeny.lean`, where it is currently bound to `-`) is available and
costs nothing mathematically.  It is not taken here because the statement as
given is TRUE, and weakening a true statement to dodge a proof is exactly what
the faithfulness rule forbids.

PIN CHECK 2026-07-28 — one claim re-run and CONFIRMED, one API added that was
not recorded here.

* The stalk half of the argument above really is blocked, and the module
  docstring's note about `NonvanishingAt` is the same gap:
  `grep -rln stalk Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` is
  **EMPTY** at this pin.  (`Scheme.Modules.restrictStalkNatIso` does exist, but
  it is a stalk of the underlying `Ab`-presheaf and carries no `Module`
  structure, so it cannot express "`A_y` is invertible over `𝒪_y`".)
* NOT recorded here before, and it is the vocabulary this leaf should be phrased
  against: `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean` EXISTS at
  this pin, supplying `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData` and
  `GeneratingSections`, on top of `Sheaf/Generators.lean` and
  `Sheaf/Quasicoherent.lean`.  That is DEFINITIONS, not this theorem —
  "invertible implies locally free of rank one" is not in the pin, and a grep
  for it returns nothing — but the finite-generation half of the argument above
  ("`A` is generated by `s_1, …, s_m` there") is literally a
  `LocalGeneratorsData`, and `free.generatingSections` already gives the rank-one
  model.  So the missing input is the STALK-MODULE structure, not the
  local-freeness vocabulary. -/
theorem exists_trivialization_of_modTensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    {k : ℕ} (hk : 0 < k) (ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}))
    {z : Z} (hz : z ∈ U) :
    ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ Nonempty (A.restrict W.ι ≅ modUnit (W : Scheme.{u})) := sorry

/-- **AMPLE IMPLIES INVERTIBLE** (PROVEN 2026-07-28 over
`exists_trivialization_of_modTensorPow`) — **and this is the FAITHFULNESS VERDICT
that `nonvanishingLocus_modPullback_of_isAmpleSheaf` was flagged as needing.**

The recorded worry was: `IsAmpleSheaf L` guarantees only that at each `z` SOME
power `L^{⊗m}` has a trivializing section, and the set of such `m` is a numerical
SEMIGROUP, not all of `ℕ`; so it is not obvious that it says anything about the
particular power `n` appearing in that leaf.  **The worry is real and the
conclusion is that the leaf is nevertheless TRUE**, by the following two steps:

1.  `IsAmpleSheaf L` gives, at each `z`, an `m > 0` and a trivialization of
    `L^{⊗m}` on some `U ∋ z` (that trivialization is inside `NonvanishingAt`
    itself — this is the step that makes ampleness, as defined here, carry local
    triviality at all).
2.  `exists_trivialization_of_modTensorPow` turns a trivialization of `L^{⊗m}`
    into one of `L`.  **This is where the semigroup collapses**: once `L` itself
    is locally trivial, every power is, and `n` is no longer special.

So no hypothesis needs adding anywhere.  The counterexample recorded on
`nonvanishingLocus_modPullback_of_isAmpleSheaf` (the skyscraper `k` at the origin
of `Spec k[u]`) is still exactly right about why the hypothesis-free statement is
FALSE, and it is ruled out here at step 1: no power of that skyscraper is
locally trivial at the origin. -/
theorem isInvertibleSheaf_of_isAmpleSheaf {Z : Scheme.{u}} {L : Z.Modules}
    (h : IsAmpleSheaf L) : IsInvertibleSheaf L := by
  intro z
  obtain ⟨m, hm, s, V, hzV, -, hloc⟩ := h z
  have hz : z ∈ nonvanishingLocus (modTensorPow L m) s := by rw [hloc]; exact hzV
  obtain ⟨U, hzU, φ, -⟩ := hz
  obtain ⟨W, -, hzW, hW⟩ := exists_trivialization_of_modTensorPow hm φ hzU
  exact ⟨W, hzW, hW⟩

/-! ### Tensor powers of a global section -/

/-! `modTensorMk` and `tensorSection` used to be declared here.  They were
HOISTED (2026-07-28) to `§ Tensor products of global sections`, immediately after
`modTensorPowUnitIso`, because `exists_modPullback_modTensor` states its pinning
clause in terms of `tensorSection`.  Nothing else about them changed. -/

/-- **`s^{⊗k}`**, right-nested onto `1 ∈ Γ(𝒪_Z, ⊤)` exactly as `modTensorPow` is
right-nested onto `modUnit`. -/
noncomputable def tensorPowSection {Z : Scheme.{u}} {A : Z.Modules} (s : Γ(A, ⊤)) :
    ∀ k : ℕ, Γ(modTensorPow A k, ⊤)
  | 0 => unitOne Z
  | (k + 1) => tensorSection s (tensorPowSection s k)

/-- **A TRIVIALIZATION OF A TENSOR PRODUCT MULTIPLIES SECTIONS** (sorry leaf, cut
2026-07-28 out of `exists_trivialization_tensorPow`).

Given trivializations of `L` and `M` over one open `U`, there is a trivialization
of `L ⊗ M` over `U` that carries `a ⊗ b` to the PRODUCT of the two trivialized
sections.

**WHY THIS LEAF EXISTS — the ROUTE recorded on `exists_trivialization_tensorPow`
could not work as written, and this is a correction, not a restatement.**  That
route said: "induct on `k`, building `ψ` out of `nonempty_restrict_modTensor` and
`modTensorUnitLeftIso` exactly as `isInvertibleSheaf_modTensor` does, and check
the section identity against `tensorSection`'s definition".  The induction is
fine and is now discharged below.  The "check the section identity" step is not:
**`nonempty_restrict_modTensor` delivers `Nonempty`, i.e. an ARBITRARY
isomorphism**, and `trivializedSection` through an arbitrary isomorphism is not
computable by any amount of unfolding.  Concretely, post-composing that anonymous
iso with multiplication by any unit `c : Γ(U, ⊤)ˣ` satisfies every clause
`nonempty_restrict_modTensor` states while multiplying the trivialized section by
`c` — so the identity `a ⊗ₜ b ↦ a * b` is simply not pinned by the stated inputs.
The missing ingredient is a comparison isomorphism with a KNOWN effect on
sections, which is what this leaf asks for.

**Not vacuous, and not under-pinned.**  The `∀ a b` clause pins `θ` on every pure
tensor of global sections, which is exactly what the consumer consumes; a `θ`
differing by a unit fails it.  It is also satisfiable: the presheaf tensor is
OBJECTWISE (`PresheafOfModules.Monoidal.tensorObj` sends `X` to
`M₁.obj X ⊗ M₂.obj X`), and the left unitor sends `r ⊗ₜ m` to `r • m`, so the
canonical comparison composed with `modTensorMapIso φ χ ≪≫ modTensorUnitLeftIso`
has precisely this effect.

ROUTE: the honest form is to strengthen `nonempty_restrict_modTensor` from
`Nonempty` to a NAMED comparison isomorphism `(L ⊗ M)|_f ≅ L|_f ⊗ M|_f` carrying
`(a ⊗ b)|_f` to `a|_f ⊗ b|_f`, which in turn wants a canonical
`nonempty_modPullback_modTensor` rather than an anonymous one.  Restriction along
an open immersion is a `SheafOfModules.pushforward` along `opensFunctor`, hence
objectwise on presheaves where `⊗` is also objectwise, so at presheaf level the
comparison is the IDENTITY and the whole content is that sheafification commutes
with restriction to an open subsite. -/
theorem exists_trivialization_modTensor {Z : Scheme.{u}} {L M : Z.Modules} {U : Z.Opens}
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    ∃ θ : (modTensor L M).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      ∀ (a : Γ(L, ⊤)) (b : Γ(M, ⊤)),
        trivializedSection θ (tensorSection a b)
          = trivializedSection φ a * trivializedSection χ b := sorry

/-- **`s^{⊗k}` read through the `k`-th power of a trivialization is the `k`-th
power of the trivialized section** (PROVEN 2026-07-28 over
`exists_trivialization_modTensor`).

Induction on `k`, right-nested exactly as `modTensorPow` and `tensorPowSection`
are.  The base case is the canonical trivialization of `𝒪_Z` over `U`, whose
trivialized section is `U.ι.appTop 1 = 1` because `appTop` is a ring map; the
step is one application of `exists_trivialization_modTensor` and `pow_succ'`.

The bookkeeping half of the old ROUTE is therefore discharged; the half that did
not survive contact is recorded on `exists_trivialization_modTensor` above. -/
theorem exists_trivialization_tensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) (k : ℕ) :
    ∃ ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      trivializedSection ψ (tensorPowSection s k) = trivializedSection φ s ^ k := by
  induction k with
  | zero =>
    refine ⟨Scheme.Modules.restrictUnitIso U.ι, ?_⟩
    rw [pow_zero]
    exact (trivializedSection_restrictUnitIso U (1 : Γ(Z, ⊤))).trans (map_one _)
  | succ k ih =>
    obtain ⟨ψ, hψ⟩ := ih
    obtain ⟨θ, hθ⟩ := exists_trivialization_modTensor φ ψ
    exact ⟨θ, (hθ s (tensorPowSection s k)).trans (by rw [hψ, pow_succ'])⟩

/-- **Tensor powers of a section do not change the non-vanishing locus** (PROVEN
2026-07-28).

**No hypothesis on `A`** — in particular no `V`, no `hloc`, no invertibility.
The `⊇` direction is formal; the `⊆` direction is where
`exists_trivialization_of_modTensorPow` (Stacks 01CV) does its work, converting a
trivialization of `A^{⊗k}` near a point into one of `A`, after which
`Scheme.basicOpen_pow` finishes.  This is the statement that shows
`exists_tensorPowSection`'s `hloc` was inert. -/
theorem nonvanishingLocus_tensorPowSection {Z : Scheme.{u}} (A : Z.Modules) (s : Γ(A, ⊤))
    {k : ℕ} (hk : 0 < k) :
    nonvanishingLocus (modTensorPow A k) (tensorPowSection s k) = nonvanishingLocus A s := by
  ext z
  constructor
  · rintro ⟨U, hzU, ψ, hmem⟩
    obtain ⟨W, -, hzW, ⟨φ⟩⟩ := exists_trivialization_of_modTensorPow hk ψ hzU
    obtain ⟨ψ', hψ'⟩ := exists_trivialization_tensorPow φ s k
    have h1 : NonvanishingAt (modTensorPow A k) (tensorPowSection s k) z := ⟨U, hzU, ψ, hmem⟩
    rw [nonvanishingAt_iff_trivializedSection _ ψ' hzW, hψ', Scheme.basicOpen_pow _ _ hk] at h1
    exact (nonvanishingAt_iff_trivializedSection s φ hzW).2 h1
  · rintro ⟨U, hzU, φ, hmem⟩
    obtain ⟨ψ, hψ⟩ := exists_trivialization_tensorPow φ s k
    refine (nonvanishingAt_iff_trivializedSection _ ψ hzU).2 ?_
    rw [hψ, Scheme.basicOpen_pow _ _ hk]
    exact hmem

/-- **Tensor powers of a global section** (PROVEN 2026-07-28 over
`nonvanishingLocus_tensorPowSection`): `s^{⊗k}`, with the same non-vanishing
locus as `s`.

**FAITHFULNESS — CORRECTED 2026-07-28.**  The note that used to stand here said
that `hloc` "is carried deliberately and is not decoration", because the `⊆` half
"must rule out a point at which `A^{⊗k}` happens to be invertible with `s^{⊗k}` a
generator while `A` itself is not invertible", and concluded that a version
without `V` and `hloc` "should be treated as unproven-and-suspect".

The diagnosis of the hard half is exactly right; the conclusion is wrong on both
counts.  `hloc` does **not** rule that point out — it says nothing whatever about
points outside `V`, which is precisely where the danger is.  What rules it out is
`exists_trivialization_of_modTensorPow` (Stacks 01CV), which needs no `V` and no
`hloc`.  So the general statement `nonvanishingLocus (A^{⊗k}) (s^{⊗k}) =
nonvanishingLocus A s` is TRUE with no hypothesis on `A`, and is proven above;
this leaf is a one-line corollary of it, kept in this shape only because
`isAmpleSheaf_modTensorPow` calls it this way.

`V` and `hloc` are therefore inert, and `hloc` is consumed only as the final
rewrite. -/
theorem exists_tensorPowSection {Z : Scheme.{u}} (A : Z.Modules) (s : Γ(A, ⊤)) {k : ℕ}
    (hk : 0 < k) (V : Z.Opens) (hloc : nonvanishingLocus A s = (V : Set Z)) :
    ∃ t : Γ(modTensorPow A k, ⊤),
      nonvanishingLocus (modTensorPow A k) t = (V : Set Z) :=
  ⟨tensorPowSection s k, by rw [nonvanishingLocus_tensorPowSection A s hk]; exact hloc⟩

/-! ### The pullback of a global section, through the canonical isomorphisms

(PROVEN 2026-07-28.)  Every isomorphism appearing in the trivialization calculus
above is a component of one of the four canonical comparisons — restriction-as-
pullback, pseudo-functoriality, functoriality, and `f^*𝒪 ≅ 𝒪` — and each of them
turns out to be *characterised* by what it does to `modPullbackSection` through a
single adjunction identity already in the pin.  That is the whole content of this
section: five one-step lemmas, from which the section identity for the pullback of
a trivialization follows by composition.

The route the docstring below used to call "the compatibility of
`modPullbackSection` with the adjunction unit" is exactly right, and it is CHEAPER
than it looks, because none of the five needs the adjunction unwound by hand:

* `modPullbackSection_map` is `NatTrans.naturality` of the unit;
* `modPullbackSection_compIso` is `unit_conjugateEquiv` together with mathlib's
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`;
* `modPullbackSection_congrIso` is `subst` and `rfl`;
* `modPullbackSection_unitIso` is
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`,
  whose right-hand side `unitToPushforwardObjUnit` is *by definition* the ring map
  `f.app`, which is why the answer comes out as `f.appTop`;
* `modPullbackSection_restrictPullbackIso` is
  `Adjunction.unit_leftAdjointUniq_hom_app`.  Note this is the one place where
  `restrictFunctorIsoPullback` being a `leftAdjointUniq` — recorded elsewhere in
  this file as the REASON a section identity is not definitional — is what makes
  the proof work rather than what obstructs it: `leftAdjointUniq` is *defined* by
  its compatibility with the two units, and the restriction of a global section
  IS the unit of `restrictAdjunction` at `⊤` (`restrictAdjunction_unit_app_app`).

PERFORMANCE NOTE, and it is not incidental.  Composing the six-fold isomorphism
and asking for the identity in one step is *not* feasible: both a single `rfl`
against the fully nested composite and a `rw` chain ending on the last step
exhaust 200000 heartbeats in `isDefEq`, because the trailing `rfl` attempt tries
to unfold the adjunction.  What works is to peel the composite with
`iso_trans_val_app` (a `rfl` lemma at ONE `≪≫` at a time), rewrite with
FULLY-APPLIED instances of the five lemmas, and never let a `rw` end on a goal
that is not already closed — hence the `simp only` and the final `exact`.  The
same consideration is why `modPullbackSection_trivializationStep` is a separate
declaration rather than three more entries in the rewrite list. -/

/-- The restriction of a global section to `U`, as a global section of `A|_U`.

This is the first half of `trivializedSection`, split off so that the composition
lemmas below have something to rewrite against; `trivializedSection φ s` is
`φ` applied to it (`trivializedSection_eq`, which is `rfl`). -/
noncomputable def restrictedSection {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens) (s : Γ(A, ⊤)) :
    Γ(A.restrict U.ι, ⊤) :=
  (Scheme.Modules.restrictAppIso U.ι A ⊤).inv (A.presheaf.map (homOfLE le_top).op s)

/-- `trivializedSection` is a trivialization applied to `restrictedSection`. -/
lemma trivializedSection_eq {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection φ s = φ.hom.val.app (op ⊤) (restrictedSection A U s) := rfl

/-- Peeling ONE `≪≫` off a composite, on global sections.  Definitional, and
kept as a lemma precisely so that it can be applied one step at a time. -/
lemma iso_trans_val_app {W : Scheme.{u}} {M N P : W.Modules} (α : M ≅ N) (β : N ≅ P)
    (x : Γ(M, ⊤)) :
    (α ≪≫ β).hom.val.app (op ⊤) x = β.hom.val.app (op ⊤) (α.hom.val.app (op ⊤) x) := rfl

/-- The inverse of an isomorphism of modules cancels it on global sections. -/
lemma modIso_inv_hom {W : Scheme.{u}} {M N : W.Modules} (α : M ≅ N) (x : Γ(M, ⊤)) :
    α.inv.val.app (op ⊤) (α.hom.val.app (op ⊤) x) = x := by
  have h : (α.hom ≫ α.inv).val.app (op ⊤) = (𝟙 M :).val.app (op ⊤) := by rw [α.hom_inv_id]
  exact ConcreteCategory.congr_hom h x

/-- **`f^*` of a morphism carries `f^*s` to `f^*` of the image** — naturality of
the unit of the pullback/pushforward adjunction. -/
lemma modPullbackSection_map {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (α : A ⟶ B)
    (s : Γ(A, ⊤)) :
    ((Scheme.Modules.pullback f).map α).val.app (op ⊤) (modPullbackSection f A s)
      = modPullbackSection f B (α.val.app (op ⊤) s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality α
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact (ConcreteCategory.congr_hom h2 s).symm

/-- The `modPullbackMapIso` form of `modPullbackSection_map`. -/
lemma modPullbackSection_mapIso {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (e : A ≅ B)
    (s : Γ(A, ⊤)) :
    (modPullbackMapIso f e).hom.val.app (op ⊤) (modPullbackSection f A s)
      = modPullbackSection f B (e.hom.val.app (op ⊤) s) :=
  modPullbackSection_map f e.hom s

/-- **Pseudo-functoriality on sections**: `f^*(g^*s)` is `(f ≫ g)^*s` across
`modPullbackCompIso`.  This is `unit_conjugateEquiv` applied to
`(pullbackComp f g).inv`, whose conjugate mathlib computes to be
`(pushforwardComp f g).hom`; the latter is the IDENTITY on sections
(`pushforwardComp_hom_app_app`), which is what makes the identity come out. -/
lemma modPullbackSection_compIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCompIso f g L).hom.val.app (op ⊤)
        (modPullbackSection f (modPullback g L) (modPullbackSection g L s))
      = modPullbackSection (f ≫ g) L s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  have h3 := ConcreteCategory.congr_hom h2 s
  have h4 : (modPullbackCompIso f g L).hom.val.app (op ⊤)
      ((modPullbackCompIso f g L).inv.val.app (op ⊤) (modPullbackSection (f ≫ g) L s))
      = modPullbackSection (f ≫ g) L s := by
    have h5 : ((modPullbackCompIso f g L).inv ≫ (modPullbackCompIso f g L).hom).val.app (op ⊤)
        = (𝟙 (modPullback (f ≫ g) L) :).val.app (op ⊤) := by
      rw [(modPullbackCompIso f g L).inv_hom_id]
    exact ConcreteCategory.congr_hom h5 _
  rw [← h4]
  exact congrArg _ h3

/-- The inverse form of `modPullbackSection_compIso`. -/
lemma modPullbackSection_compIso_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCompIso f g L).inv.val.app (op ⊤) (modPullbackSection (f ≫ g) L s)
      = modPullbackSection f (modPullback g L) (modPullbackSection g L s) := by
  rw [← modPullbackSection_compIso f g L s]
  exact modIso_inv_hom _ _

/-- **Pullback along equal morphisms** leaves the pulled-back section alone. -/
lemma modPullbackSection_congrIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (L : Y.Modules)
    (s : Γ(L, ⊤)) :
    (modPullbackCongrIso h L).hom.val.app (op ⊤) (modPullbackSection f L s)
      = modPullbackSection g L s := by
  subst h
  rfl

/-- **`f^*𝒪_Y ≅ 𝒪_X` computes `f^#` on sections**: the pullback of `r : Γ(𝒪_Y, ⊤)`,
read through `modPullbackUnitIso`, is `f.appTop r`.

This is the one step that produces the arithmetic — everything else in the chain
is transport — and it is immediate from mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, because the
adjoint of `pullbackObjUnitToUnit` is `unitToPushforwardObjUnit`, which is
DEFINED as the ring map underlying `f`. -/
lemma modPullbackSection_unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(modUnit Y, ⊤)) :
    (modPullbackUnitIso f).hom.val.app (op ⊤) (modPullbackSection f (modUnit Y) r)
      = f.appTop r := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (Scheme.Hom.toRingCatSheafHom f)
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact ConcreteCategory.congr_hom h2 r

/-- **Restriction read as a pullback sends the restricted section to the pulled-back
section** — `Adjunction.unit_leftAdjointUniq_hom_app`, since restricting a global
section IS the unit of `restrictAdjunction` at `⊤`. -/
lemma modPullbackSection_restrictPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (A : Y.Modules) (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso f A).hom.val.app (op ⊤)
        ((Scheme.Modules.restrictAppIso f A ⊤).inv (A.presheaf.map (homOfLE le_top).op a))
      = modPullbackSection f A a := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) A
  have h2 := congrArg (fun m => Scheme.Modules.Hom.app m ⊤) h
  exact ConcreteCategory.congr_hom h2 a

/-- `modPullbackSection_restrictPullbackIso` in `restrictedSection` form. -/
lemma modPullbackSection_restrictedSection {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens)
    (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso U.ι A).hom.val.app (op ⊤) (restrictedSection A U a)
      = modPullbackSection U.ι A a :=
  modPullbackSection_restrictPullbackIso U.ι A a

/-- The inverse form. -/
lemma modPullbackSection_restrictedSection_inv {Z : Scheme.{u}} (A : Z.Modules) (U : Z.Opens)
    (a : Γ(A, ⊤)) :
    (modRestrictPullbackIso U.ι A).inv.val.app (op ⊤) (modPullbackSection U.ι A a)
      = restrictedSection A U a := by
  rw [← modPullbackSection_restrictedSection A U a]
  exact modIso_inv_hom _ _

/-! ### The geometric step of EGA II 5.1.12 -/

/-- **The pullback of a trivialization**, as real code rather than an `∃`:
`(f^*A)|_{f⁻¹U} ≅ 𝒪_{f⁻¹U}`.

Reading right to left, the chain is restriction-as-pullback, pseudo-functoriality
down to `((f⁻¹U).ι ≫ f)^*A`, the base-change identity
`(f⁻¹U).ι ≫ f = (f ∣_ U) ≫ U.ι` (`morphismRestrict_ι`), pseudo-functoriality back
up to `(f ∣_ U)^*(A|_U)`, `f ∣_ U` applied to `φ`, and finally `f^*𝒪 ≅ 𝒪`.  Every
component is PROVEN above, and `trivializedSection_trivializationOfPullback` says
what it does to sections. -/
noncomputable def trivializationOfPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (modPullback f A).restrict (f ⁻¹ᵁ U).ι ≅ modUnit ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}) :=
  modRestrictPullbackIso (f ⁻¹ᵁ U).ι (modPullback f A) ≪≫
    modPullbackCompIso (f ⁻¹ᵁ U).ι f A ≪≫
    modPullbackCongrIso (morphismRestrict_ι f U).symm A ≪≫
    (modPullbackCompIso (f ∣_ U) U.ι A).symm ≪≫
    modPullbackMapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ) ≪≫
    modPullbackUnitIso (f ∣_ U)

/-- The `f ∣_ U`-image of `φ`, read on sections.  Split out of
`trivializedSection_trivializationOfPullback` for the performance reason recorded
in the section docstring above: three more rewrites in that proof's `simp only`
list push it over the heartbeat limit. -/
lemma modPullbackSection_trivializationStep {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    (modPullbackMapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ)).hom.val.app (op ⊤)
        (modPullbackSection (f ∣_ U) (modPullback U.ι A) (modPullbackSection U.ι A s))
      = modPullbackSection (f ∣_ U) (modUnit (U : Scheme.{u})) (trivializedSection φ s) := by
  rw [modPullbackSection_mapIso (f ∣_ U) ((modRestrictPullbackIso U.ι A).symm ≪≫ φ)
      (modPullbackSection U.ι A s),
    iso_trans_val_app (modRestrictPullbackIso U.ι A).symm φ (modPullbackSection U.ι A s),
    Iso.symm_hom, modPullbackSection_restrictedSection_inv A U s, ← trivializedSection_eq φ s]

/-- **The section identity for `trivializationOfPullback`** (PROVEN 2026-07-28):
`f^*s`, read through the pullback of `φ`, is `f^#` of `s` read through `φ`.

This is the statement the docstring of `exists_trivialization_modPullback` named
as the content of that leaf, and it is proven here by composing the five
one-step lemmas of the previous section. -/
theorem trivializedSection_trivializationOfPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfPullback f φ) (modPullbackSection f A s)
      = (f ∣_ U).appTop (trivializedSection φ s) := by
  rw [trivializedSection_eq (trivializationOfPullback f φ) (modPullbackSection f A s)]
  simp only [trivializationOfPullback, iso_trans_val_app, Iso.symm_hom,
    modPullbackSection_restrictedSection (modPullback f A) (f ⁻¹ᵁ U)
      (modPullbackSection f A s),
    modPullbackSection_compIso (f ⁻¹ᵁ U).ι f A s,
    modPullbackSection_congrIso (morphismRestrict_ι f U).symm A s,
    modPullbackSection_compIso_inv (f ∣_ U) U.ι A s,
    modPullbackSection_trivializationStep f φ s]
  exact modPullbackSection_unitIso (f ∣_ U) (trivializedSection φ s)

/-- **The pullback of a trivialization trivializes the pullback, and the
pulled-back section has the preimage basic open** (PROVEN 2026-07-28).

The witness is `trivializationOfPullback f φ`, built as real code above, and the
section identity is `trivializedSection_trivializationOfPullback`; what is left
here is the membership half, which is `Scheme.preimage_basicOpen_top (f ∣_ U)`
together with `morphismRestrict_base_coe`.

The ROUTE recorded here before it was proven was correct in every step, and its
one warning is worth keeping: the compatibility of `modPullbackSection` with the
adjunction unit is the whole content, and it is five separate adjunction facts
(see the section `The pullback of a global section, through the canonical
isomorphisms` above), not one.

Note the statement is for an ARBITRARY morphism `f`.  That is not an oversight:
basic opens pull back along any morphism of schemes, so the closed-immersion
hypothesis of the consumer plays no role here — and indeed no hypothesis on `f`
is used anywhere in the proof. -/
theorem exists_trivialization_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    ∃ ψ : (modPullback f A).restrict (f ⁻¹ᵁ U).ι ≅ modUnit ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}),
      ∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U),
        ((⟨x, hx⟩ : ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})) ∈
            ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}).basicOpen
              (trivializedSection ψ (modPullbackSection f A s))) ↔
          ((⟨f.base x, hx⟩ : (U : Scheme.{u})) ∈
            (U : Scheme.{u}).basicOpen (trivializedSection φ s)) := by
  refine ⟨trivializationOfPullback f φ, fun x hx => ?_⟩
  rw [trivializedSection_trivializationOfPullback, ← Scheme.preimage_basicOpen_top]
  show (f ∣_ U).base ⟨x, hx⟩ ∈ (U : Scheme.{u}).basicOpen (trivializedSection φ s) ↔ _
  rw [show (f ∣_ U).base ⟨x, hx⟩ = (⟨f.base x, hx⟩ : (U : Scheme.{u})) from
    Subtype.ext (morphismRestrict_base_coe f U ⟨x, hx⟩)]
  exact Iff.rfl

/-- **The geometric step of EGA II 5.1.12** (PROVEN 2026-07-28): for a closed
immersion `f`, the non-vanishing locus of a pulled-back section is the preimage
of the non-vanishing locus.

**FAITHFULNESS — the version of this lemma WITHOUT `hL` is FALSE.**  Take
`Y = Spec k[u]`, `A` the skyscraper `k` at the origin `y₀`, `X = Spec k` and
`f : X ⟶ Y` the closed immersion of `y₀`, and `s = 1 ∈ Γ(A, ⊤) = k`.  Then
`f^*A ≅ 𝒪_X = k` and `f^*s` generates it, so `f^*s` does NOT vanish at the
point of `X`; but `A` admits NO trivialization `A|_U ≅ 𝒪_U` on any neighbourhood
of `y₀` (its sections form a `k`-line while `𝒪(U)` is infinite-dimensional), so
`NonvanishingAt A s y₀` is false and `nonvanishingLocus A s = ∅`.  The
conclusion would read `{pt} = f⁻¹ ∅ = ∅`.

**THE NUMERICAL-SEMIGROUP RISK IS RESOLVED — VERDICT: FAITHFUL AS STATED.**  The
open point recorded here was whether `IsAmpleSheaf L`, which guarantees only that
SOME power of `L` is locally trivial at each point, says anything at the
particular power `n`.  It does, and the bridge is
`isInvertibleSheaf_of_isAmpleSheaf` above (read its docstring for the two-step
argument): a trivialization of `L^{⊗m}` yields one of `L` by Stacks 01CV, after
which every power is locally trivial and `n` is not special.  **No hypothesis
needed adding, and none was added.**

**THREE HYPOTHESES ARE UNUSED, and this is a finding, not an accident.**
`[IsClosedImmersion f]`, `_hn : 0 < n` and `_hV : IsAffineOpen V` play no role.
The closed immersion was believed to be needed for the `⊆` direction, on the
grounds that it induces an isomorphism on residue fields; in fact basic opens
pull back along ANY morphism of schemes (`Scheme.preimage_basicOpen`), so the
whole argument is `Scheme.preimage_basicOpen_top` applied to `f ∣_ U`.  They are
kept because removing them would churn the call site in
`AbelianSchemeIsogeny.lean` for no gain, and because `isAmpleSheaf_modPullback`
wants the instance anyway for `IsAffineOpen.preimage`. -/
theorem nonvanishingLocus_modPullback_of_isAmpleSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {L : Y.Modules} (hL : IsAmpleSheaf L) {n : ℕ} (_hn : 0 < n)
    (s : Γ(modTensorPow L n, ⊤)) (V : Y.Opens) (_hV : IsAffineOpen V)
    (hloc : nonvanishingLocus (modTensorPow L n) s = (V : Set Y)) :
    nonvanishingLocus (modPullback f (modTensorPow L n))
        (modPullbackSection f (modTensorPow L n) s) = f.base ⁻¹' (V : Set Y) := by
  have hinv : IsInvertibleSheaf (modTensorPow L n) :=
    isInvertibleSheaf_modTensorPow (isInvertibleSheaf_of_isAmpleSheaf hL) n
  rw [← hloc]
  ext x
  obtain ⟨U, hU, ⟨φ⟩⟩ := hinv (f.base x)
  obtain ⟨ψ, hψ⟩ := exists_trivialization_modPullback f φ s
  have hxU : x ∈ f ⁻¹ᵁ U := hU
  rw [Set.mem_preimage]
  show NonvanishingAt _ _ x ↔ NonvanishingAt _ _ (f.base x)
  rw [nonvanishingAt_iff_trivializedSection _ ψ hxU,
    nonvanishingAt_iff_trivializedSection s φ hU]
  exact hψ x hxU

/-! ### The six original statements, now all PROVEN -/

/-- **Tensor powers add**: `L^{⊗n} ⊗ L^{⊗k} ≅ L^{⊗(n+k)}` — induction on `n`
over `nonempty_modTensor_assoc` and the left unitor. -/
theorem nonempty_modTensorPow_add {Z : Scheme.{u}} (L : Z.Modules) (n k : ℕ) :
    Nonempty (modTensor (modTensorPow L n) (modTensorPow L k) ≅ modTensorPow L (n + k)) := by
  induction n with
  | zero =>
    refine ⟨modTensorUnitLeftIso _ ≪≫ eqToIso ?_⟩
    rw [Nat.zero_add]
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨a⟩ := nonempty_modTensor_assoc L (modTensorPow L n) (modTensorPow L k)
    exact ⟨a ≪≫ modTensorMapIso (Iso.refl L) e ≪≫ eqToIso (by rw [Nat.succ_add]; rfl)⟩

/-- **Tensor powers multiply**: `(L^{⊗n})^{⊗m} ≅ L^{⊗(n*m)}` — induction on `m`
over `nonempty_modTensorPow_add`. -/
theorem nonempty_modTensorPow_mul {Z : Scheme.{u}} (L : Z.Modules) (n m : ℕ) :
    Nonempty (modTensorPow (modTensorPow L n) m ≅ modTensorPow L (n * m)) := by
  induction m with
  | zero => exact ⟨eqToIso (by rw [Nat.mul_zero]; rfl)⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨a⟩ := nonempty_modTensorPow_add L n (n * m)
    exact ⟨modTensorMapIso (Iso.refl _) e ≪≫ a ≪≫ eqToIso (by rw [Nat.mul_succ, Nat.add_comm])⟩

/-- **Ampleness is invariant under isomorphism** (PROVEN 2026-07-27).

`modTensorPowMapIso` transports the tensor power and `nonvanishingLocus_of_iso`
transports the locus; both were the obligations recorded here. -/
theorem isAmpleSheaf_of_iso {Z : Scheme.{u}} {L M : Z.Modules} (e : L ≅ M)
    (h : IsAmpleSheaf L) : IsAmpleSheaf M := by
  intro z
  obtain ⟨n, hn, s, V, hzV, hV, hloc⟩ := h z
  refine ⟨n, hn, (modTensorPowMapIso e n).hom.val.app (op ⊤) s, V, hzV, hV, ?_⟩
  rw [nonvanishingLocus_of_iso]
  exact hloc

/-- **A positive tensor power of an ample sheaf is ample** (PROVEN 2026-07-27,
over `nonempty_modTensor_assoc` and `exists_tensorPowSection`).

Given the ampleness datum `s : Γ(L^{⊗m}, ⊤)` at `z`, the witness for
`L^{⊗n}` is `s^{⊗n}`, read through
`(L^{⊗m})^{⊗n} ≅ L^{⊗(m*n)} = L^{⊗(n*m)} ≅ (L^{⊗n})^{⊗m}`. -/
theorem isAmpleSheaf_modTensorPow {Z : Scheme.{u}} {L : Z.Modules} {n : ℕ} (hn : 0 < n)
    (h : IsAmpleSheaf L) : IsAmpleSheaf (modTensorPow L n) := by
  intro z
  obtain ⟨m, hm, s, V, hzV, hV, hloc⟩ := h z
  obtain ⟨t, ht⟩ := exists_tensorPowSection (modTensorPow L m) s hn V hloc
  obtain ⟨e1⟩ := nonempty_modTensorPow_mul L m n
  obtain ⟨e2⟩ := nonempty_modTensorPow_mul L n m
  have e : modTensorPow (modTensorPow L m) n ≅ modTensorPow (modTensorPow L n) m :=
    e1 ≪≫ eqToIso (by rw [Nat.mul_comm]) ≪≫ e2.symm
  refine ⟨m, hm, e.hom.val.app (op ⊤) t, V, hzV, hV, ?_⟩
  rw [nonvanishingLocus_of_iso, ht]

/-- **`f^* 𝒪_Y ≅ 𝒪_X`** (PROVEN 2026-07-27 — free from the pin, via
`opensMapFinal`). -/
theorem nonempty_modPullback_modUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (modPullback f (modUnit Y) ≅ modUnit X) := ⟨modPullbackUnitIso f⟩

/-- **`f^*` commutes with tensor powers** (PROVEN 2026-07-27 over
`nonempty_modPullback_modTensor`): `f^*(L^{⊗n}) ≅ (f^*L)^{⊗n}`, by induction,
with the base case `f^* 𝒪_Y ≅ 𝒪_X` now proven. -/
theorem nonempty_modPullback_modTensorPow {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty (modPullback f (modTensorPow L n) ≅ modTensorPow (modPullback f L) n) := by
  induction n with
  | zero => exact ⟨modPullbackUnitIso f⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e0⟩ := nonempty_modPullback_modTensor f L (modTensorPow L n)
    exact ⟨e0 ≪≫ modTensorMapIso (Iso.refl _) e⟩

/-- **The restriction of an ample sheaf to a closed subscheme is ample**
(PROVEN 2026-07-27 over `nonempty_modPullback_modTensor` and
`nonvanishingLocus_modPullback_of_isAmpleSheaf`) — EGA II 5.1.12,
Hartshorne III Ex. 5.7. -/
theorem isAmpleSheaf_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    {L : Y.Modules} (h : IsAmpleSheaf L) : IsAmpleSheaf (modPullback f L) := by
  intro x
  obtain ⟨n, hn, s, V, hxV, hV, hloc⟩ := h (f.base x)
  obtain ⟨e⟩ := nonempty_modPullback_modTensorPow f L n
  refine ⟨n, hn, e.hom.val.app (op ⊤) (modPullbackSection f (modTensorPow L n) s),
    f ⁻¹ᵁ V, hxV, hV.preimage f, ?_⟩
  rw [nonvanishingLocus_of_iso]
  exact nonvanishingLocus_modPullback_of_isAmpleSheaf f h hn s V hV hloc

/-- **A quasi-compact scheme with AMPLE STRUCTURE SHEAF is QUASI-AFFINE**
(PROVEN 2026-07-27 over `nonvanishingLocus_modUnit`) — EGA II 5.1.2, and the
last step of the classical proof of the consumer.

The UNITOR obligation recorded here is discharged by `modTensorPowUnitIso`; the
well-definedness obligation is exactly `nonvanishingLocus_modUnit`.  The mathlib
half is `Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`. -/
theorem isQuasiAffine_of_isAmpleSheaf_modUnit (Z : Scheme.{u}) [CompactSpace Z]
    (h : IsAmpleSheaf (modUnit Z)) : Z.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen Z fun z => ?_
  obtain ⟨n, hn, s, V, hzV, hV, hloc⟩ := h z
  have hb : Z.basicOpen ((modTensorPowUnitIso n).hom.val.app (op ⊤) s) = V := by
    refine SetLike.coe_injective ?_
    rw [← nonvanishingLocus_modUnit, nonvanishingLocus_of_iso, hloc]
  exact ⟨(modTensorPowUnitIso n).hom.val.app (op ⊤) s, hb ▸ hV, hb ▸ hzV⟩

/-! ### THE PICARD GROUP: inverses, cancellation, and `RelPicEquiv` as an
equivalence relation

(New block, 2026-07-28, added for `relPicEquiv_sectionIdeal_of_aj_eq` in
`ModularCurve/X0.lean`.  Placed here rather than in `RelativePicard.lean` —
where `modTensor`, `IsInvertibleSheaf` and `RelPicEquiv` are *defined* —
because everything below consumes the tensor calculus of THIS module, and
`RelativePicard.lean` is upstream of it.)

**THIS BLOCK REFUTES A CLAIM THAT WAS IN TWO DOCSTRINGS.**  The docstring of
`relPicEquiv_sectionIdeal_of_aj_eq` asserted, dated 2026-07-28, that
"`modTensor` has no algebraic API anywhere in this development — no
associativity, no symmetry, no unit, and in particular no cancellation of an
invertible factor", and that `grep -rn 'modTensor' Fermat/` returns "**not one
lemma**".  Every clause of that is false.

*Not one lemma* — this module already held `modTensorMapIso` (functoriality on
isos), `modTensorUnitLeftIso`, `nonempty_modTensor_assoc`,
`modPullbackUnitIso`, `modPullbackMapIso`, `nonempty_modPullback_modTensor`,
`isInvertibleSheaf_modUnit` and `isInvertibleSheaf_modTensor`, all but two of
them PROVEN (`nonempty_modPullback_modTensor` is a leaf, and
`nonempty_modTensor_assoc` rests on `modLocW_whiskerLeft`).  It reaches
`X0.lean`: that file `public import`s `AbelianSchemeIsogeny`, which
`public import`s this one.

*No associativity* — `nonempty_modTensor_assoc`.

*No unit* — `modTensorUnitLeftIso`, and `modTensorUnitRightIso` below.

*No symmetry* — `modTensorComm` below, one line over mathlib's
`SymmetricCategory` instance on `PresheafOfModules`.  This is the clause that
cost the most: believing it, an earlier draft of this very block cut the
inverse leaf in a two-sided form it does not need.

*No cancellation of an invertible factor* — this was the ONE true clause, and
it is now `nonempty_iso_of_modTensor_left` / `RelPicEquiv.cancel_left` below,
PROVEN over the single new leaf.  The claim has been corrected in place at
`relPicEquiv_sectionIdeal_of_aj_eq`; the same assertion also stands, as of
2026-07-28, in the docstring of `relPicEquiv_sectionIdeal_of_aj_add_eq`
(X0.lean, the degree-`2` sibling), which is another owner's declaration and
has been left alone and reported instead.

What is genuinely missing is exactly ONE statement — that an invertible sheaf
has a tensor INVERSE (`exists_modTensor_inverse` below) — from which
cancellation, and with it symmetry and transitivity of `RelPicEquiv`, are
formal.  The corrected inventory is recorded on that leaf. -/

/-- **THE BRAIDING**, `L ⊗ M ≅ M ⊗ L` (PROVEN, one line) — `modTensor` is
SYMMETRIC.

Mathlib gives `PresheafOfModules.{u} (R ⋙ forget₂ _ _)` a
`SymmetricCategory` instance (`PresheafOfModules.Monoidal.symmetricCategory`,
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:145`) on **exactly
the same category** as the `monoidalCategory` instance one screen above it —
so `β_ L.val M.val` is available wherever `λ_ L.val` is, and sheafifying it is
the whole construction.

**Recorded because it was nearly missed.**  An earlier draft of this block
asserted that `Z.Modules` has no braiding at this pin, on the strength of a
grep of `Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` that returned
nothing — the grep had been run on the ORCHESTRATION host, where
`.lake/packages` does not exist (it is a symlink into machine-local
`/scratch` on the worker host, so the path silently resolves to nothing and
every mathlib grep returns empty).  Run mathlib greps on the host that owns
`.lake`.  Had the claim stood, `exists_modTensor_inverse` below would have
been cut twice as strong as it needs to be. -/
noncomputable def modTensorComm {Z : Scheme.{u}} (L M : Z.Modules) :
    modTensor L M ≅ modTensor M L :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (β_ L.val M.val)

-- **THE RIGHT UNITOR**, `M ⊗ 𝒪_Z ≅ M`, is NOT declared here.  It was added to this
-- file and to `ModularCurve/RelativePicard.lean` independently on the same day, under
-- the same name and in the same namespace; since this file imports that one, keeping
-- both is a `Fermat.modTensorUnitRightIso has already been declared` error.  The
-- upstream copy wins (release-18 merge).  It is constructed there from mathlib's
-- `ρ_` directly rather than from `modTensorComm` here; the two are propositionally
-- equal and every use below resolves to the imported one.

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

**Worth recording, because the module docstring above could be read as
forbidding this.**  That docstring says `Scheme.Modules` "has no `Module`
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
out of `exists_modTensor_inverse`) — an invertible `L` admits an invertible
`M` together with a GLOBAL morphism `ev : L ⊗ M ⟶ 𝒪_Z` that is an isomorphism
LOCALLY.

TRUE and classical (Hartshorne II.6.12, Stacks 01CV): take `M := L^∨ =
Hom_{𝒪_Z}(L, 𝒪_Z)` with `ev` the evaluation map.  On a trivializing open both
sides are `𝒪` and `ev` is the multiplication `𝒪 ⊗ 𝒪 ≅ 𝒪`, which is where the
local isomorphy comes from; `L^∨` is invertible for the same local reason.

**WHY THE MORPHISM `ev` IS PART OF THE STATEMENT AND CANNOT BE DROPPED.**  A
weaker-looking cut — "`∃ M` invertible with `modTensor L M` locally isomorphic
to `𝒪`" — is TRUE FOR EVERY `M`, hence useless: `isInvertibleSheaf_modTensor`
above already proves the tensor of two invertible sheaves is locally trivial.
Local triviality never gives a global isomorphism (`L` itself is the
counterexample), so what has to be produced locally is not an isomorphism but
the LOCAL ISOMORPHY OF ONE FIXED GLOBAL MAP.  With `ev` in hand,
`isIso_of_locally_isIso` above finishes, which is exactly how
`exists_modTensor_inverse` is proven below.

**This leaf is therefore EQUIVALENT to `exists_modTensor_inverse`, not weaker**
(given an inverse iso, take `ev` to be it: restrictions of an iso are isos).
The cut buys the prover the global-from-local step, which is the half that is
formal, and nothing else.  It is recorded here so that nobody re-derives it.

**WHAT IT NEEDS, re-surveyed 2026-07-28 ON THE WORKER HOST** (the earlier
survey was run where `.lake/packages` is a dangling symlink, and this module's
own `modTensorComm` docstring records what that cost):

* **No internal `Hom`, confirmed.**  `MonoidalClosed`/`ihom`/`internalHom`
  occur nowhere under `Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/`
  or `Mathlib/AlgebraicGeometry/`; the only monoidal-closed structures at this
  pin are `ModuleCat R` itself (`ModuleCat/Monoidal/Closed.lean`) and sheaves
  of TYPES (`Sites/Monoidal.lean`, `Sites/CartesianClosed.lean`).  So `L^∨`
  must be built by hand.
* **The GLUING route is NOT cheaper, and the previous docstring was wrong to
  call it "the recommended one".**  It asserted that gluing "needs only the
  descent already available through `nonempty_restrict_modTensor` and
  `trivializationOfLE` in this module".  Neither is descent:
  `nonempty_restrict_modTensor` says `⊗` commutes with restriction and
  `trivializationOfLE` shrinks a trivialization; neither manufactures a sheaf
  from local data.  Mathlib's descent machinery is abstract
  (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean`) and has **no instances
  anywhere in mathlib** — in particular it is not known here that
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

/-- **AN INVERTIBLE SHEAF HAS A TENSOR INVERSE** (PROVEN 2026-07-28 over
`exists_modDual` and `isIso_of_locally_isIso`) — i.e. the invertible sheaves
on `Z` form a GROUP under `⊗`, which is the whole content of "`Pic Z` is a
group" and the single missing input of the relative Picard calculus below.

The proof is the whole assembly: `exists_modDual` supplies an invertible `M`
and a global pairing `ev : L ⊗ M ⟶ 𝒪_Z` that is locally an isomorphism, and
`isIso_of_locally_isIso` upgrades that to `IsIso ev`.  All the mathematics has
moved to `exists_modDual`; read ITS docstring for the survey, the route, and
the falsity audit of `hL`.

**ONE SIDE IS ENOUGH, and deliberately so.**  `modTensorComm` above makes
`modTensor` symmetric, so `modTensor M L ≅ modUnit Z` follows from the stated
`modTensor L M ≅ modUnit Z` by composing with the braiding — which is what
`nonempty_iso_of_modTensor_left` does.  An earlier draft demanded both sides,
on a since-refuted belief that no braiding exists here; a prover should NOT
reinstate that, because the extra clause is free and therefore pure noise.

**Its consumers**: `nonempty_iso_of_modTensor_left` and `RelPicEquiv.symm`
below, hence (transitively) `relPicEquiv_sectionIdeal_of_aj_eq` and the whole
Abel–Jacobi monomorphism cone in `ModularCurve/X0.lean`. -/
theorem exists_modTensor_inverse {Z : Scheme.{u}} {L : Z.Modules}
    (hL : IsInvertibleSheaf L) :
    ∃ M : Z.Modules, IsInvertibleSheaf M ∧ Nonempty (modTensor L M ≅ modUnit Z) := by
  obtain ⟨M, ev, hM, hloc⟩ := exists_modDual hL
  haveI : IsIso ev := isIso_of_locally_isIso ev hloc
  exact ⟨M, hM, ⟨asIso ev⟩⟩

/-- **CANCELLATION OF AN INVERTIBLE TENSOR FACTOR** (PROVEN over
`exists_modTensor_inverse` and `nonempty_modTensor_assoc`): if `L` is
invertible then `L ⊗ A ≅ L ⊗ B` forces `A ≅ B`.

Tensor on the left with a left inverse `M` of `L` — obtained from the right
inverse through `modTensorComm` — and reassociate; `A` and `B` are arbitrary
`𝒪_Z`-modules, no invertibility of them is used or needed. -/
theorem nonempty_iso_of_modTensor_left {Z : Scheme.{u}} {L A B : Z.Modules}
    (hL : IsInvertibleSheaf L) (e : modTensor L A ≅ modTensor L B) : Nonempty (A ≅ B) := by
  obtain ⟨M, -, ⟨eLM⟩⟩ := exists_modTensor_inverse hL
  have eML : modTensor M L ≅ modUnit Z := modTensorComm M L ≪≫ eLM
  obtain ⟨aA⟩ := nonempty_modTensor_assoc M L A
  obtain ⟨aB⟩ := nonempty_modTensor_assoc M L B
  exact ⟨(modTensorUnitLeftIso A).symm ≪≫ modTensorMapIso eML.symm (Iso.refl A) ≪≫ aA ≪≫
    modTensorMapIso (Iso.refl M) e ≪≫ aB.symm ≪≫ modTensorMapIso eML (Iso.refl B) ≪≫
    modTensorUnitLeftIso B⟩

section RelPicGroupoid

variable {X S T : Scheme.{u}} {strX : X ⟶ S} {g : T ⟶ S}

/-- **`RelPicEquiv` is REFLEXIVE** (PROVEN): take `N := 𝒪_T` and use the right
unitor together with `f^* 𝒪_T ≅ 𝒪_{X_T}`. -/
theorem RelPicEquiv.refl (L : (curveBaseChange strX g).Modules) : RelPicEquiv strX g L L :=
  ⟨modUnit T, isInvertibleSheaf_modUnit T,
    ⟨(modTensorUnitRightIso L).symm ≪≫
      modTensorMapIso (Iso.refl L) (modPullbackUnitIso _).symm⟩⟩

/-- **`RelPicEquiv` is TRANSITIVE** (PROVEN over `nonempty_modTensor_assoc`
and `nonempty_modPullback_modTensor`): the twisting sheaves multiply, and
`M ⊗ N` is invertible by `isInvertibleSheaf_modTensor`. -/
theorem RelPicEquiv.trans {L L' L'' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') (h' : RelPicEquiv strX g L' L'') : RelPicEquiv strX g L L'' := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨M, hM, ⟨e'⟩⟩ := h'
  obtain ⟨a⟩ := nonempty_modTensor_assoc L'' (modPullback (curveBaseChangeProj strX g) M)
    (modPullback (curveBaseChangeProj strX g) N)
  obtain ⟨pmn⟩ := nonempty_modPullback_modTensor (curveBaseChangeProj strX g) M N
  exact ⟨modTensor M N, isInvertibleSheaf_modTensor hM hN,
    ⟨e ≪≫ modTensorMapIso e' (Iso.refl _) ≪≫ a ≪≫ modTensorMapIso (Iso.refl L'') pmn.symm⟩⟩

/-- **`RelPicEquiv` is SYMMETRIC** (PROVEN over `exists_modTensor_inverse`):
twist back by the inverse of the twisting sheaf.

This is the step that makes `RelPicEquiv` an equivalence relation, and hence
`Pic(X_T)/Pic(T)` a group rather than a preorder — which is what its consumers
in `ModularCurve/X0.lean` (`aj_spec` read at two different points) silently
assume. -/
theorem RelPicEquiv.symm {L L' : (curveBaseChange strX g).Modules}
    (h : RelPicEquiv strX g L L') : RelPicEquiv strX g L' L := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨M, hM, ⟨eNM⟩⟩ := exists_modTensor_inverse hN
  obtain ⟨a⟩ := nonempty_modTensor_assoc L' (modPullback (curveBaseChangeProj strX g) N)
    (modPullback (curveBaseChangeProj strX g) M)
  obtain ⟨pnm⟩ := nonempty_modPullback_modTensor (curveBaseChangeProj strX g) N M
  exact ⟨M, hM, ⟨(modTensorUnitRightIso L').symm ≪≫
    modTensorMapIso (Iso.refl L') ((modPullbackUnitIso _).symm ≪≫
      modPullbackMapIso _ eNM.symm ≪≫ pnm) ≪≫ a.symm ≪≫
    modTensorMapIso e.symm (Iso.refl _)⟩⟩

/-- **CANCELLATION IN THE RELATIVE PICARD GROUP** (PROVEN over
`nonempty_iso_of_modTensor_left`): an invertible factor common to both sides
of a `RelPicEquiv` may be deleted.

`A` and `B` are arbitrary — only the CANCELLED factor `L` has to be
invertible.  This is what lets `IsRelPicZeroOf.aj_spec`, which is an equation
about `𝒪(x − o) ⊗ 𝒪(−x)`, be turned into a statement about `𝒪(−x)` alone. -/
theorem RelPicEquiv.cancel_left {L A B : (curveBaseChange strX g).Modules}
    (hL : IsInvertibleSheaf L)
    (h : RelPicEquiv strX g (modTensor L A) (modTensor L B)) : RelPicEquiv strX g A B := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  obtain ⟨a⟩ := nonempty_modTensor_assoc L B (modPullback (curveBaseChangeProj strX g) N)
  obtain ⟨f⟩ := nonempty_iso_of_modTensor_left hL (e ≪≫ a)
  exact ⟨N, hN, ⟨f⟩⟩

end RelPicGroupoid

end Fermat
