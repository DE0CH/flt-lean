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
and what is left is ONE leaf:

* `modLocW_whiskerLeft` — TENSORING PRESERVES LOCAL ISOMORPHISMS.  Read its
  docstring: it carries the entire content of "sheafification is monoidal", and
  names the two routes (internal hom, as in `Sites/Monoidal.lean`; or free
  presentations, as in `ModuleCat/Presheaf/Generator.lean`).

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

OPEN — six leaves.  Two are the original ones:

* `modLocW_whiskerLeft` — SHEAFIFICATION IS MONOIDAL, in the one instance
  needed, and now stated at the level where the mathematics actually lives
  (local isomorphisms are stable under `X ⊗ -`).  The deepest of the four;
  everything about tensor *powers* (`nonempty_modTensorPow_add`,
  `nonempty_modTensorPow_mul`) is derived from it here through
  `nonempty_modTensor_assoc`, so it is the only associativity obligation left
  anywhere.
* `nonempty_modPullback_modTensor` — monoidality of `f^*` on objects.  With
  `modPullbackUnitIso` proven, this is all that
  `nonempty_modPullback_modTensorPow` needs, and — through
  `nonempty_restrict_modTensor`, which is derived from it in three lines — it is
  also the only input the whole trivialization calculus has left.

Four are new, and each is strictly smaller than the leaf it came out of:

* `exists_trivialization_of_modTensorPow` — **the mathematical one**: Stacks
  01CV, the semigroup bridge.  It is the only one of the six that is not
  bookkeeping.  **PROVEN 2026-07-29** by reduction (one line, since
  `modTensorPow A (j+1)` IS `modTensor A (modTensorPow A j)`) to the classical
  TWO-FACTOR statement `exists_trivialization_of_modTensor_trivial`, which is
  where the mathematics and the corrected route audit now live.
* `trivializedSection_trivializationOfLE` — **PROVEN 2026-07-28.**  It was never
  mathematics; it was blocked by `modRestrictLEIso` being routed through
  `modPullback`.  Rerouting that through mathlib's `restrictFunctorCongr` +
  `restrictFunctorComp` (both `app`s are `rfl`) closed it.
* `exists_trivialization_tensorPow` — **PROVEN 2026-07-28**, by induction, over
  ONE new leaf `exists_trivialization_modTensor` ("a trivialization of a tensor
  product multiplies sections").  That cut is a CORRECTION: the route recorded
  here relied on reading `trivializedSection` through the anonymous iso supplied
  by `nonempty_restrict_modTensor`, which pins nothing — see that leaf's
  docstring for the unit-scaling counterexample.
  **`exists_trivialization_modTensor` is itself PROVEN 2026-07-29**, in the
  `§ The CANONICAL trivialization of a tensor product` block; the anonymous iso
  is used there for EXISTENCE only, and the value comes from a canonical
  morphism built out of the sheafification adjunction.  So the trivialization
  calculus is down to `exists_trivialization_modPullback` plus the mathematical
  leaf below.
* `exists_trivialization_modPullback` — the same for `f^*`.

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

/-! ### Pseudo-functoriality of `modPullback` (PROVEN — free from the pin) -/

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

/-! ### The monoidal structure that `modTensor` inherits from presheaves

`RelativePicard.lean` built only the object part of `⊗` because "building the
monoidal category would require knowing that sheafification is monoidal".  That
is true of the ASSOCIATOR and false of everything else: functoriality and both
unitors come for free from the presheaf-level monoidal category together with
the fact that the sheafification adjunction has invertible counit. -/

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

The morphism part that `RelativePicard.lean` declined to define: sheafify
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

/-! ### Pullback of a global section, and `f^* 𝒪_Y ≅ 𝒪_X` -/

/-- **The pullback of a global section**, `f^* s ∈ Γ(f^*A, ⊤)`.

Obtained from the unit `A ⟶ f_* f^* A` of the pullback/pushforward adjunction
evaluated on global sections; `Γ(f_*N, ⊤) = Γ(N, f ⁻¹ᵁ ⊤) = Γ(N, ⊤)` is
definitional. -/
noncomputable def modPullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    (s : Γ(A, ⊤)) : Γ(modPullback f A, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op ⊤) s

/-- **`Opens.map g` is a FINAL functor**, for every continuous `g : X ⟶ Y`.

This refutes the note recorded against `nonempty_modPullback_modUnit`, which
said finality of the site functor "is not automatic for `Opens.map f`".  It is:
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

/-- **TENSORING PRESERVES LOCAL ISOMORPHISMS** (sorry leaf).  This is the entire
mathematical content of "sheafification is monoidal" for `𝒪_Z`-modules: with it,
`MorphismProperty.IsMonoidal (modLocW Z)` holds, and every associativity and
unit statement about `modTensor` follows formally.

Concretely: if `g` becomes an isomorphism after sheafification, so does
`X ◁ g : X ⊗ Y₁ ⟶ X ⊗ Y₂`.  Unfolded through
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` and
`GrothendieckTopology.WEqualsLocallyBijective`, it says that `X ⊗ -` preserves
LOCAL BIJECTIVITY of maps of abelian presheaves.

TRUE, and standard (Stacks 01LA; Mac Lane VII).  Note it is NOT a formal
consequence of right exactness alone: local surjectivity of `X ◁ g` is the easy
half (a section of `X ⊗ Y₂` is a finite sum of tensors, each of whose right
factors lifts locally, and finitely many covering sieves may be intersected),
while local INJECTIVITY has to rule out a `Tor`-type contribution.

TWO ROUTES, neither yet tried here.

1. *Internal hom.*  This is exactly how mathlib proves the analogous
   `CategoryTheory.GrothendieckTopology.W.whiskerLeft` for `Sheaf J A` with `A`
   monoidal closed (`Mathlib/CategoryTheory/Sites/Monoidal.lean`): `modLocW` is
   `ObjectProperty.isLocal` of "is a sheaf", so membership means
   `Hom(X ⊗ Y₂, H) → Hom(X ⊗ Y₁, H)` is bijective for every sheaf `H`; currying
   turns that into `Hom(Y₂, ihom X H) → Hom(Y₁, ihom X H)`, which is `hg`
   applied to the sheaf `ihom X H`.  What is missing at this pin is the internal
   hom of PRESHEAVES OF MODULES (mathlib has `MonoidalClosed` for `ModuleCat`
   and for functor categories, but not for `PresheafOfModules`), together with
   the analogue of `Presheaf.isSheaf_functorEnrichedHom`.

2. *Free presentations.*  `Mathlib/Algebra/Category/ModuleCat/Presheaf/`
   `Generator.lean` presents every `X` as a cokernel
   `X.freeYonedaCoproduct ⟶ X` of a map between coproducts of
   `(free R).obj (yoneda.obj U)` (`isColimitFreeYonedaCoproductsCokernelCofork`;
   available here because `Z.Opens` is a `SmallCategory`).  Both
   `MonoidalCategory.tensorRight Y` (instance in
   `ModuleCat/Presheaf/Monoidal.lean`) and sheafification preserve colimits, so
   it suffices to know the statement for `X` FREE — where `X ⊗ Y` is a direct
   sum of copies of `Y` indexed by `F U`, and local bijectivity is
   componentwise.  The residue of this route is therefore
   `modLocW ((PresheafOfModules.free _).obj F ◁ g)` for `F : Cᵒᵖ ⥤ Type u`,
   plus the cokernel comparison.

3. *Stalks* — and this is probably the right one HERE, because the site is the
   site of OPENS of a topological space, which is special.  `Mathlib/Topology/
   Sheaves/Points.lean` proves `GrothendieckTopology.HasEnoughPoints
   (Opens.grothendieckTopology X)`: the points of the space form a conservative
   family of points of the site.  `Mathlib/CategoryTheory/Sites/Point/`
   `IsMonoidalW.lean` then derives `(J.W).IsMonoidal` from exactly that, by
   checking `IsIso` STALKWISE and using `Functor.Monoidal.map_tensor` — see
   `ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`.  That instance is
   *not* directly usable here, because it is about the tensor product of
   `Cᵒᵖ ⥤ AddCommGrpCat` (over `ℤ`) and not the `𝒪_Z`-linear one; but the
   argument transports verbatim once one has a MONOIDAL stalk functor
   `PresheafOfModules Z.ringCatSheaf.obj ⥤ ModuleCat 𝒪_{Z,z}`, i.e. the single
   fact that

       colim_{U ∋ z} (X(U) ⊗_{𝒪(U)} Y(U))  ≅  X_z ⊗_{𝒪_{Z,z}} Y_z,

   a filtered colimit of tensor products over a filtered system of base rings.
   With that, `modLocW Z (X ◁ g)` is stalkwise `𝟙 ⊗ g_z`, and `g_z` is an
   isomorphism because `g ∈ modLocW Z`.  This is the smallest genuinely new
   input of the three routes. -/
theorem modLocW_whiskerLeft {Z : Scheme.{u}} (X : PresheafOfModules.{u} Z.ringCatSheaf.obj)
    {Y₁ Y₂ : PresheafOfModules.{u} Z.ringCatSheaf.obj} {g : Y₁ ⟶ Y₂}
    (hg : modLocW Z g) : modLocW Z (X ◁ g) := sorry

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

Each is strictly smaller than one of the six statements it replaced, and each
names in its docstring what it needs.  Between them they are the residue of the
ampleness theory that `Mathlib/AlgebraicGeometry/` does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY at this pin — re-run it
before believing this sentence).

The other four open leaves are further down, in the trivialization calculus that
begins after `nonvanishingLocus_modUnit`; only one of them
(`exists_trivialization_of_modTensorPow`) is mathematics. -/

/-- **THE ASSOCIATOR** — PROVEN (2026-07-28): `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` for
`𝒪_Z`-modules.

The route recorded in the previous version of this docstring — pair
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` with
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean` — is the one that
works; see the section above.  The whole associativity question is now carried
by the single leaf `modLocW_whiskerLeft` ("tensoring preserves local
isomorphisms"), from which the localized monoidal structure, and with it this
associator, both unitors and the braiding, are formal.

Everything else about tensor powers in this file (`nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, and hence `isAmpleSheaf_modTensorPow`) is DERIVED
from this statement, so `modLocW_whiskerLeft` is the single associativity
obligation of the module. -/
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
`f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`.

`Scheme.Modules.pullback` is a left adjoint and the presheaf-level tensor is a
colimit-friendly construction, so this is expected to follow from the
presheaf-level statement (base change of modules is monoidal:
`S ⊗_R (M ⊗_R N) ≅ (S ⊗_R M) ⊗_S (S ⊗_R N)`) plus the same
sheafification-is-monoidal input as `nonempty_modTensor_assoc`.

With `modPullbackUnitIso` PROVEN, this is the only obligation of
`nonempty_modPullback_modTensorPow` — and, since 2026-07-28, the only input of
the trivialization calculus below as well (`nonempty_restrict_modTensor` is
three lines over it, via `Scheme.Modules.restrictFunctorIsoPullback`).  So this
is now the ONLY leaf in the module that anything except
`exists_trivialization_of_modTensorPow` waits on.

ROUTE AUDIT (2026-07-28; each claim below was checked against the pin, and each
names the check that would refute it).

* `Scheme.Modules.pullback f` is DEFINED as an abstract left adjoint
  (`PresheafOfModules.pullback φ := (pushforward φ).leftAdjoint`, and the sheaf
  version through `SheafOfModules.pullbackPushforwardAdjunction`).  So there is
  no formula to compute with, and a hands-on construction of the comparison map
  is not available: `grep -n "def pullback" Mathlib/Algebra/Category/ModuleCat/
  {Sheaf,Presheaf}/*.lean`.
* The pushforward with NO change of rings IS strong monoidal at this pin —
  `PresheafOfModules.pushforward₀OfCommRingCat F R` carries a `.Monoidal`
  instance with `μIso _ _ := Iso.refl _`
  (`Presheaf/PushforwardZeroMonoidal.lean`, one declaration, added 2026).  The
  ring-CHANGING pushforward is only lax, and the left adjoint of a lax monoidal
  functor is oplax, which is what supplies the canonical comparison
  `f^*(L ⊗ M) ⟶ f^*L ⊗ f^*M`.  The content of this leaf is that it is an ISO.
* The natural route to that is: `f^*` preserves colimits (it is a left adjoint),
  `- ⊗ -` preserves colimits in each variable, and the FREE case is already in
  the pin — `SheafOfModules.pullbackObjFreeIso (I : Type u) : (pullback φ).obj
  (free I) ≅ free I` and `pullbackObjUnitToUnit` (`Sheaf/PullbackFree.lean`,
  which this module already imports).  Every sheaf of modules is locally a
  quotient of frees (`Sheaf/Generators.lean`, `LocalGeneratorsData`).
* A prover who wants a smaller first target: the OPEN IMMERSION case is strictly
  easier and is what everything below actually consumes.  For an open immersion
  `Scheme.Modules.restrictFunctor` is a `SheafOfModules.pushforward` along
  `f.opensFunctor` with an ISOMORPHISM of ring presheaves, hence objectwise on
  presheaves, where the tensor product is also objectwise
  (`PresheafOfModules.Monoidal.tensorObj` sends `X` to `M₁.obj X ⊗ M₂.obj X`);
  the only real step left is that sheafification commutes with restriction to an
  open subsite.  It is NOT stated as a separate leaf here only because it is a
  three-line corollary of this one, and a redundant leaf is worse than a hint.

PIN CHECK 2026-07-28.  The second bullet's load-bearing claim was re-run and
STANDS: `Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`
is present at this pin.

One addition to the last bullet, and it raises that bullet's priority.  The OPEN
IMMERSION case is not merely "a smaller first target" — it is what
`nonempty_restrict_modTensor`, the whole trivialization calculus, and the new
leaf `exists_trivialization_modTensor` all wait on.  And that last leaf needs
strictly more than this one gives: it needs the comparison to be **canonical**,
with a known effect on `tensorSection`, not merely to EXIST.  A `Nonempty`
comparison can be post-composed with multiplication by any unit of `Γ(U, ⊤)`,
which is invisible to every clause stated here.  So a prover closing this leaf
should consider delivering a NAMED isomorphism rather than a `Nonempty` — the
`Nonempty` packaging is precisely what forced that leaf to be cut. -/
theorem nonempty_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M)) := sorry

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

**CORRECTED 2026-07-28.**  A previous version of this note said the section was
routed through `modPullback` rather than through
`Scheme.Modules.restrictFunctorComp` because `restrictFunctor` carries an
`[IsOpenImmersion f]` instance argument, "so transporting it along
`Scheme.homOfLE_ι` needs a congruence over that instance, whereas
`modPullbackCongrIso` does exactly that job with no instance juggling".

**The premise is false, and the refuting check is one grep**: the pin already has
`Scheme.Modules.restrictFunctorCongr` (`Mathlib/AlgebraicGeometry/Modules/`
`Sheaf.lean`), which is precisely a congruence of `restrictFunctor` over equal
open immersions, instance argument included.  The detour was not merely
unnecessary, it was the whole obstruction: `modPullback`'s comparison
isomorphisms come from `Adjunction.leftAdjointUniq` and compute with nothing,
whereas **`restrictFunctorCongr_hom_app_app` and `restrictFunctorComp_hom_app_app`
are both `rfl`**, each equal to a bare `M.presheaf.map (eqToHom _).op`.  Rerouting
`modRestrictLEIso` through them is what turned
`trivializedSection_trivializationOfLE` from a sorry into a proof.

The `modPullback*Iso` family is untouched and still PROVEN above; it keeps its
own consumers in `AbelianSchemeIsogeny.lean` and in the recorded route of
`exists_trivialization_modPullback`. -/

/-- **Restriction along an open immersion IS the pullback** —
`Scheme.Modules.restrictFunctorIsoPullback`, read on an object.  This is what
makes the whole calculus below depend on `nonempty_modPullback_modTensor` and on
nothing else. -/
noncomputable def modRestrictPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (A : Y.Modules) : A.restrict f ≅ modPullback f A :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app A

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

/-- **`A|_W ≅ (A|_U)|_W` for `W ≤ U`** (PROVEN).

**REROUTED 2026-07-28**, from the `modPullback` pseudo-functoriality chain to
mathlib's own `restrictFunctorCongr` + `restrictFunctorComp`.  The statement is
unchanged; what changes is that the isomorphism now COMPUTES.  Both components
are `rfl`-equal to `A.presheaf.map (eqToHom _).op`
(`Scheme.Modules.restrictFunctorCongr_hom_app_app`,
`Scheme.Modules.restrictFunctorComp_hom_app_app`), whereas the `modPullback`
route went through `Adjunction.leftAdjointUniq` and was opaque on sections.  See
the section docstring above; this is what closed
`trivializedSection_trivializationOfLE`. -/
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

/-- **Restricting a trivialization restricts the trivialized section** (PROVEN
2026-07-28).  Pure plumbing — no mathematics.

**What unblocked it.**  The previous version of this docstring recorded the leaf
as blocked because `modRestrictLEIso` was "routed through `modPullback`, whose
component isomorphisms come from `Adjunction.leftAdjointUniq` and are therefore
not definitional".  That diagnosis was exactly right; the recorded FIX was not.
It proposed rebuilding `modRestrictLEIso` from `restrictFunctorComp` alone, with
the `[IsOpenImmersion]` congruence discharged by an `eqToIso` plus `congr 1`.
That is unnecessary: **the pin already has
`Scheme.Modules.restrictFunctorCongr`**, so no hand-rolled `eqToIso` is needed
and no "motive is not type correct" ever arises.  With `modRestrictLEIso`
rerouted through `restrictFunctorCongr ≪≫ restrictFunctorComp`, every component
is `rfl`.

The old note also warned that "the identity is still NOT `rfl`" and that
`unfold`+`simp` on `restrictUnitIso` and `restrictFunctorComp` PANICS the
elaborator.  Both remain true, and neither is needed: the proof below never
unfolds those, it splits the composite by `rfl` and then does exactly one
naturality step.  The three `rfl` splits are the reason it is short —

* `restrictFunctor g` applied to a morphism is that morphism at `g ''ᵁ ⊤`;
* `restrictUnitIso g` on sections is `(g.appIso ⊤).hom`;
* `restrictAppIso` is `Iso.refl`, so `trivializedSection` is a bare
  `presheaf.map` followed by the trivialization.

What is left is `hkey` (three presheaf maps out of `op ⊤` collapse to one,
because `Z.Opensᵒᵖ` has subsingleton hom-sets), the naturality of `φ.hom.val`
between `op ⊤` and `op (g ''ᵁ ⊤)`, and `Scheme.Hom.map_appLE` for the last
step. -/
theorem trivializedSection_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfLE h φ) s
      = (Z.homOfLE h).appTop (trivializedSection φ s) := by
  have hD : ∀ x : Γ(A.restrict W.ι, ⊤),
      (modRestrictLEIso A h).hom.val.app (op ⊤) x
        = A.presheaf.map (eqToHom (show U.ι ''ᵁ (Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens))
              = (Z.homOfLE h ≫ U.ι) ''ᵁ (⊤ : (W : Scheme.{u}).Opens) by
            simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr h])).op
            (A.presheaf.map (eqToHom (show (Z.homOfLE h ≫ U.ι) ''ᵁ (⊤ : (W : Scheme.{u}).Opens)
              = W.ι ''ᵁ (⊤ : (W : Scheme.{u}).Opens) by simp)).op x) :=
    fun _ => rfl
  have hkey : (modRestrictLEIso A h).hom.val.app (op ⊤)
        (A.presheaf.map (homOfLE (le_top : W.ι ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op s)
      = (A.restrict U.ι).presheaf.map
          (homOfLE (le_top : Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op
          (A.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op s) := by
    have hG : (A.restrict U.ι).presheaf.map
          (homOfLE (le_top : Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op
          (A.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op s)
        = A.presheaf.map (U.ι.opensFunctor.map
            (homOfLE (le_top : Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤))).op
            (A.presheaf.map
              (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op s) := rfl
    rw [hD, hG]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1
  calc trivializedSection (trivializationOfLE h φ) s
      = ((Z.homOfLE h).appIso ⊤).hom
          (φ.hom.val.app (op (Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens)))
            ((modRestrictLEIso A h).hom.val.app (op ⊤)
              (A.presheaf.map
                (homOfLE (le_top : W.ι ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op s))) := rfl
    _ = ((Z.homOfLE h).appIso ⊤).hom
          (φ.hom.val.app (op (Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens)))
            ((A.restrict U.ι).presheaf.map
              (homOfLE (le_top : Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op
              (A.presheaf.map
                (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op s))) := by
        rw [hkey]
    _ = ((Z.homOfLE h).appIso ⊤).hom
          ((U : Scheme.{u}).presheaf.map
            (homOfLE (le_top : Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens) ≤ ⊤)).op
            (trivializedSection φ s)) :=
        congrArg _ (PresheafOfModules.naturality_apply φ.hom.val
          (X := op (⊤ : (U : Scheme.{u}).Opens))
          (Y := op (Z.homOfLE h ''ᵁ (⊤ : (W : Scheme.{u}).Opens)))
          (homOfLE le_top).op
          (A.presheaf.map (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op s))
    _ = (Z.homOfLE h).appTop (trivializedSection φ s) := by
        rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE,
          Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        simp

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

/-- `𝒪_Z` is invertible.  (Recorded as a one-liner in `RelativePicard.lean`'s
docstring for `IsInvertibleSheaf`; it has a consumer now, so it is a
declaration.) -/
theorem isInvertibleSheaf_modUnit (Z : Scheme.{u}) : IsInvertibleSheaf (modUnit Z) :=
  fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : Z.Opens).ι⟩⟩

/-- **A tensor product of invertible sheaves is invertible** (PROVEN over
`nonempty_restrict_modTensor`): trivialize both over `U ⊓ V`. -/
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

/-- **AN INVERTIBLE SHEAF OF MODULES IS LOCALLY FREE OF RANK ONE** (sorry leaf,
cut 2026-07-29 out of `exists_trivialization_of_modTensorPow`) — Stacks 0B8L /
01CV, Hartshorne II.6.12, in its classical TWO-FACTOR form: if `L ⊗ N` is trivial
on `U` for SOME `N`, then `L` is trivial near each point of `U`.

**This is the single mathematical leaf of the module** (`modLocW_whiskerLeft` and
`nonempty_modPullback_modTensor` aside), and it is the whole content of the
numerical-semigroup worry recorded against
`nonvanishingLocus_modPullback_of_isAmpleSheaf`.

**FAITHFUL, and strictly stronger than the tensor-power form it came from.**
`modTensorPow A (j+1)` is `modTensor A (modTensorPow A j)` definitionally, so the
power statement is the special case `N = A^{⊗j}`; the `0 < k` hypothesis of the
consumer is exactly what produces the `j`.  Nothing else about `N` is used or
true: `N` is an arbitrary `𝒪_Z`-module, as in Stacks, and the statement holds
over an arbitrary RINGED SPACE — no quasi-coherence, no scheme hypothesis beyond
what `Z.Modules` already carries.

WHY IT IS TRUE.  Near a point, `ν⁻¹(1) = Σ_{i≤m} s_i ⊗ t_i` for finitely many
sections; writing `λ_i(x) := ν(x ⊗ t_i)` one has `Σ_i λ_i(s_i) = ν(ν⁻¹ 1) = 1`,
so some `λ_i(s_i)` is a unit on a neighbourhood `W` of the given point (a sum of
sections equal to `1` cannot have every term in the maximal ideal at a point, so
the basic opens `W_i := basicOpen (λ_i(s_i))` cover).  On that `W`, `s_i`
generates and `c⁻¹λ_i` is inverse to `r ↦ r·s_i`.

**ROUTE AUDIT 2026-07-29 — this CORRECTS the audit that stood here.**  The old
note said the blocker is the missing STALK-MODULE structure.  That is true of the
route it had in mind and it is not the whole story, and naming only stalks sends
a prover at the wrong subtree.  Re-running the checks:

* **CONFIRMED, and it is the old note's one surviving claim.**
  `grep -rln stalk Mathlib/Algebra/Category/ModuleCat/{Presheaf,Sheaf}/` is still
  **EMPTY** at this pin, so `A_y` cannot even be *said* to be invertible over
  `𝒪_y`.  (`Scheme.Modules.restrictStalkNatIso` exists but is a stalk of the
  underlying `Ab`-presheaf and carries no `Module` structure.)
* **NEWLY FOUND, and NOT previously recorded: the LOCAL PRESENTATION half is
  already available.**  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean`
  carries `instance : IsLocallySurjective J (toSheafify α φ)` (line 352 at this
  pin), and `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`
  identifies `modTensorMk` with `CategoryTheory.toSheafify` on underlying
  presheaves.  So "`ν⁻¹(1)` is locally a finite sum of pure tensors" needs no new
  theory — only the unfolding of local surjectivity over the Opens topology into
  its pointwise form.  Refuting check: the `grep` above on `Sheafify.lean`.
* **THE OBSTRUCTION IS THE SYMMETRY, NOT THE STALKS.**  The endgame is the
  generation identity `x = Σ_i λ_i(x)·s_i`, and it is NOT a consequence of
  `Σ_i λ_i(s_i) = 1` by any amount of bilinearity: the derivation is
  `x ⊗ 1 = Σ_i x ⊗ s_i ⊗ t_i ↦ Σ_i s_i ⊗ x ⊗ t_i = Σ_i λ_i(x)·s_i ⊗ 1`, which
  uses the ASSOCIATOR and the BRAIDING of `L ⊗ L ⊗ N`.  (Equivalently: the two
  maps `L⊗N⊗L⊗N → 𝒪`, `ν₁₄·ν₃₂` and `ν₁₂·ν₃₄`, agree on `ν⁻¹(1) ⊗ x ⊗ u` — a
  symmetry statement.)  Both structures EXIST here, through
  `nonempty_modTensor_assoc` and the braiding of `ModLM Z` — but only ABSTRACTLY:
  `Localization.Monoidal.μ` comes from the localization's universal property, so
  its effect on `modTensorMk`-image sections does not compute.  This is the same
  defect, one level up, that forced `exists_trivialization_modTensor` to be cut,
  and the fix there (build a canonical MORPHISM out of the sheafification instead
  of reading an abstract iso) does not apply, because here the needed map goes
  INTO a tensor product.
* **CONSEQUENCE WORTH ACTING ON: one piece of machinery closes two of this
  module's four remaining leaves.**  The monoidal stalk functor named as route 3
  of `modLocW_whiskerLeft` — `colim_{V ∋ y} (X(V) ⊗_{𝒪(V)} Y(V)) ≅ X_y ⊗_{𝒪_y} Y_y`
  — supplies BOTH: it closes `modLocW_whiskerLeft` (stalkwise `𝟙 ⊗ g_y`), and it
  reduces this leaf to commutative algebra over the local ring `𝒪_y`, where the
  symmetry is mathlib's own `TensorProduct.comm` and computes.  A prover sent at
  the stalk functor is therefore worth two leaves, not one.
* Unchanged and still useful: `Mathlib/Algebra/Category/ModuleCat/Sheaf/`
  `LocallyFree.lean` EXISTS, supplying `SheafOfModules.IsLocallyFree`,
  `LocalGeneratorsData.IsLocallyFreeData` and `GeneratingSections`.  Those are
  DEFINITIONS, not this theorem — "invertible implies locally free of rank one"
  is still absent from the pin — but the finite-generation half above is literally
  a `LocalGeneratorsData`, and `free.generatingSections` gives the rank-one model.

Do NOT weaken this to a hypothesis on the consumers instead: `IsAmpleSheaf` is
what the consumer `exists_isAmpleSheaf_cube_of_isAlgClosed` produces, and it
produces `IsInvertibleSheaf` beside it — so the ALTERNATIVE repair (thread
`IsInvertibleSheaf L` through `nonvanishingLocus_modPullback_of_isAmpleSheaf` and
`isAmpleSheaf_modPullback`, and stop discarding it at the call site in
`AbelianSchemeIsogeny.lean`, where it is currently bound to `-`) is available and
costs nothing mathematically.  It is not taken here because the statement as
given is TRUE, and weakening a true statement to dodge a proof is exactly what
the faithfulness rule forbids. -/
theorem exists_trivialization_of_modTensor_trivial {Z : Scheme.{u}} {L N : Z.Modules}
    {U : Z.Opens}
    (hν : Nonempty ((modTensor L N).restrict U.ι ≅ modUnit (U : Scheme.{u})))
    {z : Z} (hz : z ∈ U) :
    ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ Nonempty (L.restrict W.ι ≅ modUnit (W : Scheme.{u})) := sorry

/-- **AN INVERTIBLE SHEAF OF MODULES IS LOCALLY FREE OF RANK ONE, in the tensor
power form the audit needs** (PROVEN 2026-07-29 over
`exists_trivialization_of_modTensor_trivial`): if SOME positive tensor power of
`A` is trivial on `U`, then `A` itself is trivial on a smaller neighbourhood of
each point of `U`.

One line, because `modTensorPow A (j+1)` IS `modTensor A (modTensorPow A j)`
definitionally; `hk` is used exactly to produce the `j`.  The mathematics, and
the route audit, are on `exists_trivialization_of_modTensor_trivial` above.

The paragraph below is retained from the previous version of this docstring
because its analysis of the argument is still exactly right; note only that the
"stalks are the blocker" reading of it is corrected above.

Stalks first: sheafification preserves
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

Two amendments to that paragraph, both 2026-07-29 and both recorded in full on
`exists_trivialization_of_modTensor_trivial`: the "near each point
`1 = Σ_i s_i ⊗ t_i`" step is NOT missing from the pin (it is local surjectivity
of the sheafification unit, `Sheafify.lean`'s
`instance : IsLocallySurjective J (toSheafify α φ)`), and the
`m = Σ_i ⟨t_i, m⟩ s_i` step needs the BRAIDING, which is what is actually
blocked here — not merely the stalks. -/
theorem exists_trivialization_of_modTensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    {k : ℕ} (hk : 0 < k) (ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}))
    {z : Z} (hz : z ∈ U) :
    ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ Nonempty (A.restrict W.ι ≅ modUnit (W : Scheme.{u})) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  exact exists_trivialization_of_modTensor_trivial ⟨ψ⟩ hz

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

/-- **`s^{⊗k}`**, right-nested onto `1 ∈ Γ(𝒪_Z, ⊤)` exactly as `modTensorPow` is
right-nested onto `modUnit`. -/
noncomputable def tensorPowSection {Z : Scheme.{u}} {A : Z.Modules} (s : Γ(A, ⊤)) :
    ∀ k : ℕ, Γ(modTensorPow A k, ⊤)
  | 0 => unitOne Z
  | (k + 1) => tensorSection s (tensorPowSection s k)

/-! ### The CANONICAL trivialization of a tensor product

**NEW BLOCK, 2026-07-29.**  Everything from here to
`exists_trivialization_modTensor` exists to build a trivialization of `L ⊗ M`
over `U` whose effect on `tensorSection` is KNOWN.  The route recorded on that
leaf ("strengthen `nonempty_restrict_modTensor` to a named comparison
`(L ⊗ M)|_U ≅ L|_U ⊗ M|_U`, which wants a canonical
`nonempty_modPullback_modTensor`") is NOT the route taken, and does not have to
be: a canonical comparison is more than the leaf needs.

What the leaf needs is a canonical MORPHISM `(L ⊗ M)|_U ⟶ 𝒪_U` with the right
effect on sections, plus the knowledge — from any `Nonempty` comparison — that
`(L ⊗ M)|_U` is abstractly trivial.  The morphism direction is free from the
universal property of sheafification, because it maps OUT of `modTensor`:

* `pushUnitMul` — `(f_*𝒪_X) ⊗ (f_*𝒪_X) ⟶ f_*𝒪_X`, multiplication.  This is the
  only genuinely new construction, and it is elementary: restriction along
  `Opens.map f.base` is a ring map, so multiplication is `Γ(Y,V)`-balanced.
* `pushUnitOfTrivialization` — `φ : L|_U ≅ 𝒪_U` read as `L ⟶ (U.ι)_*𝒪_U`, by
  the unit of `restrictAdjunction`.
* `tensorPairing` — `L.val ⊗ M.val ⟶ ((U.ι)_*𝒪_U).val`, `x ⊗ y ↦ φ(x)·χ(y)`,
  at PRESHEAF level, where the tensor product is objectwise.
* `tensorPairingSheaf` / `trivializationMulHom` — its transposes across the
  sheafification adjunction and `restrictAdjunction`.  Both counits COMPUTE
  (`restrictAdjunction_counit_app_app` is `rfl`; the sheafification counit is
  `modSheafifyValIso`), which is why the section identity is provable.

That `trivializationMulHom` is an ISO is then a one-line unit argument, and this
is the step that consumes the anonymous comparison: writing `ν` for any
isomorphism `(L ⊗ M)|_U ≅ 𝒪_U` (from `nonempty_restrict_modTensor`, `φ`, `χ`),
`ν⁻¹ ≫ trivializationMulHom φ χ` is an ENDOMORPHISM of `𝒪_U`, hence
multiplication by its value `c` at `1` (`unitHomApply_eq`).  Evaluating at the
distinguished section `tensorUnitSection = φ⁻¹(1) ⊗ χ⁻¹(1)`, whose image under
`trivializationMulHom` is `1` by construction, gives `d · c = 1`.  So `c` is a
unit, `isIso_of_isUnit_unitHom` applies, and no property of `ν` beyond its
existence is ever used — which is exactly the right shape, since `ν` is
anonymous.

So this block waits on `nonempty_modPullback_modTensor` (through
`nonempty_restrict_modTensor`) for EXISTENCE only, and on nothing else. -/

section PushforwardUnit
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f_*𝒪_X`, as an `𝒪_Y`-module. -/
noncomputable abbrev pushUnit : Y.Modules := (Scheme.Modules.pushforward f).obj (modUnit X)

/-- `(f_*𝒪_X).val`, retyped over `Y.presheaf ⋙ forget₂ _ _` so that the monoidal
structure on `ModuleCat` at each open is found by instance search. -/
noncomputable abbrev pushUnitVal :
    PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := (pushUnit f).val

/-- `Γ(f_*𝒪_X, V) = Γ(X, f⁻¹V)` is definitional; this names the direction into
the module, so that `*` and `+` can be written on the other side. -/
noncomputable def pushUnitEq {V : Y.Opensᵒᵖ} (x : Γ(X, f ⁻¹ᵁ V.unop)) :
    ((pushUnitVal f).obj V) := x

/-- The inverse retyping of `pushUnitEq`. -/
noncomputable def pushUnitEq' {V : Y.Opensᵒᵖ} (x : ((pushUnitVal f).obj V)) :
    Γ(X, f ⁻¹ᵁ V.unop) := x

/-- Multiplication on `f_*𝒪_X` over one open.  Balanced over `Γ(Y, V)` because
the `Γ(Y,V)`-action is through the ring map `f.app V`. -/
noncomputable def pushUnitMulApp (V : Y.Opensᵒᵖ) :
    (pushUnitVal f).obj V ⊗ (pushUnitVal f).obj V ⟶ (pushUnitVal f).obj V :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun x y => pushUnitEq f (pushUnitEq' f x * pushUnitEq' f y))
    (by intro x₁ x₂ y
        show pushUnitEq f ((pushUnitEq' f x₁ + pushUnitEq' f x₂) * pushUnitEq' f y)
          = pushUnitEq f (pushUnitEq' f x₁ * pushUnitEq' f y
              + pushUnitEq' f x₂ * pushUnitEq' f y)
        rw [add_mul])
    (by intro a x y
        show pushUnitEq f ((f.app V.unop a * pushUnitEq' f x) * _) = _
        show _ = pushUnitEq f (f.app V.unop a * (pushUnitEq' f x * pushUnitEq' f y))
        rw [mul_assoc])
    (by intro x y₁ y₂
        show pushUnitEq f (pushUnitEq' f x * (pushUnitEq' f y₁ + pushUnitEq' f y₂))
          = pushUnitEq f (pushUnitEq' f x * pushUnitEq' f y₁
              + pushUnitEq' f x * pushUnitEq' f y₂)
        rw [mul_add])
    (by intro a x y
        show pushUnitEq f (pushUnitEq' f x * (f.app V.unop a * pushUnitEq' f y)) = _
        show _ = pushUnitEq f (f.app V.unop a * (pushUnitEq' f x * pushUnitEq' f y))
        rw [mul_left_comm])

/-- **Multiplication `(f_*𝒪_X) ⊗ (f_*𝒪_X) ⟶ f_*𝒪_X`** (PROVEN 2026-07-29).
Naturality is `map_mul` for the restriction ring map. -/
noncomputable def pushUnitMul :
    PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf) (pushUnitVal f) (pushUnitVal f) ⟶
      pushUnitVal f where
  app V := pushUnitMulApp f V
  naturality := by
    intro V W i
    refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
    show pushUnitEq f (X.presheaf.map ((Opens.map f.base).map i.unop).op (pushUnitEq' f x)
          * X.presheaf.map ((Opens.map f.base).map i.unop).op (pushUnitEq' f y))
      = pushUnitEq f (X.presheaf.map ((Opens.map f.base).map i.unop).op
          (pushUnitEq' f x * pushUnitEq' f y))
    rw [map_mul]

end PushforwardUnit

section TensorTrivialization
variable {Z : Scheme.{u}} {L M : Z.Modules} {U : Z.Opens}

/-- `φ : L|_U ≅ 𝒪_U`, read as a morphism `L ⟶ (U.ι)_* 𝒪_U` on `Z`. -/
noncomputable def pushUnitOfTrivialization
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u})) : L ⟶ pushUnit U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).unit.app L ≫
    (Scheme.Modules.pushforward U.ι).map φ.hom

lemma pushUnitOfTrivialization_app (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (V : Z.Opens) (x : Γ(L, V)) :
    pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app (op V) x)
      = φ.hom.val.app (op (U.ι ⁻¹ᵁ V))
          (L.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op x) := rfl

/-- The presheaf-level pairing `L ⊗ M ⟶ (U.ι)_* 𝒪_U`, `x ⊗ y ↦ φ(x)·χ(y)`. -/
noncomputable def tensorPairing (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val ⟶ pushUnitVal U.ι :=
  PresheafOfModules.Monoidal.tensorHom (pushUnitOfTrivialization φ).val
      (pushUnitOfTrivialization χ).val ≫ pushUnitMul U.ι

/-- Its transpose across the sheafification adjunction, written with the counit
(`modSheafifyValIso`) rather than `homEquiv`, so that it computes.  Going through
`Adjunction.homEquiv` instead makes the evaluation lemma below time out, because
the `restrictScalars (𝟙 _)` in the right adjoint has to be defeq-unfolded. -/
noncomputable def tensorPairingSheaf (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    modTensor L M ⟶ pushUnit U.ι :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (tensorPairing φ χ) ≫
    (modSheafifyValIso (pushUnit U.ι)).hom

/-- **The canonical trivialization morphism `(L ⊗ M)|_U ⟶ 𝒪_U`.** -/
noncomputable def trivializationMulHom (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (modTensor L M).restrict U.ι ⟶ modUnit (U : Scheme.{u}) :=
  (Scheme.Modules.restrictFunctor U.ι).map (tensorPairingSheaf φ χ) ≫
    (Scheme.Modules.restrictAdjunction U.ι).counit.app (modUnit (U : Scheme.{u}))

/-- Applying a presheaf-of-modules morphism equation at one open and one section. -/
lemma presheafHom_congr_apply {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {A B : PresheafOfModules.{u} R} {m₁ m₂ : A ⟶ B} (h : m₁ = m₂) (V : Cᵒᵖ) (z : A.obj V) :
    m₁.app V z = m₂.app V z := by rw [h]

/-- The transpose undoes the sheafification unit: naturality of the unit plus the
right triangle identity. -/
lemma tensorPairingSheaf_modTensorMk (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (V : Z.Opensᵒᵖ)
    (z : (PresheafOfModules.Monoidal.tensorObj (R := Z.presheaf) L.val M.val).obj V) :
    (tensorPairingSheaf φ χ).val.app V ((modTensorMk L M).app V z)
      = (tensorPairing φ χ).app V z := by
  have hnat := presheafHom_congr_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.naturality
      (tensorPairing φ χ)) V z
  have htri := presheafHom_congr_apply
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 Z.ringCatSheaf.obj)).right_triangle_components (pushUnit U.ι)) V
      ((tensorPairing φ χ).app V z)
  have hnat' : ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
        (tensorPairing φ χ)).val.app V ((modTensorMk L M).app V z)
      = ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
          (pushUnitVal U.ι)).app V ((tensorPairing φ χ).app V z) := hnat.symm
  have htri' : ((modSheafifyValIso (pushUnit U.ι)).hom).val.app V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).unit.app
          (pushUnitVal U.ι)).app V ((tensorPairing φ χ).app V z))
      = (tensorPairing φ χ).app V z := htri
  show ((modSheafifyValIso (pushUnit U.ι)).hom).val.app V
      (((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map (tensorPairing φ χ)).val.app V
        ((modTensorMk L M).app V z)) = _
  rw [hnat']
  exact htri'

/-- `trivializedSection` for a bare morphism rather than an isomorphism. -/
noncomputable def trivializedSectionHom {A : Z.Modules}
    (θ : A.restrict U.ι ⟶ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) : Γ((U : Scheme.{u}), ⊤) :=
  θ.val.app (op ⊤)
    ((Scheme.Modules.restrictAppIso (f := U.ι) A ⊤).inv
      (A.presheaf.map (homOfLE le_top).op s))

lemma restrictAppIso_inv_apply {A : Z.Modules} (W : (U : Scheme.{u}).Opens)
    (x : Γ(A, U.ι ''ᵁ W)) :
    (Scheme.Modules.restrictAppIso (f := U.ι) A W).inv x = x := rfl

/-- `Z.Opens` is a thin category, so any endomorphism of an open acts trivially. -/
lemma presheafMap_self_apply {A : Z.Modules} {V : Z.Opens}
    (g : op V ⟶ op V) (y : Γ(A, V)) : A.presheaf.map g y = y := by
  rw [Subsingleton.elim g (𝟙 _), CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

lemma pushUnitOfTrivialization_top (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (x : Γ(L, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) :
    (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
      (pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app
        (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) x))
      = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens)) x := by
  rw [pushUnitOfTrivialization_app]
  calc (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
        (φ.hom.val.app (op (U.ι ⁻¹ᵁ (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))))
          (L.presheaf.map (homOfLE (U.ι.image_preimage_le _)).op x))
      = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
          (L.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map
              (eqToHom (U.ι.preimage_image_eq ⊤).symm)).op
            (L.presheaf.map (homOfLE (U.ι.image_preimage_le _)).op x)) :=
        (PresheafOfModules.naturality_apply φ.hom.val
          (X := op (U.ι ⁻¹ᵁ (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))))
          (Y := op (⊤ : (U : Scheme.{u}).Opens))
          (eqToHom (U.ι.preimage_image_eq ⊤).symm).op _).symm
    _ = φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens)) x := by
        refine congrArg _ ?_
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, presheafMap_self_apply]

lemma pushUnitOfTrivialization_top_global (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (a : Γ(L, ⊤)) :
    (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
      (pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app
        (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) (L.presheaf.map (homOfLE le_top).op a)))
      = trivializedSection φ a := by
  rw [pushUnitOfTrivialization_top]
  unfold trivializedSection
  rw [restrictAppIso_inv_apply]

lemma trivializationMulHom_app_top (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (w : Γ(modTensor L M, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) :
    (trivializationMulHom φ χ).val.app (op ⊤) w
      = (U : Scheme.{u}).presheaf.map (eqToHom (U.ι.preimage_image_eq ⊤).symm).op
          (pushUnitEq' U.ι ((tensorPairingSheaf φ χ).val.app
            (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) w)) := rfl

lemma tensorSection_restrict (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    (modTensor L M).presheaf.map
        (homOfLE (le_top : U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens) ≤ ⊤)).op (tensorSection a b)
      = (modTensorMk L M).app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
          (L.presheaf.map (homOfLE le_top).op a ⊗ₜ M.presheaf.map (homOfLE le_top).op b) :=
  (PresheafOfModules.naturality_apply (modTensorMk L M)
    (X := op (⊤ : Z.Opens)) (Y := op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (homOfLE le_top).op (a ⊗ₜ b)).symm

lemma tensorPairing_tmul (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (V : Z.Opens)
    (x : Γ(L, V)) (y : Γ(M, V)) :
    pushUnitEq' U.ι ((tensorPairing φ χ).app (op V) (x ⊗ₜ y))
      = pushUnitEq' U.ι ((pushUnitOfTrivialization φ).val.app (op V) x)
        * pushUnitEq' U.ι ((pushUnitOfTrivialization χ).val.app (op V) y) := rfl

/-- **The canonical trivialization morphism multiplies sections** (PROVEN
2026-07-29).  This is the identity the leaf below asks for; what is left there is
only that the morphism is invertible. -/
theorem trivializedSectionHom_trivializationMulHom
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) (a : Γ(L, ⊤)) (b : Γ(M, ⊤)) :
    trivializedSectionHom (trivializationMulHom φ χ) (tensorSection a b)
      = trivializedSection φ a * trivializedSection χ b := by
  unfold trivializedSectionHom
  rw [restrictAppIso_inv_apply, trivializationMulHom_app_top, tensorSection_restrict,
    tensorPairingSheaf_modTensorMk, tensorPairing_tmul, map_mul,
    pushUnitOfTrivialization_top_global, pushUnitOfTrivialization_top_global]

/-! #### Endomorphisms of `𝒪_W`

The general form of the transition-function computation already done at `⊤` in
`nonvanishingLocus_modUnit`: an endomorphism of `𝒪_W` is multiplication by its
value at `1`, and it is an isomorphism as soon as that value is a unit. -/

/-- `1 : Γ(W, V)`, read as a section of the unit module over `V`. -/
def unitOneAt (W : Scheme.{u}) (V : W.Opens) : Γ(modUnit W, V) := (1 : Γ(W, V))

/-- An endomorphism of `𝒪_W` applied to a section over `V`, both sides typed in
`Γ(W, V)`.  Same role as `unitEndoApply` above, for a bare morphism and over an
arbitrary open. -/
noncomputable def unitHomApply {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) {V : W.Opens}
    (a : Γ(W, V)) : Γ(W, V) := α.val.app (op V) a

lemma unitHomApply_eq {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) {V : W.Opens}
    (a : Γ(W, V)) :
    unitHomApply α a = a * unitHomApply α (1 : Γ(W, V)) := by
  have h2 : unitHomApply α (a * 1) = a * unitHomApply α (1 : Γ(W, V)) :=
    (α.val.app (op V)).hom.map_smul a (unitOneAt W V)
  simpa using h2

lemma unitHom_app_one {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W) (V : W.Opens) :
    unitHomApply α (1 : Γ(W, V))
      = W.presheaf.map (homOfLE le_top).op (unitHomApply α (1 : Γ(W, ⊤))) := by
  have h1 : ((modUnit W).val.map (homOfLE (le_top : V ≤ ⊤)).op) (unitOneAt W ⊤)
      = unitOneAt W V :=
    PresheafOfModules.unit_map_one W.ringCatSheaf.obj (homOfLE le_top).op
  have hnat := PresheafOfModules.naturality_apply α.val
    (X := op (⊤ : W.Opens)) (Y := op V) (homOfLE le_top).op (unitOneAt W ⊤)
  rw [h1] at hnat
  exact hnat

/-- The compatible family of restrictions of a global section of `𝒪_W`. -/
noncomputable def unitSectionOf {W : Scheme.{u}} (c : Γ(W, ⊤)) : (modUnit W).sections :=
  PresheafOfModules.sectionsMk (fun V => W.presheaf.map (homOfLE le_top).op c)
    (fun V V' g => by
      show W.presheaf.map g (W.presheaf.map (homOfLE le_top).op c) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      congr 1)

/-- Multiplication by a global section of `𝒪_W`, as an endomorphism of `𝒪_W`.
Built through `SheafOfModules.unitHomEquiv`, so no naturality proof is needed. -/
noncomputable def unitMulHom {W : Scheme.{u}} (c : Γ(W, ⊤)) : modUnit W ⟶ modUnit W :=
  (SheafOfModules.unitHomEquiv (modUnit W)).symm (unitSectionOf c)

lemma unitMulHom_app_one {W : Scheme.{u}} (c : Γ(W, ⊤)) (V : W.Opens) :
    unitHomApply (unitMulHom c) (1 : Γ(W, V))
      = W.presheaf.map (homOfLE le_top).op c :=
  congrArg (fun s : (modUnit W).sections => s.val (op V))
    ((SheafOfModules.unitHomEquiv (modUnit W)).apply_symm_apply (unitSectionOf c))

/-- **An endomorphism of `𝒪_W` whose value at `1` is a unit is an isomorphism**
(PROVEN 2026-07-29). -/
theorem isIso_of_isUnit_unitHom {W : Scheme.{u}} (α : modUnit W ⟶ modUnit W)
    (h : IsUnit (unitHomApply α (1 : Γ(W, ⊤)))) : IsIso α := by
  obtain ⟨v, hv⟩ := h
  refine ⟨unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)), ?_, ?_⟩
  · refine (SheafOfModules.unitHomEquiv (modUnit W)).injective
      (PresheafOfModules.sections_ext _ _ (fun V => ?_))
    show unitHomApply (unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)))
        (unitHomApply α (1 : Γ(W, V.unop))) = (1 : Γ(W, V.unop))
    rw [unitHom_app_one, unitHomApply_eq, unitMulHom_app_one, ← map_mul, ← hv,
      v.mul_inv, map_one]
  · refine (SheafOfModules.unitHomEquiv (modUnit W)).injective
      (PresheafOfModules.sections_ext _ _ (fun V => ?_))
    show unitHomApply α (unitHomApply (unitMulHom ((v⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)))
        (1 : Γ(W, V.unop))) = (1 : Γ(W, V.unop))
    rw [unitMulHom_app_one, unitHomApply_eq, unitHom_app_one, ← map_mul, ← hv,
      v.inv_mul, map_one]

/-- `φ⁻¹(1) ⊗ χ⁻¹(1)`, a section of `L ⊗ M` over `U`.  This is the witness that
makes `trivializationMulHom` surjective on `𝒪_U`, and it is where `φ` and `χ`
being ISOMORPHISMS (rather than mere maps) is used. -/
noncomputable def tensorUnitSection (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    Γ(modTensor L M, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) :=
  (modTensorMk L M).app (op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))
    (φ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u})) ⊗ₜ
      χ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u})))

lemma trivializationMulHom_tensorUnitSection
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    (trivializationMulHom φ χ).val.app (op ⊤) (tensorUnitSection φ χ)
      = (1 : Γ((U : Scheme.{u}), ⊤)) := by
  have hφ : φ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
      (φ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u}))) = (1 : Γ((U : Scheme.{u}), ⊤)) :=
    presheafHom_congr_apply (congrArg SheafOfModules.Hom.val φ.inv_hom_id) (op ⊤) _
  have hχ : χ.hom.val.app (op (⊤ : (U : Scheme.{u}).Opens))
      (χ.inv.val.app (op ⊤) (unitOne (U : Scheme.{u}))) = (1 : Γ((U : Scheme.{u}), ⊤)) :=
    presheafHom_congr_apply (congrArg SheafOfModules.Hom.val χ.inv_hom_id) (op ⊤) _
  rw [tensorUnitSection, trivializationMulHom_app_top, tensorPairingSheaf_modTensorMk,
    tensorPairing_tmul, map_mul, pushUnitOfTrivialization_top, pushUnitOfTrivialization_top,
    hφ, hχ, mul_one]

end TensorTrivialization

/-- **A TRIVIALIZATION OF A TENSOR PRODUCT MULTIPLIES SECTIONS** (PROVEN
2026-07-29; cut 2026-07-28 out of `exists_trivialization_tensorPow`).

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

**THE RECORDED ROUTE WAS NOT NEEDED — corrected 2026-07-29.**  It read:

> the honest form is to strengthen `nonempty_restrict_modTensor` from `Nonempty`
> to a NAMED comparison isomorphism `(L ⊗ M)|_f ≅ L|_f ⊗ M|_f` carrying
> `(a ⊗ b)|_f` to `a|_f ⊗ b|_f`, which in turn wants a canonical
> `nonempty_modPullback_modTensor` rather than an anonymous one … the whole
> content is that sheafification commutes with restriction to an open subsite.

Every clause of that is TRUE and none of it is required, because a canonical
comparison ISOMORPHISM is strictly more than this leaf asks for.  The leaf asks
for a map `(L ⊗ M)|_U ⟶ 𝒪_U` with a known effect on sections, and maps OUT of
`modTensor` are free: `modTensor` is a sheafification, so its universal property
supplies them from presheaf-level data, where `⊗` is objectwise.  Nothing has to
commute with anything.  See the section heading above for the construction; the
one new ingredient is `pushUnitMul`, multiplication on `(U.ι)_*𝒪_U`.

The `Nonempty` comparison is still used — but only for EXISTENCE of some
trivialization, never for its value, which is exactly the strength it has.  So
this leaf did not, after all, need "strictly more than
`nonempty_modPullback_modTensor` gives"; it needed the same thing used
differently. -/
theorem exists_trivialization_modTensor {Z : Scheme.{u}} {L M : Z.Modules} {U : Z.Opens}
    (φ : L.restrict U.ι ≅ modUnit (U : Scheme.{u}))
    (χ : M.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    ∃ θ : (modTensor L M).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      ∀ (a : Γ(L, ⊤)) (b : Γ(M, ⊤)),
        trivializedSection θ (tensorSection a b)
          = trivializedSection φ a * trivializedSection χ b := by
  obtain ⟨e⟩ := nonempty_restrict_modTensor U.ι L M
  obtain ⟨ν⟩ : Nonempty ((modTensor L M).restrict U.ι ≅ modUnit (U : Scheme.{u})) :=
    ⟨e ≪≫ modTensorMapIso φ χ ≪≫ modTensorUnitLeftIso _⟩
  have hfac : trivializationMulHom φ χ = ν.hom ≫ (ν.inv ≫ trivializationMulHom φ χ) := by
    rw [← Category.assoc, ν.hom_inv_id, Category.id_comp]
  have hu : IsUnit (unitHomApply (ν.inv ≫ trivializationMulHom φ χ)
      (1 : Γ((U : Scheme.{u}), ⊤))) := by
    have h1 : (trivializationMulHom φ χ).val.app (op ⊤) (tensorUnitSection φ χ)
        = unitHomApply (ν.inv ≫ trivializationMulHom φ χ)
            (ν.hom.val.app (op ⊤) (tensorUnitSection φ χ)) :=
      presheafHom_congr_apply (congrArg SheafOfModules.Hom.val hfac) (op ⊤) _
    rw [trivializationMulHom_tensorUnitSection, unitHomApply_eq, mul_comm] at h1
    exact IsUnit.of_mul_eq_one _ h1.symm
  haveI hiso : IsIso (ν.inv ≫ trivializationMulHom φ χ) := isIso_of_isUnit_unitHom _ hu
  haveI hiso2 : IsIso (trivializationMulHom φ χ) := by rw [hfac]; infer_instance
  exact ⟨asIso (trivializationMulHom φ χ), fun a b =>
    trivializedSectionHom_trivializationMulHom φ χ a b⟩

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

/-! ### The geometric step of EGA II 5.1.12 -/

/-- **The pullback of a trivialization trivializes the pullback, and the
pulled-back section has the preimage basic open** (sorry leaf).

Bookkeeping, in the membership form its one consumer uses.  ROUTE: the
trivialization is `f^*` applied to `φ` — `modPullbackMapIso`, composed with base
change of restriction (`(f^*A)|_{f⁻¹U} ≅ (f∣_U)^*(A|_U)`, which is
`modPullbackCompIso` twice over `morphismRestrict_ι`) and `modPullbackUnitIso`,
all of which are PROVEN above.  The section identity is
`trivializedSection ψ (f^*s) = (f ∣_ U).appTop (trivializedSection φ s)` — the
compatibility of `modPullbackSection` with the adjunction unit — and the
membership statement then follows from `Scheme.preimage_basicOpen_top (f ∣_ U)`
together with `morphismRestrict_base_coe`.

Note the statement is for an ARBITRARY morphism `f`.  That is not an oversight:
basic opens pull back along any morphism of schemes, so the closed-immersion
hypothesis of the consumer plays no role here. -/
theorem exists_trivialization_modPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Y.Modules}
    {U : Y.Opens} (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    ∃ ψ : (modPullback f A).restrict (f ⁻¹ᵁ U).ι ≅ modUnit ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}),
      ∀ (x : X) (hx : x ∈ f ⁻¹ᵁ U),
        ((⟨x, hx⟩ : ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})) ∈
            ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u}).basicOpen
              (trivializedSection ψ (modPullbackSection f A s))) ↔
          ((⟨f.base x, hx⟩ : (U : Scheme.{u})) ∈
            (U : Scheme.{u}).basicOpen (trivializedSection φ s)) := sorry

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

end Fermat
