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
  bookkeeping.
* `trivializedSection_trivializationOfLE` — pure plumbing: restricting a
  trivialization to a smaller open restricts the trivialized section.
* `exists_trivialization_tensorPow` — `s^{⊗k}` read through the `k`-th power of
  a trivialization is the `k`-th power of the trivialized section.
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
  three-line corollary of this one, and a redundant leaf is worse than a hint. -/
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
move.  Note it is stated through `modPullback` rather than directly through
`Scheme.Modules.restrictFunctorComp`: `restrictFunctor` carries an
`[IsOpenImmersion f]` instance argument, so transporting it along
`Scheme.homOfLE_ι` needs a congruence over that instance, whereas
`modPullbackCongrIso` (already proven above, off `Scheme.Modules.pullbackCongr`)
does exactly that job with no instance juggling. -/

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

/-- **`A|_W ≅ (A|_U)|_W` for `W ≤ U`** (PROVEN — pseudo-functoriality of
`modPullback`, plus `Scheme.homOfLE_ι`). -/
noncomputable def modRestrictLEIso {Z : Scheme.{u}} (A : Z.Modules) {W U : Z.Opens} (h : W ≤ U) :
    A.restrict W.ι ≅ (A.restrict U.ι).restrict (Z.homOfLE h) :=
  modRestrictPullbackIso W.ι A ≪≫
    modPullbackCongrIso (Z.homOfLE_ι h).symm A ≪≫
    (modPullbackCompIso (Z.homOfLE h) U.ι A).symm ≪≫
    modPullbackMapIso (Z.homOfLE h) (modRestrictPullbackIso U.ι A).symm ≪≫
    (modRestrictPullbackIso (Z.homOfLE h) (A.restrict U.ι)).symm

/-- **A trivialization over `U` restricts to one over any `W ≤ U`** (PROVEN). -/
noncomputable def trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens} (h : W ≤ U)
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) :
    A.restrict W.ι ≅ modUnit (W : Scheme.{u}) :=
  modRestrictLEIso A h ≪≫ (Scheme.Modules.restrictFunctor (Z.homOfLE h)).mapIso φ ≪≫
    Scheme.Modules.restrictUnitIso (Z.homOfLE h)

/-- **Restricting a trivialization restricts the trivialized section** (sorry
leaf).  Pure plumbing — no mathematics — and the only reason it is not proven
here is that `modRestrictLEIso` is routed through `modPullback`, whose component
isomorphisms come from `Adjunction.leftAdjointUniq` and are therefore not
definitional.

ROUTE, with the parts that were actually tried on 2026-07-28 marked as such.
The honest fix is to redefine `modRestrictLEIso` directly off
`Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι` — restriction is a
`SheafOfModules.pushforward` along `opensFunctor` with `restrictAppIso = Iso.refl`,
so on sections it is literally `Γ(A, W.ι ''ᵁ ⊤) ⟶ Γ(A, U.ι ''ᵁ ⊤)` re-indexed.

* **CHECKED: that definition typechecks**, and the congruence over the
  `[IsOpenImmersion]` instance argument — which is what a bare
  `rw [← Z.homOfLE_ι h]` fails on, with "motive is not type correct" — is
  discharged by `congr 1` ALONE, leaving only the morphism goal:

      eqToIso (show A.restrict W.ι = A.restrict (Z.homOfLE h ≫ U.ι) by
        congr 1; exact (Z.homOfLE_ι h).symm) ≪≫
      (Scheme.Modules.restrictFunctorComp (Z.homOfLE h) U.ι).app A

  No `proof_irrel_heq` is needed; supplying one gives "no goals to be solved".
* **CHECKED: the identity is still NOT `rfl`** with that definition, so the
  remaining work is a genuine computation and not a defeq unfolding.  Do not
  `unfold` and `simp` your way in — doing so on `restrictUnitIso` and
  `restrictFunctorComp` together panicked the elaborator (`PANIC at
  Lean.MetavarContext.getDecl`, an unknown-metavariable crash) rather than
  producing a goal.
* What is left is the naturality of `φ.hom.val` between `op ⊤` and
  `op ((Z.homOfLE h).opensFunctor.obj ⊤)`, together with `Scheme.homOfLE_app`
  (which rewrites `(X.homOfLE e).app W` into an honest `X.presheaf.map`).  That
  is the same shape as `trivializedSection_of_iso` above, which is proven in
  about twenty lines and is the model to copy. -/
theorem trivializedSection_trivializationOfLE {Z : Scheme.{u}} {A : Z.Modules} {W U : Z.Opens}
    (h : W ≤ U) (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) :
    trivializedSection (trivializationOfLE h φ) s
      = (Z.homOfLE h).appTop (trivializedSection φ s) := sorry

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
the faithfulness rule forbids. -/
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

/-- **`s^{⊗k}` read through the `k`-th power of a trivialization is the `k`-th
power of the trivialized section** (sorry leaf).

This is the computational half of `nonvanishingLocus_tensorPowSection`; it is
bookkeeping, not mathematics.  ROUTE: induct on `k`, building `ψ` out of
`nonempty_restrict_modTensor` and `modTensorUnitLeftIso` exactly as
`isInvertibleSheaf_modTensor` does, and check the section identity against
`tensorSection`'s definition — the presheaf tensor is objectwise, so the
identity to verify is that the trivialization of a tensor sends `a ⊗ₜ b` to
`a * b`, which is the definition of the left unitor composed with
`modTensorMapIso`. -/
theorem exists_trivialization_tensorPow {Z : Scheme.{u}} {A : Z.Modules} {U : Z.Opens}
    (φ : A.restrict U.ι ≅ modUnit (U : Scheme.{u})) (s : Γ(A, ⊤)) (k : ℕ) :
    ∃ ψ : (modTensorPow A k).restrict U.ι ≅ modUnit (U : Scheme.{u}),
      trivializedSection ψ (tensorPowSection s k) = trivializedSection φ s ^ k := sorry

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

/-- **THE RIGHT UNITOR**, `M ⊗ 𝒪_Z ≅ M` (PROVEN) — the mirror of
`modTensorUnitLeftIso`, obtained from it through `modTensorComm`. -/
noncomputable def modTensorUnitRightIso {Z : Scheme.{u}} (M : Z.Modules) :
    modTensor M (modUnit Z) ≅ M :=
  modTensorComm M (modUnit Z) ≪≫ modTensorUnitLeftIso M

/-- **AN INVERTIBLE SHEAF HAS A TENSOR INVERSE** (sorry leaf, new 2026-07-28) —
i.e. the invertible sheaves on `Z` form a GROUP under `⊗`, which is the whole
content of "`Pic Z` is a group" and the single missing input of the relative
Picard calculus below.

TRUE and classical (Hartshorne II.6.12, Stacks 01CV): the inverse is the DUAL
`L^∨ = Hom_{𝒪_Z}(L, 𝒪_Z)`, and the evaluation map `L ⊗ L^∨ ⟶ 𝒪_Z` is an
isomorphism because it is one on the trivializing opens supplied by
`IsInvertibleSheaf`, where both sides are `𝒪`.  `L^∨` is invertible for the
same local reason.

**`hL` IS LOAD-BEARING AND THE STATEMENT IS FALSE WITHOUT IT**, with a
counterexample needing no geometry: take `L := 0`, the zero object of the
abelian category `Z.Modules`.  Then `modTensor 0 M` has zero stalks for every
`M`, while `modUnit Z` has stalk `𝒪_{Z,z} ≠ 0` at every `z`, so no `M`
works on any nonempty `Z`.  A skyscraper `k` at a closed point of
`Spec k[u]` is a second, non-degenerate witness: it is finitely generated and
nonzero, and `k ⊗ M` is again supported at that point, never all of `𝒪`.
So this is not a formal fact about a monoidal category — it is exactly the
statement that local triviality globalises to an inverse.

**WHAT IT NEEDS, surveyed 2026-07-28.**  The pin has no internal `Hom` on
`SheafOfModules` — `grep -rn 'internalHom\|ihom' Mathlib/Algebra/Category/
ModuleCat/Sheaf/` returns nothing — so `L^∨` has to be built, either as the
sheafification of `U ↦ Hom_{𝒪(U)}(L(U), 𝒪(U))` or, avoiding internal Hom
entirely, by GLUING: `IsInvertibleSheaf L` hands out a cover by opens with
`L|_U ≅ 𝒪_U`, the transition data is a Čech `1`-cocycle valued in `𝒪^×`, and
the inverse is the sheaf glued from the inverse cocycle.  The second route
needs only the descent already available through
`nonempty_restrict_modTensor` and `trivializationOfLE` in this module, and is
the recommended one.

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
    (_hL : IsInvertibleSheaf L) :
    ∃ M : Z.Modules, IsInvertibleSheaf M ∧ Nonempty (modTensor L M ≅ modUnit Z) :=
  sorry

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
