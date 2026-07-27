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
leaves are now PROVEN**, on top of five smaller named ones.  The route that
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
* both UNITORS are free — `a(𝟙 ⊗ M) ≅ a(M) ≅ M` — `modTensorUnitLeftIso`,
  `modTensorUnitRightIso`;
* the ASSOCIATOR is *not*, and is the only one of the three that is a real
  theorem.  It is now the single named leaf `nonempty_modTensor_assoc`.

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
`modTensorUnitLeftIso`, `modTensorUnitRightIso`, `modTensorPowMapIso`,
`modTensorPowUnitIso`, `modPullbackUnitIso`, `trivializedSection_of_iso`,
`nonvanishingAt_of_iso`, `nonvanishingLocus_of_iso`, and — derived from the
five leaves below — all six original statements
(`isAmpleSheaf_of_iso`, `isAmpleSheaf_modTensorPow`, `isAmpleSheaf_modPullback`,
`isQuasiAffine_of_isAmpleSheaf_modUnit`, `nonempty_modPullback_modTensorPow`,
`nonempty_modPullback_modUnit`).

OPEN — five leaves, each strictly smaller than what it replaced:

* `nonempty_modTensor_assoc` — SHEAFIFICATION IS MONOIDAL, in the one instance
  needed.  The deepest of the five; everything about tensor *powers*
  (`nonempty_modTensorPow_add`, `nonempty_modTensorPow_mul`) is derived from it
  here, so it is the only associativity obligation left anywhere.
* `nonempty_modPullback_modTensor` — monoidality of `f^*` on objects.  With
  `modPullbackUnitIso` proven, this is all that
  `nonempty_modPullback_modTensorPow` needs.
* `exists_tensorPowSection` — the `k`-th tensor power `s^{⊗k}` of a global
  section, with the same non-vanishing locus.
* `nonvanishingLocus_modUnit` — the transition-function computation:
  `Z_r = Z.basicOpen r` for the structure sheaf.  This is the "well-definedness
  of the non-vanishing locus" obligation named in the original docstring of
  `isQuasiAffine_of_isAmpleSheaf_modUnit`, and it is now that leaf's ONLY
  remaining obligation — the unitor half is discharged.
* `nonvanishingLocus_modPullback_of_isAmpleSheaf` — EGA II 5.1.12's geometric
  step.  **Read its FAITHFULNESS note**: the hypothesis-free version of this
  lemma is FALSE, with an explicit counterexample.

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

/-- **The RIGHT UNITOR**, `M ⊗ 𝒪_Z ≅ M`. -/
noncomputable def modTensorUnitRightIso {Z : Scheme.{u}} (M : Z.Modules) :
    modTensor M (modUnit Z) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
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

/-! ### The five remaining leaves

Each is strictly smaller than one of the six statements it replaced, and each
names in its docstring what it needs.  Between them they are the residue of the
ampleness theory that `Mathlib/AlgebraicGeometry/` does not have
(`grep -rl Ample Mathlib/AlgebraicGeometry/` is EMPTY at this pin — re-run it
before believing this sentence). -/

/-- **THE ASSOCIATOR** (sorry leaf): `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` for
`𝒪_Z`-modules.

This is the one obligation of the original six that survives intact, and it is
exactly the statement that SHEAFIFICATION IS MONOIDAL: unfolded, it asks for
`a(a(L ⊗ M) ⊗ N) ≅ a(L ⊗ a(M ⊗ N))`, which reduces to
`a(a(P) ⊗ Q) ≅ a(P ⊗ Q)`, i.e. that the class of local isomorphisms is stable
under `- ⊗ Q`.

ROUTE: `Mathlib/CategoryTheory/Localization/Monoidal/{Basic,Functor}.lean`
transports a monoidal structure along a localization functor once the inverted
class is compatible with `⊗`; `Mathlib/Algebra/Category/ModuleCat/Sheaf/
Localization.lean` presents `SheafOfModules R` as a localization of
`PresheafOfModules R.val`.  Neither has been tried here — that pairing is the
first thing to check before writing anything by hand.

Everything else about tensor powers in this file (`nonempty_modTensorPow_add`,
`nonempty_modTensorPow_mul`, and hence `isAmpleSheaf_modTensorPow`) is DERIVED
from this leaf, so it is the single associativity obligation of the module. -/
theorem nonempty_modTensor_assoc {Z : Scheme.{u}} (L M N : Z.Modules) :
    Nonempty (modTensor (modTensor L M) N ≅ modTensor L (modTensor M N)) := sorry

/-- **Monoidality of `f^*` on objects** (sorry leaf):
`f^*(L ⊗ M) ≅ f^*L ⊗ f^*M`.

`Scheme.Modules.pullback` is a left adjoint and the presheaf-level tensor is a
colimit-friendly construction, so this is expected to follow from the
presheaf-level statement (base change of modules is monoidal:
`S ⊗_R (M ⊗_R N) ≅ (S ⊗_R M) ⊗_S (S ⊗_R N)`) plus the same
sheafification-is-monoidal input as `nonempty_modTensor_assoc`.

With `modPullbackUnitIso` PROVEN, this is the only obligation of
`nonempty_modPullback_modTensorPow`. -/
theorem nonempty_modPullback_modTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    Nonempty (modPullback f (modTensor L M) ≅
      modTensor (modPullback f L) (modPullback f M)) := sorry

/-- **Tensor powers of a global section** (sorry leaf): `s^{⊗k}`, with the same
non-vanishing locus as `s`.

FAITHFULNESS: the hypothesis `hloc` is carried deliberately and is not
decoration.  The `⊇` half is formal — where `A` is trivialized and `s` is a
unit, `A^{⊗k}` is trivialized and `s^{⊗k}` is a unit.  The `⊆` half is the
substantive one: it must rule out a point at which `A^{⊗k}` happens to be
invertible with `s^{⊗k}` a generator while `A` itself is not invertible.  It is
`hloc` — which says `A` IS trivialized, with `s` a generator, at every point of
`V` and at no other point — that has to supply this.  A version of this leaf
stated without `V` and `hloc` should be treated as unproven-and-suspect, not as
an obvious generalization. -/
theorem exists_tensorPowSection {Z : Scheme.{u}} (A : Z.Modules) (s : Γ(A, ⊤)) {k : ℕ}
    (hk : 0 < k) (V : Z.Opens) (hloc : nonvanishingLocus A s = (V : Set Z)) :
    ∃ t : Γ(modTensorPow A k, ⊤),
      nonvanishingLocus (modTensorPow A k) t = (V : Set Z) := sorry

/-- **The non-vanishing locus of a section of the structure sheaf is its basic
open** (sorry leaf) — the transition-function computation.

This is the "well-definedness of `nonvanishingLocus`" obligation named in the
original docstring of `isQuasiAffine_of_isAmpleSheaf_modUnit`, and it is now
that theorem's ONLY remaining input: the UNITOR half is discharged by
`modTensorPowUnitIso`.

PROOF SKETCH: `⊇` take `U = ⊤` and `φ = Scheme.Modules.restrictUnitIso (⊤ :
Z.Opens).ι`.  `⊆` an arbitrary `φ : (modUnit Z).restrict U.ι ≅ modUnit U` is an
automorphism of the structure sheaf as a module over itself, hence is
multiplication by the unit `u = φ.hom.app ⊤ 1` (from `x = x • 1` and
`PresheafOfModules.unitHomEquiv`); `u` is invertible because `φ.inv` inverts it,
and `basicOpen (u * r) = basicOpen r` for a unit `u`.

Note `Γ(modUnit Z, ⊤)` and `Γ(Z, ⊤)` are DEFEQ at this pin, which is why no
coercion appears in the statement. -/
theorem nonvanishingLocus_modUnit (Z : Scheme.{u}) (r : Γ(Z, ⊤)) :
    nonvanishingLocus (modUnit Z) r = (Z.basicOpen r : Set Z) := sorry

/-- **The geometric step of EGA II 5.1.12** (sorry leaf): for a closed immersion
`f`, the non-vanishing locus of a pulled-back section is the preimage of the
non-vanishing locus.

**FAITHFULNESS — the version of this lemma WITHOUT `hL` is FALSE.**  Take
`Y = Spec k[u]`, `A` the skyscraper `k` at the origin `y₀`, `X = Spec k` and
`f : X ⟶ Y` the closed immersion of `y₀`, and `s = 1 ∈ Γ(A, ⊤) = k`.  Then
`f^*A ≅ 𝒪_X = k` and `f^*s` generates it, so `f^*s` does NOT vanish at the
point of `X`; but `A` admits NO trivialization `A|_U ≅ 𝒪_U` on any neighbourhood
of `y₀` (its sections form a `k`-line while `𝒪(U)` is infinite-dimensional), so
`NonvanishingAt A s y₀` is false and `nonvanishingLocus A s = ∅`.  The
conclusion would read `{pt} = f⁻¹ ∅ = ∅`.

So the `⊆` direction is not formal: it needs `modTensorPow L n` to be locally
trivial near the points of `f.base ⁻¹' Vᶜ` at which the pullback happens to be
trivial, and `hL : IsAmpleSheaf L` is what must supply it.  (`hL` does rule the
counterexample out: `IsAmpleSheaf A` fails for the skyscraper, since `A^{⊗m}` is
never invertible near `y₀`.)  Whether `IsAmpleSheaf L` supplies enough local
triviality *at the particular power `n`* is the open point of this leaf and
deserves an audit before a long proof effort; note `IsAmpleSheaf` only
guarantees, at each `z`, SOME power with a trivializing section, and the set of
such powers is a numerical semigroup, not all of `ℕ`.

The `⊇` direction is formal (pull back a trivialization along `f`), and the
mathlib half of what the consumer needs is present:
`IsAffineOpen.preimage` gives `IsAffineOpen (f ⁻¹ᵁ V)` for an affine morphism. -/
theorem nonvanishingLocus_modPullback_of_isAmpleSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] {L : Y.Modules} (hL : IsAmpleSheaf L) {n : ℕ} (hn : 0 < n)
    (s : Γ(modTensorPow L n, ⊤)) (V : Y.Opens) (hV : IsAffineOpen V)
    (hloc : nonvanishingLocus (modTensorPow L n) s = (V : Set Y)) :
    nonvanishingLocus (modPullback f (modTensorPow L n))
        (modPullbackSection f (modTensorPow L n) s) = f.base ⁻¹' (V : Set Y) := sorry

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
